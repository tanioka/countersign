#!/usr/bin/env python3
"""sign_par.py — 純粋な関数の並列実行: スケジューラとディスパッチ(仕様に無い追加。処理系の外側の最適化で、値は変えない)。

使い方: python3 sign.py prog.sn --par[=N] [--par-stats]      (N = 同時に走らせる数。既定は CPU の数。N が 1 以下なら何もしない)
  環境変数 SIGN_PAR_PROBE_MS=ミリ秒  「重い」と見なす長さ(既定 30)。0 にすると最初の呼び出しからすぐ分割する(試験用)

広げた範囲(第94段): (1) + と * の連なり a + b + c + d は項を平らにして 3 つ以上を同時に。(2) 関数の実引数どうし `f (g x) (h y)`。
  (3) 演算子は + - * / % && || ;; << >> の両辺。(4) 子にもコアを分け与え、子の中でも式を開いて分ける(コアの予算は子ごとに持つ)。
  (5) 待っている間は、待ち行列の仕事を親が奪って計算する。SIGN_PAR_TRACE=1 で子の起動・終了・奪いを時刻つきで stderr へ。
何を並列にするか(sign_plan.py の『兄弟の呼び出し』):
  `fib (n - 1) + fib (n - 2)` のように、演算子 + - * の両辺が「整数だけの純粋な関数の呼び出し」なら、
  左辺を別のプロセスに渡し、右辺を自分で計算する。純粋 = 速い道(run_pure)の計画があり、メモリを読みも書きもしない。
  実引数は整数・定数・名前・括弧・+ - * だけ(副作用が無く、何度評価しても同じ)。これらを満たさない式は今までどおり順番に評価する。
  値は変わらない。変わりうるのは『両辺とも罠・エラーのとき、どちらが先に報告されるか』だけで、それも左辺を先に報告して直列と同じにしてある。

仕組み:
  ディスパッチ  一つの仕事 = (閉包, 整数の実引数)。os.fork() の子が run_pure で計算し、パイプへ 16 進の整数 1 つを書いて終わる。
                fork なので、子は親のその時の状態をそのまま持つ(閉包・計画・環境の写しを送る必要が無い)。
  スケジューラ  同時に走る子は N-1 まで(親が 1 つ計算するので合計 N)。あふれた仕事は待ち行列(先に入れた物から)。
                合流(join)で、まだ始まっていない仕事は親が自分で奪って計算する(待たない)。走っている子は終わるまで select で待ち、
                待つあいだに空いた枠へ待ち行列の仕事を始める。子が失敗・異常終了したら、親が同じ式を直列に評価し直す(落ちない)。
  粒度の見極め  いちばん外の呼び出しは、まず子に全部を計算させて probe_ms だけ待つ(プローブ)。間に合えば軽いので、そのまま答えを使う
                (軽い呼び出しが 3 回続いた本体は以後プローブしない)。間に合わなければ「重い」本体として、一段だけ式を開いて左右に分ける。
                分ける深さは 1 + ceil(log2 N) 段まで(N=4 なら 3 段 = 最大 8 個の仕事)。それより深い所は今までの速い道。
  子の中では並列を使わない(入れ子の fork で枠をあふれさせない)。
限界: Windows など fork が無い環境では使えない(無視して直列)。分けられるのは、式の形が上の条件に合う所だけ。仕事の重さは測るだけで、
  仕事の大きさに合わせた細かい割り振り(盗みあい)はしない。メモリを触る関数・出力する関数は並列にならない。
"""
import atexit, collections, math, os, select, signal, sys, time, warnings

FAIL = object()
INLINE = object()


class Task:
    __slots__ = ("g", "state", "pid", "fd", "buf", "value", "secs", "t0", "give")
    def __init__(self, g):
        self.g = g; self.state = "pending"; self.pid = 0; self.fd = -1; self.buf = b""; self.value = FAIL; self.secs = 0.0; self.t0 = 0.0; self.give = 1


class Par:
    def __init__(self, S, n, probe_ms=30.0, stats=False):
        self.S = S; self.n = max(1, n); self.probe = probe_ms / 1000.0
        self.levels = self._levels(self.n)
        self.level = 0; self.in_child = False
        self.avail = self.n - 1            # 自分のほかに使える余りのコア数。子を出すたび分け与え、子が終われば戻る
        self.force = False                 # 子の最初の呼び出しは、プローブせずにすぐ式を開く
        self.running = {}                  # fd → Task
        self.queue = collections.deque()
        self.body_stat = {}                # id(本体) → [軽い回数, 重いか]
        self.verdict = {}                  # (id(本体), id(環境), 型) → (計画, 並列にできるか)
        self.exp_cache = {}                # id(本体) → (本体, 式を開けるか)
        self.trace = os.environ.get("SIGN_PAR_TRACE") == "1"          # 1 なら 子の起動・終了・奪い・合流を時刻つきで stderr へ
        self.st = collections.Counter(); self.child_secs = 0.0; self.t_start = time.time()
        warnings.filterwarnings("ignore", message=".*fork.*", category=DeprecationWarning)
        atexit.register(self.shutdown)
        if stats: atexit.register(self.report)

    def _tr(self, msg):
        if self.trace: print("[par %.3f pid %d] %s" % (time.time() - self.t_start, os.getpid(), msg), file=sys.stderr)

    @staticmethod
    def _levels(n): return 2 + math.ceil(math.log2(n)) if n > 1 else 0

    # ------------------------------------------------------------ 仕事を出せる式か
    def _lookup(self, env, name):                    # Env.get と違い、副作用(遅延の定義の強制)を起こさない
        e = env
        while e:
            v = e.vars.get(name, None)
            if v is not None or name in e.vars: return v
            e = e.parent
        return None

    def _simple(self, m):                            # 副作用が無く、何度評価しても同じ引数の式
        k = m[0]
        if k == "lit": return len(m) == 2 and type(m[1]) is int
        if k == "id": return True
        if k == "block": return not isinstance(m[1], list) and self._simple(m[1])
        if k == "bin": return m[1] in ("+", "-", "*", "/", "%") and self._simple(m[2]) and self._simple(m[3])
        return False

    def _has_call(self, x):
        """式 x の中に(入れ子でも)関数の呼び出し(seq)があるか。無ければ並べて出しても重ならない(オーバーヘッドだけ)。"""
        if isinstance(x, (tuple, list)):
            if isinstance(x, tuple) and x and x[0] == "seq": return True
            return any(self._has_call(y) for y in x)
        return False

    def call_of(self, node, env):
        """node が『整数だけの引数で呼ぶ、メモリに触れない純粋な関数』の呼び出しなら、実引数がそろった閉包を返す。違えば None(何も評価していない)。"""
        S = self.S
        while node[0] == "block" and not isinstance(node[1], list): node = node[1]
        if node[0] != "seq": return None
        items = node[1]
        if len(items) < 2 or items[0][0] != "id": return None
        f = self._lookup(env, items[0][1])
        if type(f) is not S.Closure or f.acc is not None or not S._pure_plain(f): return None
        if len(f.params) != len(items) - 1: return None
        args = items[1:]
        for m in args:
            if not self._simple(m): return None
        vals = []
        try:
            for m in args:
                v = S.ev(m, env)
                if type(v) is not int: return None
                vals.append(v)
        except S.SignError: return None
        g = S._cp(f, args=vals)
        if not self._memfree(g, "i" * len(vals)): return None
        return g

    def _memfree(self, g, sig):
        S = self.S
        plan = S.pure_plan(g, sig, False)
        if not plan: return False
        key = (id(g.body), id(g.env), sig)
        ent = self.verdict.get(key)
        if ent is not None and ent[0] is plan: return ent[1]
        ok = not any(m in nd["src"] for nd in plan[0] for m in S._PURE_IMPURE)
        self.verdict[key] = (plan, ok)
        return ok

    def _stat(self, g):                                  # 本体ごとの [軽かった回数, 重いと分かったか, 本体]
        bs = self.body_stat.setdefault(id(g.body), [0, False, g.body])
        if bs[2] is not g.body: bs[:] = [0, False, g.body]
        return bs

    def expandable(self, body):
        """本体のどこかに『両辺が名前で始まる並び』の + - * があるか(= 開けば左右に分けられるかもしれない形)。"""
        ent = self.exp_cache.get(id(body))
        if ent is not None and ent[0] is body: return ent[1]
        def seq_call(n):
            while n[0] == "block" and not isinstance(n[1], list): n = n[1]
            return n[0] == "seq" and len(n[1]) >= 2 and n[1][0][0] == "id"
        def walk(n):
            if isinstance(n, tuple) and n and isinstance(n[0], str):
                if n[0] == "bin" and n[1] in ("+", "-", "*") and seq_call(n[2]) and seq_call(n[3]): return True
                return any(walk(x) for x in n[1:])
            if isinstance(n, (list, tuple)): return any(walk(x) for x in n)
            return False
        r = walk(body)
        self.exp_cache[id(body)] = (body, r)
        return r

    # ------------------------------------------------------------ ディスパッチ(子の起動)
    def _start(self, t):
        give = max(1, (self.avail + 1) // 2)          # 子に渡すコア数(子自身を含む)。残りは自分と、あとから出す仕事に
        try:
            r, w = os.pipe()
            sys.stdout.flush(); sys.stderr.flush()
            pid = os.fork()
        except OSError:
            self.st["fork 失敗"] += 1; return False
        if pid == 0:                                  # ---- 子 ----
            code = 0
            try:
                os.close(r)
                for fd in list(self.running): os.close(fd)
                self.running = {}; self.queue.clear()
                self.n = give; self.avail = give - 1; self.level = 0; self.levels = self._levels(give)
                if give <= 1: self.S.PAR[0] = None; self.in_child = True
                else: self.force = True               # 子もコアを持つ: 自分の中でも式を開いて分ける
                t0 = time.time()
                try:
                    v = self.S.run_fixed(t.g) if give > 1 else self.S.run_pure(t.g)
                    data = (b"V %x %.6f\n" % (v, time.time() - t0)) if type(v) is int else b"F\n"
                except BaseException:
                    data = b"F\n"
                while data:
                    k = os.write(w, data); data = data[k:]
            except BaseException:
                code = 1
            finally:
                os._exit(code)
        os.close(w)
        self._tr("子 %d を起動(コア %d)" % (pid, give))
        t.state = "running"; t.pid = pid; t.fd = r; t.t0 = time.time(); t.give = give; self.avail -= give; self.running[r] = t
        self.st["子を起動"] += 1
        if give > 1: self.st["子にも分けるコアを渡した"] += 1
        if len(self.running) > self.st["同時に走った最大"]: self.st["同時に走った最大"] = len(self.running)
        return True

    def _finish(self, t):
        self._tr("子 %d が終わった" % t.pid)
        self.running.pop(t.fd, None); self.avail += t.give
        try: os.close(t.fd)
        except OSError: pass
        try: os.waitpid(t.pid, 0)
        except OSError: pass
        b = t.buf
        t.value = FAIL
        if b.endswith(b"\n") and b.startswith(b"V "):
            try:
                _, hx, secs = b.split()
                t.value = int(hx, 16); t.secs = float(secs); self.child_secs += t.secs
            except ValueError: pass
        if t.value is FAIL: self.st["子の失敗"] += 1
        t.state = "done"

    def _slots(self): return self.avail

    def _fill(self):                                   # 空いた枠へ、待ち行列の先頭から
        while self.queue and self._slots() > 0:
            t = self.queue.popleft()
            if not self._start(t):
                t.state = "stolen"; self.st["親が奪った(fork 失敗)"] += 1

    def _wait(self, timeout):
        """走っている子の出力を読む。終わった子を片づけ、枠が空けば待ち行列の仕事を始める。timeout 秒まで待つ(None は無期限)。"""
        if not self.running: return
        rl, _, _ = select.select(list(self.running), [], [], timeout)
        for fd in rl:
            t = self.running.get(fd)
            if t is None: continue
            try: chunk = os.read(fd, 4096)
            except OSError: chunk = b""
            if chunk:
                t.buf += chunk
                if t.buf.endswith(b"\n"): self._finish(t)          # 答えは 1 行。改行まで読めたら終わり(EOF を待たない)
            else: self._finish(t)
        self._fill()

    def submit(self, g):
        t = Task(g); self.st["仕事を出した"] += 1
        self._wait(0)
        if self._slots() > 0 and self._start(t): return t
        t.state = "queued"; self.queue.append(t); self.st["待ち行列に入れた"] += 1
        return t

    def join(self, t, node, env):
        """仕事の答え(整数)。奪う・失敗したときは親が直列に評価して返す。"""
        if t.state == "queued":
            try: self.queue.remove(t)
            except ValueError: pass
            t.state = "stolen"; self.st["親が奪った"] += 1
        while t.state == "running":
            self._wait(0)
            if t.state != "running": break
            if self.queue and self.avail <= 0:                 # 待っているだけの間に、待ち行列の仕事を 1 つ奪って自分で計算する(後ろから: 親に近い物を残す)
                self._tr("待つあいだに奪う")
                u = self.queue.pop(); u.state = "stolen"; self.st["待つあいだに奪って計算した"] += 1
                v = self.S.run_pure(u.g); self._tr("奪った仕事が終わった")
                u.value = v if type(v) is int else FAIL; u.state = "done" if u.value is not FAIL else "stolen"
                continue
            self._wait(None)
        if t.state == "done" and t.value is not FAIL: return t.value
        if t.state == "done": self.st["親が直列にやり直した"] += 1
        return self.S.ev(node, env)

    def cancel(self, t):
        if t.state == "queued":
            try: self.queue.remove(t)
            except ValueError: pass
            t.state = "stolen"
        elif t.state == "running":
            try: os.kill(t.pid, signal.SIGKILL)
            except OSError: pass
            self._finish(t)

    # ------------------------------------------------------------ 兄弟の呼び出し(演算子の両辺・連なり・関数の実引数)
    def _ok(self):
        S = self.S
        return not (self.in_child or self.level >= self.levels or S.STRICT_GATES or S.OVERRIDES or S.DECL_USED[0] or S.FUEL[0] is not None or S.INTCHK[0])

    def operands(self, n):
        """n = ("bin", op, 左, 右)。+ と * は結合律が成り立つので、同じ演算子の連なり(a + b + c + d)を平らにした項の並び。ほかは 2 項。"""
        op = n[1]
        if op not in ("+", "*"): return [n[2], n[3]]
        out = []
        def flat(x):
            while x[0] == "block" and not isinstance(x[1], list): x = x[1]
            if x[0] == "bin" and x[1] == op: flat(x[2]); flat(x[3])
            else: out.append(x)
        flat(n)
        return out

    def _group(self, nodes, gs, env):
        """nodes[i] は呼び出し(gs[i] はその実引数のそろった閉包)。最後の 1 つを自分で、ほかを子に出して値の並びを返す。
        いちばん外の重さの分からない本体は、先頭を子に出して probe_ms 待つ(間に合えば軽い: 残りは順に自分で)。子が失敗したら None(呼び側が直列)。"""
        S = self.S; k = len(nodes)
        bs = self._stat(gs[0]); tasks = {}
        if self.level == 0 and not bs[1]:
            if bs[0] >= 3: return None
            self.st["プローブ"] += 1
            t = self.submit(gs[0])
            if t.state == "running":
                t_end = time.time() + self.probe
                while t.state == "running":
                    left = t_end - time.time()
                    if left <= 0: break
                    self._wait(left)
            if t.state == "done" and t.value is not FAIL:
                bs[0] += 1; self.st["軽かった(プローブで済んだ)"] += 1
                return [t.value] + [S.ev(x, env) for x in nodes[1:]]
            if t.state == "done": return None                    # 子が失敗: 直列
            bs[1] = True; self.st["重いと見なして分けた"] += 1
            tasks[0] = t
        self.st["式を分けた"] += 1
        if k > 2: self.st["3 つ以上に分けた"] += 1
        for i in range(k - 1):
            if i not in tasks: tasks[i] = self.submit(gs[i])
        self.level += 1; rerr = None; last = None
        try:
            try: last = S.ev(nodes[-1], env)
            except S.SignError as e: rerr = e
            except BaseException:
                for t in tasks.values(): self.cancel(t)
                raise
        finally: self.level -= 1
        vals = []
        try:
            for i in range(k - 1): vals.append(self.join(tasks[i], nodes[i], env))        # 左の誤りを先に出す(直列と同じ)
        except BaseException:
            for t in tasks.values(): self.cancel(t)
            raise
        if rerr is not None: raise rerr
        return vals + [last]

    def pair(self, n, env):
        """n = ("bin", op, 左, 右)。項が全部並列にできる呼び出しなら (左の値, 右の値)(+ と * の連なりは前の項を畳んだ値と最後の値)。そうでなければ None(何も評価していない)。"""
        if not self._ok(): return None
        nodes = self.operands(n); gs = []
        if len(nodes) == 2:                                  # 片方だけが呼び出しでもよい(もう片方が呼び出しを含む = 重そうな式なら、呼び出しを仕事に出して、その間に自分がもう片方を評価)
            gs = [self.call_of(x, env) for x in nodes]
            if gs[0] is None and gs[1] is None: return None
            if gs[0] is None or gs[1] is None:
                i = 0 if gs[0] is not None else 1
                if not self._has_call(nodes[1 - i]): return None
                vals = self._group([nodes[i], nodes[1 - i]], [gs[i], None], env)
                if vals is None: return None
                self.st["呼び出し + 別の式"] += 1
                return (vals[0], vals[1]) if i == 0 else (vals[1], vals[0])
        else:
            for x in nodes:
                g = self.call_of(x, env)
                if g is None: return None
                gs.append(g)
        vals = self._group(nodes, gs, env)
        if vals is None: return None
        if len(vals) == 2: return vals[0], vals[1]
        acc = vals[0]
        for v in vals[1:-1]: acc = acc + v if n[1] == "+" else acc * v
        return acc, vals[-1]

    def seq_vals(self, items, env):
        """並び `f (g x) (h y) …` の値の並び。頭が名前で、後ろが『副作用の無い実引数』か『並列にできる呼び出し』で、呼び出しが 2 つ以上のとき、呼び出しを同時に評価する。"""
        if len(items) < 3 or items[0][0] != "id" or not self._ok(): return None
        calls = []; kinds = []
        for m in items[1:]:
            g = self.call_of(m, env) if m[0] in ("block", "seq") else None
            if g is not None: calls.append((m, g)); kinds.append(True)
            elif self._simple(m): kinds.append(False)
            else: return None
        if len(calls) < 2: return None
        S = self.S
        res = self._group([c[0] for c in calls], [c[1] for c in calls], env)
        if res is None: return None
        it = iter(res); head = S.ev_head(items[0], env); out = [head]
        for m, isc in zip(items[1:], kinds): out.append(next(it) if isc else S.ev(m, env))
        return out

    # ------------------------------------------------------------ 速い道の入口(プローブと分割の判断)
    def run_pure(self, g):
        S = self.S
        if self.in_child or S.STRICT_GATES or S.OVERRIDES or S.DECL_USED[0] or S.FUEL[0] is not None or S.INTCHK[0]: return S.run_pure(g)
        if not g.args or not all(type(a) is int for a in g.args): return S.run_pure(g)
        if self.level >= self.levels or not self.expandable(g.body) or not self._memfree(g, "i" * len(g.args)): return S.run_pure(g)
        if self.level > 0: return None                                  # 分割の途中: 式を開いて、さらに左右に分ける
        if self.force: self.force = False; return None                  # 子の最初の呼び出し: すぐ開く
        bs = self._stat(g)
        if bs[1]: return None                                           # 重いと分かった本体: 開く
        if bs[0] >= 3: return S.run_pure(g)                             # 軽い呼び出しが続いた本体: プローブしない
        t = Task(g); self.st["プローブ"] += 1
        self._wait(0)
        if not self._start(t): return S.run_pure(g)
        t_end = time.time() + self.probe
        while t.state == "running":
            left = t_end - time.time()
            if left <= 0: break
            self._wait(left)
        if t.state == "done":
            if t.value is not FAIL:
                bs[0] += 1; self.st["軽かった(プローブで済んだ)"] += 1; return t.value
            return S.run_pure(g)
        self.cancel(t); bs[1] = True; self.st["重いと見なして開いた"] += 1
        return None

    # ------------------------------------------------------------ 後始末と報告
    def shutdown(self):
        for t in list(self.running.values()):
            try: os.kill(t.pid, signal.SIGKILL)
            except OSError: pass
            try: os.waitpid(t.pid, 0)
            except OSError: pass
        self.running.clear(); self.queue.clear()

    def report(self):
        wall = time.time() - self.t_start
        print("[par] N=%d 段=%d 経過 %.3f 秒 / 子の計算の合計 %.3f 秒" % (self.n, self.levels, wall, self.child_secs), file=sys.stderr)
        for k, v in sorted(self.st.items()): print("[par]   %s: %d" % (k, v), file=sys.stderr)
