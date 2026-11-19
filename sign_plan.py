#!/usr/bin/env python3
"""sign_plan.py — 並列実行のプラン(計画)だけを出す。実際には並列に走らせない(仕様に無い追加の道具)。

Sign の式は、引数をすべて先に(左から右へ)評価する。引数どうしは互いの値を使わないので、
副作用(メモリの書き込み・読み出し・デバイスの入出力)がぶつからない限り、同時に評価してよい。
このツールは構文木を読んで、次を出す:
  1. 関数の表     副作用の種類(純粋 / 読む / 書く)・自己呼び出し・重さの概算
  2. 並列にできる所  どの式の、どの部分どうしを同時に評価できるか(引数どうし・演算子の両辺・分割統治の再帰)と、見込める速さ
  3. 実行プラン   最上位の式を「波(同時に走らせる組)」の列にした木。波は順番に、波の中は同時
  4. 並列にできない所  なぜ順番を守る必要があるか(同じ番地への書き込み・番地が計算で決まる・デバイスの入出力 など)

使い方:  python3 sign_plan.py prog.sn [--json] [--dot] [--depth N] [--cores N] [--min-work N] [--rec-weight N]
  --json        機械が読める形(別の実行系が使う用)で出す   --dot  Graphviz の DOT で出す
  --depth N     プランで関数の中身を何段まで開くか(既定 3)  --cores N  コア数(速さの見込みの上限。既定 4)
  --min-work N  これより軽い部分は並列の対象にしない(既定 8。構文木の節の数)  --rec-weight N  再帰の呼び出し 1 回の重さの仮定(既定 200)

重さは構文木の節の数の概算(静的)。実際にかかる時間ではない。副作用の判定は安全側: 迷ったら「ぶつかる」とみなして順番を守る。
  番地が定数(名前つき定数・+ - * の計算を含む)で決まるものだけ「別の番地」と言える。計算で決まる番地(*)は、どの番地とも重なりうるとみなす。
  アドレス 0x9000000 以上はデバイス。デバイスの読み書きは、順番に意味があるので書き込みとして扱う。
言語の意味は変えない前提の計画: 引数の評価は元々すべて行われる(どれかが __ でも、他の引数は評価される)ので、同時に評価しても値は同じ。
  変わりうるのは「エラーが複数あるとき、どれが先に報告されるか」だけ。
"""
import json, os, sys

sys.setrecursionlimit(20000)
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
ANY = "*"
DEV0 = 0x9000000


# ------------------------------------------------------------------ 副作用
class Eff:
    __slots__ = ("r", "w")
    def __init__(self, r=(), w=()): self.r, self.w = set(r), set(w)
    def __or__(self, o): return Eff(self.r | o.r, self.w | o.w)
    def key(self): return (frozenset(self.r), frozenset(self.w))
    def pure(self): return not self.r and not self.w
    def kind(self): return "純粋" if self.pure() else ("書く" if self.w else "読む")

def _inter(a, b): return bool(a and b and (ANY in a or ANY in b or a & b))
def conflict(a, b):
    """同時に走らせると結果が変わりうるか。書き込みどうし・書き込みと読み出しがぶつかる。"""
    return _inter(a.w, b.w) or _inter(a.w, b.r) or _inter(a.r, b.w)
def why(a, b):
    """ぶつかる理由(人が読む文)。"""
    for x, y, nm in ((a.w, b.w, "どちらも"), (a.w, b.r, "前が書いて後が読む"), (a.r, b.w, "前が読んで後が書く")):
        if _inter(x, y):
            common = (x & y) - {ANY}
            if common and any(isinstance(l, tuple) for l in common): return f"{nm}同じデバイスを使う(入出力は順番に意味がある)"
            if common and ANY not in x and ANY not in y: return f"{nm}番地 {fmt_locs(common)} を使う"
            return f"{nm}番地が計算で決まる(*)ので、重なるかもしれない"
    return "?"
def loc_of(v):
    return ("dev", v >> 20) if v >= DEV0 else v
def fmt_locs(ls): return ", ".join(("(計算で決まる)" if l == ANY else hex(l) if isinstance(l, int) else f"デバイス{hex(l[1] << 20)}") for l in sorted(ls, key=str))


# ------------------------------------------------------------------ プラン
class Task:
    def __init__(self, kind, label, eff=None):
        self.kind, self.label, self.eff = kind, label, eff or Eff()
        self.waves, self.alts = [], []            # waves: [[Task]](順番の組・中は同時)。alts: 行の候補(どれか 1 つが選ばれる)
        self.work, self.span, self.notes, self.rec = 1, 1, [], set()
    def trivial(self): return self.kind == "leaf"
    def walk(self):
        yield self
        for w in self.waves:
            for t in w: yield from t.walk()
        for t in self.alts: yield from t.walk()


class Planner:
    def __init__(self, nodes, depth=3, rec_w=200, min_work=8, cores=4):
        self.depth, self.rec_w, self.min_work, self.cores = depth, rec_w, min_work, cores
        self.defs, self.consts = {}, {}
        for n in nodes:
            if n[0] == "def":
                if n[2][0] == "lam": self.defs.setdefault(n[1], n[2])
                elif n[2][0] == "lit" and isinstance(n[2][1], int) and not isinstance(n[2][1], bool): self.consts.setdefault(n[1], n[2][1])
        self.main = [n for n in nodes if n[0] not in ("def", "importspread", "opdef", "export")]
        self.summ = {f: Eff() for f in self.defs}
        self.weight_memo, self.calls = {}, {f: set() for f in self.defs}
        self.fixpoint()
        self.recursive = self.find_recursive()
        self.opps, self.blocks = [], []           # 並列にできる所 / できない所

    # --- 定数の畳み込み(番地の計算)
    def const(self, n, params=()):
        k = n[0]
        if k == "lit": return n[1] if isinstance(n[1], int) and not isinstance(n[1], bool) else None
        if k == "id": return None if n[1] in params else self.consts.get(n[1])
        if k == "block": return self.const(n[1], params)
        if k == "bin" and n[1] in ("+", "-", "*"):
            a, b = self.const(n[2], params), self.const(n[3], params)
            if a is None or b is None: return None
            return a + b if n[1] == "+" else a - b if n[1] == "-" else a * b
        return None

    # --- 関数の副作用の不動点(引数は未知として、番地が引数で決まるものは *)
    def params(self, lam):
        out = set()
        for sp in lam[1]:
            out |= {sp[1]} if sp[0] == "name" else set(sp[1]) | ({sp[2]} if sp[2] else set())
        return out

    def eff_of(self, n, params):
        """式 n の副作用(子を含む)。呼ぶ関数は summ の値を使う。"""
        k = n[0]
        if k in ("lit", "hole"): return Eff()
        if k == "id": return Eff()
        if k == "input":
            c = self.const(n[1], params); e = self.eff_of(n[1], params)
            if c is None: return e | Eff(r=[ANY])
            l = loc_of(c); return e | (Eff(w=[l]) if isinstance(l, tuple) else Eff(r=[l]))
        if k == "bin" and n[1] == "#":
            c = self.const(n[2], params); e = self.eff_of(n[2], params) | self.eff_of(n[3], params)
            if c is None: return e | Eff(w=[ANY])
            return e | Eff(w=[loc_of(c)])
        if k == "seq" and n[1] and n[1][0][0] == "id":
            f = n[1][0][1]
            e = Eff()
            for a in n[1][1:]: e = e | self.eff_of(a, params)
            if f in self.defs: self.calls.setdefault(self.cur, set()).add(f) if getattr(self, "cur", None) else None; return e | self.summ[f]
            if f in params: return e | Eff(r=[ANY], w=[ANY])          # 引数として渡された関数を呼ぶ: 何をするか分からない
            return e
        e = Eff()
        for m in children(n): e = e | self.eff_of(m, params)
        return e

    def fixpoint(self):
        changed = True
        while changed:
            changed = False
            for f, lam in self.defs.items():
                self.cur = f
                e = self.eff_of(lam[2], self.params(lam))
                if e.key() != self.summ[f].key(): self.summ[f], changed = e, True
        self.cur = None

    def callees(self, n):
        return {m[1][0][1] for m in nodes_of(n) if m[0] == "seq" and m[1] and m[1][0][0] == "id" and m[1][0][1] in self.defs}

    def find_recursive(self):
        """自分自身に(間接にも)戻ってくる関数。"""
        g = {f: self.callees(lam[2]) for f, lam in self.defs.items()}
        out = set()
        for f in g:
            seen, todo = set(), list(g[f])
            while todo:
                x = todo.pop()
                if x == f: out.add(f); break
                if x in seen: continue
                seen.add(x); todo += g.get(x, ())
        return out

    # --- 重さ(静的)
    def size(self, n): return sum(1 for _ in nodes_of(n))
    def weight(self, f, stack=()):
        if f in stack: return self.rec_w
        if f in self.weight_memo: return self.weight_memo[f]
        lam = self.defs[f]; w = self.size(lam[2])
        for m in nodes_of(lam[2]):
            if m[0] == "seq" and m[1] and m[1][0][0] == "id" and m[1][0][1] in self.defs: w += self.weight(m[1][0][1], stack + (f,))
        if not stack: self.weight_memo[f] = w
        return w

    # --- 組み立て
    def schedule(self, tasks, where):
        """左から右の順を保ちながら、ぶつからない組を同じ波にする。"""
        waves, cur = [], []
        for t in tasks:
            hit = next((u for u in cur if conflict(u.eff, t.eff)), None)
            if hit is not None:
                if not t.trivial() and not hit.trivial(): self.blocks.append((where, hit.label, t.label, why(hit.eff, t.eff)))
                waves.append(cur); cur = []
            cur.append(t)
        if cur: waves.append(cur)
        return waves

    def done(self, t):
        t.work = 1 + sum(sum(x.work for x in w) for w in t.waves) + (max((x.work for x in t.alts), default=0))
        t.span = 1 + sum(max(x.span for x in w) for w in t.waves) + (max((x.span for x in t.alts), default=0))
        for w in t.waves:
            for x in w: t.rec |= x.rec
        for x in t.alts: t.rec |= x.rec
        return t

    def note(self, t, where):
        """波の中に重いものが 2 つ以上あれば、並列にできる所として記録する。"""
        for w in t.waves:
            heavy = [x for x in w if not x.trivial() and x.work >= self.min_work]
            if len(heavy) >= 2:
                tot, sp = sum(x.work for x in heavy), max(x.span for x in heavy)
                kind = "分割統治の再帰" if len({r for x in heavy for r in x.rec} & {where}) and sum(1 for x in heavy if where in x.rec) >= 2 else {"call": "引数どうし", "op": "演算子の両辺", "prod": "並べた要素どうし"}.get(t.kind, t.kind)
                self.opps.append(dict(where=where, kind=kind, at=t.label, tasks=[x.label for x in heavy], work=tot, span=sp, speedup=round(tot / sp, 2), spec=("投機" in " ".join(t.notes))))

    def plan(self, n, params, where, stack, depth):
        k = n[0]
        if k in ("lit", "hole") or (k == "id"):
            return self.done(Task("leaf", fmt(n)))
        if k == "block": return self.plan(n[1], params, where, stack, depth)
        if k == "input":
            t = Task("op", "@ 読む", self.eff_of(n, params)); t.waves = [[self.plan(n[1], params, where, stack, depth)]]; return self.done(t)
        if k == "bin":
            t = Task("op", f"演算 {n[1]}", self.eff_of(n, params))
            kids = [self.plan(n[2], params, where, stack, depth), self.plan(n[3], params, where, stack, depth)]
            if n[1] == "|" and kids[1].eff.w:
                t.notes.append("`|` は右を使わないことがある(短絡の可能性)ので、右が書き込みを含むなら順番を守る")
                t.waves = [[kids[0]], [kids[1]]]
            else:
                if n[1] == "|" and not kids[1].trivial(): t.notes.append("投機: `|` は左が非 __ なら右は不要かもしれない(右が純粋なら、先に走らせても無駄になるだけ)")
                t.waves = self.schedule(kids, where)
            t = self.done(t); self.note(t, where); return t
        if k == "seq" and n[1] and n[1][0][0] == "id" and n[1][0][1] in self.defs:
            f = n[1][0][1]
            t = Task("call", f"呼び出し {f}", self.eff_of(n, params))
            args = [self.plan(a, params, where, stack, depth) for a in n[1][1:]]
            t.waves = self.schedule(args, where)
            if f in stack:
                body = Task("leaf", f"再帰 {f}"); body.work = body.span = self.rec_w; body.rec = {f}; body.eff = self.summ[f]
                t.waves.append([body])
            elif depth > 0:
                lam = self.defs[f]
                body = self.plan(lam[2], self.params(lam), f, stack + (f,), depth - 1); body.label = f"{f} の中身"
                t.waves.append([body])
            else:
                body = Task("leaf", f"{f} の中身(省略)"); body.work = body.span = self.weight(f); body.eff = self.summ[f]
                t.waves.append([body])
            t = self.done(t); self.note(t, where); return t
        if k == "cases":
            t = Task("cases", "条件の行", self.eff_of(n, params))
            for c, e in n[1]:
                if c is not None: t.waves.append([self.plan(c, params, where, stack, depth)])
            alts = []
            for i, (c, e) in enumerate(n[1]):
                a = self.plan(e, params, where, stack, depth); a.label = f"行 {i + 1}: " + a.label; alts.append(a)
            t.alts = alts
            t.notes.append("行は上から順に調べ、最初に非 __ の行の値が選ばれる。条件は順番に評価する(並列にしない)。値は選ばれた 1 行だけ")
            t = self.done(t)
            rows = [e for c, e in n[1]]
            safe = lambda e: not (self.callees(e) & self.recursive)          # 再帰を含む行は先読みしない(止まらなくなるかもしれない)
            heavy = [a for a, e in zip(alts, rows) if a.work >= self.min_work and safe(e)]
            if len(heavy) >= 2 and all(not a.eff.w for a in alts): self.opps.append(dict(where=where, kind="投機(行の値の先読み)", at=t.label, tasks=[a.label for a in heavy], work=sum(a.work for a in heavy), span=max(a.span for a in heavy), speedup=None, spec=True))
            return t
        if k in ("prod",) or (k == "seq" and (not n[1] or n[1][0][0] != "id")):
            t = Task("prod", "並べた要素", self.eff_of(n, params))
            t.waves = self.schedule([self.plan(a, params, where, stack, depth) for a in (n[1] if isinstance(n[1], list) else [])], where)
            t = self.done(t); self.note(t, where); return t
        if k == "seq":                                                    # 知らない関数・引数で渡された関数の呼び出し
            f = n[1][0][1]
            t = Task("call", f"呼び出し {f}(定義が見えない)", self.eff_of(n, params))
            t.waves = [[x] for x in [self.plan(a, params, where, stack, depth) for a in n[1][1:]]]
            if f in params: t.notes.append("引数として渡された関数を呼ぶので、何をするか分からない(副作用ありとして順番を守る)")
            return self.done(t)
        t = Task("op", f"{k}", self.eff_of(n, params))                    # そのほか(順番に子を評価するだけ)
        t.waves = [[self.plan(m, params, where, stack, depth)] for m in children(n)]
        return self.done(t)

    # --- 全体
    def analyse(self):
        self.fn_plans = {}
        for f, lam in self.defs.items():
            self.fn_plans[f] = self.plan(lam[2], self.params(lam), f, (f,), 0)
        self.main_plans = []
        for i, n in enumerate(self.main):
            self.main_plans.append(self.plan(n, set(), f"最上位 {i + 1}", (), self.depth))
        self.dedupe()
        return self

    def dedupe(self):
        seen, out = set(), []
        for o in self.opps:
            key = (o["where"], o["kind"], o["at"], tuple(o["tasks"]))
            if key not in seen: seen.add(key); out.append(o)
        self.opps = out
        seen, out = set(), []
        for b in self.blocks:
            if b not in seen: seen.add(b); out.append(b)
        self.blocks = out


def children(n):
    for x in n[1:]:
        if isinstance(x, tuple) and x and isinstance(x[0], str): yield x
        elif isinstance(x, list):
            for y in x:
                if isinstance(y, tuple) and y and isinstance(y[0], str): yield y
                elif isinstance(y, tuple):
                    for z in y:
                        if isinstance(z, tuple) and z and isinstance(z[0], str): yield z
def nodes_of(x):
    if isinstance(x, tuple):
        if x and isinstance(x[0], str): yield x
        for y in x: yield from nodes_of(y)
    elif isinstance(x, list):
        for y in x: yield from nodes_of(y)
def fmt(n):
    if n[0] == "lit": return repr(n[1]) if not isinstance(n[1], int) else (hex(n[1]) if len(n) > 2 and n[2] == "Address" else str(n[1]))
    if n[0] == "id": return n[1]
    return n[0]


# ------------------------------------------------------------------ 読み込み(取り込みも開く)
def load(path, seen=None):
    import sign_interp as S
    seen = seen or set(); path = os.path.abspath(path)
    if path in seen: return []
    seen.add(path)
    S.IMPORT_STACK.append(path)
    try: nodes = S.parse_source(open(path, encoding="utf-8").read())
    finally: S.IMPORT_STACK.pop()
    out = []
    for n in nodes:
        if n[0] == "importspread" and n[1][0] == "lit" and isinstance(n[1][1], str):
            name = n[1][1]
            cands = [name if os.path.isabs(name) else os.path.join(os.path.dirname(path), name), os.path.abspath(name)]
            f = next((c for c in cands if os.path.exists(c)), None)
            if f: out += [m for m in load(f, seen) if m[0] in ("def", "importspread")]
            continue
        out.append(n)
    return out


# ------------------------------------------------------------------ 出力
def render(t, ind=0, out=None, hide_trivial=True):
    out = out if out is not None else []
    pad = "  " * ind
    eff = "" if t.eff.pure() else f"  [{t.eff.kind()}]"
    out.append(f"{pad}{t.label}   (仕事 {t.work}・最長の道 {t.span}){eff}")
    for nt in t.notes: out.append(f"{pad}  ※ {nt}")
    k = 0
    for w in t.waves:
        shown = [x for x in w if not (hide_trivial and x.trivial())]
        if not shown: continue
        k += 1
        n_real = len([x for x in w if not x.trivial()])
        out.append(f"{pad}  {'┌' if n_real >= 2 else '├'} 波 {k}" + (f": 同時に {n_real} 個" if n_real >= 2 else ""))
        for x in shown: render(x, ind + 2, out, hide_trivial)
    if t.alts:
        out.append(f"{pad}  └ 選ばれる 1 行(候補):")
        for x in t.alts: render(x, ind + 2, out, hide_trivial)
    return out

def to_json(t):
    return {"kind": t.kind, "label": t.label, "work": t.work, "span": t.span, "effect": t.eff.kind(),
            "reads": sorted(map(str, t.eff.r)), "writes": sorted(map(str, t.eff.w)), "notes": t.notes,
            "waves": [[to_json(x) for x in w if not x.trivial()] for w in t.waves if any(not x.trivial() for x in w)],
            "alternatives": [to_json(x) for x in t.alts]}

def to_dot(P):
    lines, n = ["digraph plan {", "  rankdir=TB; node [shape=box, fontname=sans-serif];"], [0]
    def emit(t, parent=None, style=""):
        n[0] += 1; me = f"n{n[0]}"
        color = "lightyellow" if not t.eff.pure() else "white"
        lines.append(f'  {me} [label="{t.label}\\n仕事 {t.work} / 道 {t.span}", style=filled, fillcolor={color}];')
        if parent: lines.append(f"  {parent} -> {me}{style};")
        for i, w in enumerate(t.waves):
            real = [x for x in w if not x.trivial()]
            if len(real) >= 2:
                n[0] += 1; g = f"c{n[0]}"
                lines.append(f'  subgraph cluster_{g} {{ label="波 {i + 1}: 同時"; style=dashed;')
                for x in real: emit(x, me)
                lines.append("  }")
            else:
                for x in real: emit(x, me, ' [style=bold]')
        for x in t.alts: emit(x, me, " [style=dotted]")
    for i, t in enumerate(P.main_plans): emit(t)
    lines.append("}"); return "\n".join(lines)

def report(P):
    o = []
    o.append("■ 1. 関数の表(副作用・自己呼び出し・重さの概算)")
    for f, lam in P.defs.items():
        e = P.summ[f]; selfc = sum(1 for m in nodes_of(lam[2]) if m[0] == "seq" and m[1] and m[1][0] == ("id", f))
        extra = ""
        if not e.pure(): extra = f"  読む番地: {fmt_locs(e.r) if e.r else '-'} / 書く番地: {fmt_locs(e.w) if e.w else '-'}"
        o.append(f"  {f:<22} {e.kind():<4} 重さ {P.weight(f):>5}  自己呼び出し {selfc} 箇所{extra}")
    o.append("")
    o.append("■ 2. 並列にできる所(同時に評価してよい組。見込みは 仕事 ÷ 最長の道 の概算で、コア数 %d が上限)" % P.cores)
    if not P.opps: o.append("  (見つかりませんでした。重さが --min-work 未満・副作用がぶつかる・呼び出しが 1 つだけ のどれかです)")
    for i, op in enumerate(sorted(P.opps, key=lambda x: -x["work"]), 1):
        if op["speedup"] is None: sp = "投機(無駄になりうる)"
        elif op["kind"] == "分割統治の再帰": sp = f"再帰を深く分けるほどコア数({P.cores})倍に近づく見込み(1 段だけなら約 {op['speedup']:.1f} 倍)"
        elif op["speedup"] < 1.2: sp = f"効果は小さい(約 {op['speedup']:.1f} 倍。片方がほとんどの仕事をしている)"
        else: sp = f"見込み 約 {min(op['speedup'], P.cores):.1f} 倍"
        o.append(f"  {i}. {op['where']} の「{op['at']}」: {op['kind']}  → {sp}")
        for t in op["tasks"]: o.append(f"       - {t}")
        if op["kind"] == "分割統治の再帰":
            o.append(f"       助言: 呼び出しの深さが log2(コア数)+1 ≒ {max(1, (P.cores - 1).bit_length()) + 1} 段までを並列にし、それより奥は順番に(細かい仕事を同時に走らせると、起こす手間のほうが大きくなる)")
    o.append("")
    o.append("■ 3. 実行プラン(最上位の式。波は上から順に、「同時に」と書いた波の中は同時に走らせてよい)")
    for i, t in enumerate(P.main_plans, 1):
        o.append(f"  最上位の式 {i}:")
        o += ["    " + x for x in render(t)]
        o.append(f"    → 仕事 {t.work}・最長の道 {t.span} ・理想の速さ {t.work / t.span:.1f} 倍(コア {P.cores} なら高々 {min(t.work / t.span, P.cores):.1f} 倍)")
    o.append("")
    o.append("■ 4. 並列にできない所(順番を守る理由)")
    if not P.blocks: o.append("  (ありません)")
    for where, a, b, r in P.blocks[:40]: o.append(f"  {where}: 「{a}」→「{b}」  {r}")
    if len(P.blocks) > 40: o.append(f"  … ほか {len(P.blocks) - 40} 件")
    o.append("")
    o.append("注意: これは計画で、実行はしていない。重さは構文木の節の数の概算。メモリの番地が計算で決まる式は、安全側(ぶつかる)に倒している。")
    return "\n".join(o)


def main(argv):
    args = [a for a in argv if not a.startswith("--")]
    def opt(name, default):
        for i, a in enumerate(argv):
            if a == name and i + 1 < len(argv): return int(argv[i + 1])
        return default
    if len(args) != 1 or "--help" in argv:
        print(__doc__); return 2
    nodes = load(args[0])
    P = Planner(nodes, depth=opt("--depth", 3), rec_w=opt("--rec-weight", 200), min_work=opt("--min-work", 8), cores=opt("--cores", 4)).analyse()
    if "--json" in argv:
        print(json.dumps({"functions": {f: {"effect": P.summ[f].kind(), "weight": P.weight(f), "reads": sorted(map(str, P.summ[f].r)), "writes": sorted(map(str, P.summ[f].w))} for f in P.defs},
                          "opportunities": P.opps, "blocked": [dict(where=a, first=b, second=c, reason=d) for a, b, c, d in P.blocks],
                          "plan": [to_json(t) for t in P.main_plans]}, ensure_ascii=False, indent=1))
    elif "--dot" in argv: print(to_dot(P))
    else: print(report(P))
    return 0

if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
