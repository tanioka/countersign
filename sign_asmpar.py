#!/usr/bin/env python3
"""sign_asmpar.py — AArch64 バックエンドの並列実行(--par[=N])。純粋な整数関数の兄弟の呼び出しを、スレッドの池に渡す。
Python 処理系の sign_par.py(第92段)と同じ考えを、生成物の中の小さな実行環境にしたもの。仕様に無い追加で、値は変えない。

何を並列にするか:  `fib (n - 1) + fib (n - 2)` のように、`+ - * / % && || ;; << >>` の両辺が『純粋な整数関数』の呼び出しのとき。
  純粋な整数関数 = 仮引数が全部 Int・返値が Int・本体が 整数の字面・仮引数・定数・算術・比べ・条件の行・同じ性質の関数の呼び出し だけ
  (メモリの読み書き・装置・器・文字列に触れない)。実引数は 整数の字面・仮引数・定数・+ - * だけ(副作用が無く、`__` にならない)。
  3 項以上の左結合の連なり `a + b + c + d`(葉が全部そうした呼び出し)は、最後の 1 つ以外を全部仕事に出し、畳み込みは元の演算で左から(第96段)。
  外れる式は今までどおり直列のコードが出る(同じ式に直列版も残してあり、実行時に選ぶ)。

仕組み:
  仕事の入れ物   呼び出し側のフレームに置く 5+k 語:  +0 状態(0 出さない 1 待ち 2 走行中 3 終わり 4 呼び側が奪った) +8 包みの番地 +16 答え
                +24 入れ子の段 +32 かかった時計の数 +40.. 実引数。
  ディスパッチ   _sign_par_submit(入れ物)が待ち行列(64 個の輪)に入れ、futex で眠っている労働者を 1 つ起こす。
                労働者(N-1 本)は最初の submit で clone(CLONE_THREAD) して作る(積みは 64 MiB の mmap)。作れなければ全部直列。
  スケジューラ   待ち行列は先入れ先出し。労働者は取り出して包み(_sign_pw_関数: 入れ物から実引数を読んで呼び、答えと時計を書く)を走らせ、状態 3 にして futex で起こす。
                合流 _sign_par_join は、まだ待ち行列にある仕事を奪って自分で走らせ(行列から外してから)、走行中なら futex で待つ。待つ間も、ほかの労働者が走る。
                待ち行列と状態の遷移はスピンロック 1 つで守る(区間は数命令)。
  粒度           (1) 空き(第97段): 数の箱 _sign_par_load = 待ち行列の仕事 + 労働者が走らせている仕事。N-1 以上なら空きの労働者が無いので、その所は直列
                (呼び側が先に読んで素通りし、submit でも錠の中で見直す。入れなかった仕事は合流で自分が計算する)。労働者の中でも同じ。
                (入れ子の段 TLS+8 は数え続けるが、もう上限には使わない。第96段までの 2 + ceil(log2 N) の固定の上限は無くした。)
                (2) 軽さ: 各所に数の箱を持ち、左の仕事が 1000 時計(cntvct_el0)より短かった回が 3 回続いたら、その所は以後ずっと直列。
限界:  Linux 用(--target=linux)だけ。時計の長さは cntvct_el0 の周波数による(Pi 4 は 54 MHz で 1000 時計 = 約 18 マイクロ秒)。
  Int の溢れの罠(wfi)は労働者の中で起きても、直列と同じに止まる(進まない)。終了は exit_group で、労働者もまとめて終わる。
  実機では未実行(疑似カーネルでは協調スレッドで、切り替えは futex・sched_yield・clone のときだけ)。
"""
import math

LIGHT = 100                   # これより短い(時計の刻みで)左の仕事は『軽い』。--par-light=N。既定の深さ方式では 100(Pi 3 A+ で約 5 µs、Pi 4 で約 2 µs)。--par-site-light の既定は 1000
LIGHT_SET = False             # --par-light=N が明示されたか
RELIGHT = True                # 軽さを『スレッドごとの積みの深さ』で覚える(既定。TLS+0 = 軽かった枠の x29、TLS+24 = 見送った回数。2^20 回で忘れる)。False = 呼び出し位置ごとの数え(3 回続けて軽いと以後ずっと直列。--par-site-light)
SPIN = 0                      # join が走行中の仕事を待つとき、futex で眠る前に状態を見に行く回数(--par-spin=N。0 なら眠る前に見ない)
STACK = 0x4000000             # 労働者の積み(64 MiB。mmap NORESERVE)
QCAP = 64
SPEC_N = 32                   # --par-spec の入れ物の池の数
SPEC_KEEP = 1                 # 投機のために使わず、--par の本来の並列にあけておく労働者の数(実機: --par=2 で投機が占めると 0.5〜0.95 倍に遅くなった)
SPEC_BLK = 160                # 入れ物 1 つの大きさ(+0..+104 は --par の入れ物と同じ、+104 失敗・+112 戻りの積み・+120 戻り先・+128 捨てた印)
OPS = {"+", "-", "*"}
ARITH = {"+", "-", "*", "/", "%", "&&", "||", ";;", "<<", ">>"}


def levels(n): return 2 + math.ceil(math.log2(n)) if n > 1 else 0


# ------------------------------------------------------------ どの関数が並列にできるか
PAR_KINDS = ("I", "C", "L", "S", "N")         # 仕事に出せる関数の仮引数の種類: Int・Char(1 語)・Int のリスト・文字列・入れ子の器({先頭の番地, 長さ} の 2 語)
MAX_WORDS = 8              # レジスタ x0〜x7 に載る語の数(包みが入れ物から読む)


def nwords(kinds):
    return sum(1 if k in ("I", "C") else 2 for k in kinds)


def eligible(p):
    """p(Program)の中の『純粋な整数関数』の集まり {名前: 仮引数の数}。仮引数は Int か、Int のリスト・文字列(読むだけ)。"""
    cands = {}
    for f, params in p.fns.items():
        body = p.bodies.get(f)
        if body is None or not (1 <= len(params) <= 8): continue
        ks = p.pkind.get(f, ())
        if any(k not in PAR_KINDS for k in ks) or nwords(ks) > MAX_WORDS or p.retk.get(f, "I") != "I": continue
        if getattr(p, "grow", {}).get(f): continue
        cands[f] = len(params)
    changed = True
    while changed:
        changed = False
        for f in list(cands):
            if not _pure(p, p.bodies[f], dict(zip(p.fns[f], p.pkind[f])), cands):
                del cands[f]; changed = True
    return cands


def _list_ok(p, n, params, cands):
    """読むだけの器・文字列を表す式: 器の仮引数・字面の名前・その末尾の切り出し `l ' a~`・スライス・入れ子の器の要素 `ls ' i`(`__` になりうるが、呼ぶ側が見る)。"""
    while n[0] == "block": n = n[1]
    if n[0] == "id": return params.get(n[1]) in ("L", "S", "N") or n[1] in p.lists or n[1] in p.strs or n[1] in p.nests
    if n[0] == "bin" and n[1] == "'":
        try:
            tl = p.tail_of(n)
            if tl is not None: return _list_ok(p, tl[0], params, cands)
            sl = p.slice_of(n)
            if sl is not None: return _list_ok(p, sl[0], params, cands)
        except Exception: return False
        l = n[2]
        while l[0] == "block": l = l[1]
        return l[0] == "id" and (params.get(l[1]) == "N" or l[1] in p.nests) and _pure(p, n[3], params, cands)
    return False


def _pure(p, n, params, cands):
    """副作用が無く、仮引数・定数・読むだけの器しか見ない式(本体はもう直列で出せている。ここは『別のスレッドで走らせてよいか』だけ)。"""
    k = n[0]
    if k == "lit": return True
    if k == "id": return n[1] in params or isinstance(p.consts.get(n[1]), int) or n[1] in getattr(p, "dyn", ()) or n[1] in p.chars
    if k in ("block", "neg", "not"): return _pure(p, n[1], params, cands)
    if k == "norm": return _list_ok(p, n[1], params, cands)                       # ||l||
    if k == "bin" and n[1] == "'":                                                  # l ' i(器・文字列の要素。入れ子の器の要素は器)
        try:
            if p.tail_of(n) is not None or p.slice_of(n) is not None: return False
        except Exception: return False
        l = n[2]
        while l[0] == "block": l = l[1]
        if l[0] != "id" or not (params.get(l[1]) in ("L", "S") or l[1] in p.lists or l[1] in p.strs): return False
        return _pure(p, n[3], params, cands)
    if k == "bin": return n[1] in ARITH and _pure(p, n[2], params, cands) and _pure(p, n[3], params, cands)
    if k == "cmp": return all(_pure(p, x, params, cands) for x in n[1])
    if k == "cases": return all((c is None or _pure(p, c, params, cands)) and _pure(p, v, params, cands) for c, v in n[1])
    if k == "seq":
        items = n[1]
        if not items or items[0][0] != "id" or items[0][1] not in cands: return False
        g = items[0][1]
        if len(items) - 1 != cands[g]: return False
        gk = p.pkind.get(g, ())
        return all((_pure(p, a, params, cands) if kd in ("I", "C") else _list_ok(p, a, params, cands)) for a, kd in zip(items[1:], gk))
    return False


def arg_ok(p, a):
    """実引数に置ける式: 整数の字面・名前・+ - *・符号・括弧(副作用が無い)。"""
    k = a[0]
    if k == "lit": return type(a[1]) is int
    if k == "id": return True
    if k in ("block", "neg"): return arg_ok(p, a[1])
    if k == "bin": return a[1] in OPS and arg_ok(p, a[2]) and arg_ok(p, a[3])
    return False


# ------------------------------------------------------------ --par-spec: 『必ず終わる』と言える関数
def _strip(n):
    while n[0] == "block": n = n[1]
    return n


def _lit(p, n):
    """整数の字面(負も)・Int の定数の名前なら その値、そうでなければ None。"""
    n = _strip(n)
    if n[0] == "lit" and type(n[1]) is int: return n[1]
    if n[0] == "neg":
        v = _lit(p, n[1]); return -v if v is not None else None
    if n[0] == "id" and isinstance(p.consts.get(n[1]), int) and n[1] not in p.fns: return p.consts[n[1]]
    return None


def _real_arith(p, f, n):
    """n は『`__` でない Int』か『溢れの罠』のどちらかになる式か: 字面、f の Int の仮引数(投機の入口で `__` でない)、それらの + - * 。呼び出しの答えは入れない。"""
    n = _strip(n)
    if _lit(p, n) is not None: return True
    if n[0] == "id": return n[1] in p.fns[f] and p.pkind[f][p.fns[f].index(n[1])] == "I"
    if n[0] == "neg": return _real_arith(p, f, n[1])
    if n[0] == "bin" and n[1] in ("+", "-", "*"): return _real_arith(p, f, n[2]) and _real_arith(p, f, n[3])
    return False


def _facts(p, c, params, truth):
    """条件 c が truth(成り立つ/外れる)とき、Int の仮引数について言える下限 'lo'・上限 'up' の集まり {(仮引数の位置, 'lo'|'up')}。
    仮引数は `__` でない(par_call が `__` になりうる実引数を通さない)ので、`p < K` が外れれば p >= K と言える。"""
    c = _strip(c)
    if c[0] == "bin" and c[1] in ("==", "!=="): return set()
    if c[0] == "bin" and c[1] == "&" and truth: return _facts(p, c[2], params, True) | _facts(p, c[3], params, True)
    if c[0] == "bin" and c[1] == "|" and not truth: return _facts(p, c[2], params, False) | _facts(p, c[3], params, False)
    if c[0] != "cmp" or len(c[2]) != 1: return set()
    a, b = _strip(c[1][0]), _strip(c[1][1]); op = c[2][0]
    if op not in ("<", "<=", ">", ">="): return set()
    if a[0] == "id" and a[1] in params and _lit(p, b) is not None: pos = params[a[1]]; rel = op
    elif b[0] == "id" and b[1] in params and _lit(p, a) is not None: pos = params[b[1]]; rel = {"<": ">", "<=": ">=", ">": "<", ">=": "<="}[op]
    else: return set()
    if not truth: rel = {"<": ">=", "<=": ">", ">": "<=", ">=": "<"}[rel]
    return {(pos, "lo" if rel in (">", ">=") else "up")}


def _self_calls(p, f, n, params, facts, out):
    """本体 n の中の f の自分の呼び出しを (呼び出し, その場で言える下限上限) の列 out に集める。"""
    if not isinstance(n, (tuple, list)) or not n: return
    if isinstance(n, tuple) and n[0] == "cases":
        known = set(facts)
        for c, v in n[1]:
            if c is not None:
                _self_calls(p, f, c, params, known, out)
                _self_calls(p, f, v, params, known | _facts(p, c, params, True), out)
                known = known | _facts(p, c, params, False)
            else: _self_calls(p, f, v, params, known, out)
        return
    if isinstance(n, tuple) and n[0] == "seq" and n[1] and n[1][0] == ("id", f): out.append((n, facts))
    for x in n: _self_calls(p, f, x, params, facts, out)


def _callees(n, el, acc):
    if not isinstance(n, (tuple, list)) or not n: return
    if isinstance(n, tuple) and n[0] == "seq" and n[1] and n[1][0][0] == "id" and n[1][0][1] in el: acc.add(n[1][0][1])
    for x in n: _callees(n, el, acc) if False else _callees(x, el, acc)


def terminating(p, el):
    """el(--par の純粋な整数関数)のうち、どんな(`__` でない)実引数でも必ず終わる物 {名前: None(再帰しない) か (位置, 'lo'|'up')(自分を呼ぶ)}。
    終わると言える形だけ:  相互再帰が無く、自分を呼ぶのは (1) どれも同じ Int の仮引数 p について `p - 字面` (下限が条件から言える所だけ)
    か (2) どれも `p + 字面` (上限が言える所だけ) の呼び方で、ほかの関数の呼び出しは終わると言える関数へ(再帰する関数へは、その位置の実引数が『字面・自分の Int の仮引数・それらの + - *』= `__` でない Int か溢れの罠になる式)。
    (言えない物は投機にしない。積みの深さは証明できないので、実行時の限界として残る。)"""
    calls = {}
    for f in el:
        acc = set(); _callees(p.bodies[f], el, acc); calls[f] = acc
    def reach(f):
        seen, st = set(), [g for g in calls[f] if g != f]
        while st:
            g = st.pop()
            if g in seen: continue
            seen.add(g); st += [h for h in calls[g] if h != g]
        return seen
    cyc = {f for f in el if f in reach(f)}
    ok = {}
    for f in el:
        if f in cyc: continue
        if f not in calls[f]: ok[f] = None; continue
        params = {nm: i for i, nm in enumerate(p.fns[f]) if p.pkind[f][i] == "I"}
        out = []; _self_calls(p, f, p.bodies[f], params, set(), out)
        found = None
        for (i, d) in [(i, d) for i in params.values() for d in ("lo", "up")]:
            good = True
            for call, facts in out:
                al = call[1][1:]
                a = _strip(al[i]) if i < len(al) else None
                nm = p.fns[f][i]
                if a is None or a[0] != "bin" or a[1] != ("-" if d == "lo" else "+") or _strip(a[2]) != ("id", nm) or (_lit(p, a[3]) or 0) <= 0 or (i, d) not in facts: good = False; break
            if good: found = (i, d); break
        if found: ok[f] = found
    changed = True
    while changed:
        changed = False
        for f in list(ok):
            for g in calls[f]:
                if g == f: continue
                if g not in ok: del ok[f]; changed = True; break
                if ok[g] is not None:                       # 再帰する関数を呼ぶ: その位置の実引数が字面
                    bad = []
                    def chk(n):
                        if not isinstance(n, (tuple, list)) or not n: return
                        if isinstance(n, tuple) and n[0] == "seq" and n[1] and n[1][0] == ("id", g):
                            al = n[1][1:]
                            if ok[g][0] >= len(al) or not _real_arith(p, f, al[ok[g][0]]): bad.append(1)
                        for x in n: chk(x)
                    chk(p.bodies[f])
                    if bad: del ok[f]; changed = True; break
    return ok


# ------------------------------------------------------------ 包み(仕事の入れ物から実引数を読んで関数を呼ぶ)
def wrapper(f, symbol, nparams):          # nparams = 渡す語の数(リスト・文字列は 2 語)
    ln = ["_sign_pw_%s:" % symbol,
          "\tstp x29, x30, [sp, #-32]!", "\tmov x29, sp", "\tstr x0, [x29, #16]",
          "\tmrs x10, cntvct_el0", "\tstr x10, [x29, #24]", "\tmov x9, x0"]
    ln += ["\tldr x%d, [x9, #%d]" % (i, 40 + 8 * i) for i in range(nparams)]
    ln += ["\tbl %s" % symbol, "\tldr x9, [x29, #16]", "\tstr x0, [x9, #16]",
           "\tmrs x10, cntvct_el0", "\tldr x11, [x29, #24]", "\tsub x10, x10, x11", "\tstr x10, [x9, #32]",
           "\tldp x29, x30, [sp], #32", "\tret", ""]
    return ln


def spec_wrapper(f, symbol, nparams, callee=None):
    """投機の包み: 走行の間 TLS+16 に入れ物を置き(罠はここへ巻き戻る)、積み・戻り先を入れ物に覚え、x19-x28 を保存して、戻り(罠のあとも)で戻す。"""
    ln = ["_sign_sw_%s:" % symbol,
          "\tstp x29, x30, [sp, #-128]!", "\tmov x29, sp",
          "\tstp x19, x20, [x29, #16]", "\tstp x21, x22, [x29, #32]", "\tstp x23, x24, [x29, #48]", "\tstp x25, x26, [x29, #64]", "\tstp x27, x28, [x29, #80]",
          "\tstr x0, [x29, #96]", "\tmov x9, x0",
          "\tmrs x11, tpidr_el0", "\tldr x12, [x11, #16]", "\tstr x12, [x29, #104]", "\tstr x0, [x11, #16]",
          "\tstr xzr, [x9, #104]", "\tmov x12, sp", "\tstr x12, [x9, #112]", "\tadr x12, _sign_swr_%s" % symbol, "\tstr x12, [x9, #120]"]
    ln += ["\tldr x%d, [x9, #%d]" % (i, 40 + 8 * i) for i in range(nparams)]
    ln += ["\tbl %s" % (callee or symbol), "_sign_swr_%s:" % symbol, "\tmov x29, sp",
           "\tldp x19, x20, [x29, #16]", "\tldp x21, x22, [x29, #32]", "\tldp x23, x24, [x29, #48]", "\tldp x25, x26, [x29, #64]", "\tldp x27, x28, [x29, #80]",
           "\tldr x9, [x29, #96]", "\tmrs x11, tpidr_el0", "\tldr x12, [x29, #104]", "\tstr x12, [x11, #16]",
           "\tstr x0, [x9, #16]",
           "\tldp x29, x30, [sp], #128", "\tret", ""]
    return ln


# ------------------------------------------------------------ 実行環境
def runtime(n, spec=False):
    w = n - 1
    L = []
    a = L.append
    a("// ---- 並列(--par): スレッドの池・待ち行列・合流。sign_asmpar.py ----")
    a("_sign_par_boot:  // 主スレッドの TLS(+8 = 入れ子の段)")
    a("\tadrp x9, _sign_par_tls"); a("\tadd x9, x9, :lo12:_sign_par_tls"); a("\tmsr tpidr_el0, x9"); a("\tret")
    a("_sign_par_acq:  // ロック(x9-x11 だけ使う)")
    a("\tadrp x9, _sign_par_lock"); a("\tadd x9, x9, :lo12:_sign_par_lock")
    a("1:"); a("\tldaxr w10, [x9]"); a("\tcbnz w10, 2f"); a("\tmov w10, #1"); a("\tstlxr w11, w10, [x9]"); a("\tcbnz w11, 1b"); a("\tret")
    a("2:"); a("\tyield"); a("\tb 1b")
    a("_sign_par_rel:  // x9 だけ使う")
    a("\tadrp x9, _sign_par_lock"); a("\tadd x9, x9, :lo12:_sign_par_lock"); a("\tstlr wzr, [x9]"); a("\tret")
    # submit
    a("_sign_par_submit:  // x0 = 入れ物、x1 = 強制(1 なら空きの数を見ない)。待ち行列に入れて労働者を 1 つ起こす(入れなければ状態は 0 のまま = 合流で直列)")
    a("\tstp x29, x30, [sp, #-32]!"); a("\tmov x29, sp"); a("\tstr x0, [x29, #16]"); a("\tstr x1, [x29, #24]")   # x1 = 1
    if spec: a("\tmrs x9, tpidr_el0"); a("\tldr x9, [x9, #16]"); a("\tcbnz x9, 9f")   # 投機の中では仕事を行列に出さない(巻き戻しで積みが消えるため。合流で自分が計算する)
    a("\tadrp x9, _sign_par_init"); a("\tadd x9, x9, :lo12:_sign_par_init"); a("\tldr x10, [x9]"); a("\tcbnz x10, 1f")
    a("\tmov x10, #1"); a("\tstr x10, [x9]"); a("\tbl _sign_par_spawn")
    a("1:"); a("\tadrp x9, _sign_par_nw"); a("\tadd x9, x9, :lo12:_sign_par_nw"); a("\tldr x10, [x9]"); a("\tcbz x10, 9f")
    a("\tbl _sign_par_acq"); a("\tldr x0, [x29, #16]")
    a("\tadrp x9, _sign_par_qh"); a("\tadd x9, x9, :lo12:_sign_par_qh"); a("\tldr x10, [x9]")
    a("\tadrp x9, _sign_par_qt"); a("\tadd x9, x9, :lo12:_sign_par_qt"); a("\tldr x11, [x9]")
    a("\tadrp x6, _sign_par_load"); a("\tadd x6, x6, :lo12:_sign_par_load"); a("\tldr x7, [x6]"); a("\tldr x15, [x29, #24]"); a("\tcbnz x15, 7f"); a("\tcmp x7, #%d" % w); a("\tb.hs 8f"); a("7:")  # 空きの労働者が無ければ入れない(合流で自分が計算)
    a("\tsub x12, x11, x10"); a("\tcmp x12, #%d" % QCAP); a("\tb.hs 8f")
    a("\tand x12, x11, #%d" % (QCAP - 1)); a("\tadrp x13, _sign_par_q"); a("\tadd x13, x13, :lo12:_sign_par_q"); a("\tadd x13, x13, x12, lsl #3"); a("\tstr x0, [x13]")
    a("\tmov x14, #1"); a("\tstr x14, [x0]"); a("\tadd x7, x7, #1"); a("\tstr x7, [x6]")
    a("\tadd x11, x11, #1"); a("\tstr x11, [x9]")
    a("\tadrp x13, _sign_par_seq"); a("\tadd x13, x13, :lo12:_sign_par_seq"); a("\tldr w14, [x13]"); a("\tadd w14, w14, #1"); a("\tstr w14, [x13]")
    a("\tbl _sign_par_rel")
    a("\tadrp x0, _sign_par_seq"); a("\tadd x0, x0, :lo12:_sign_par_seq"); a("\tmov x1, #129"); a("\tmov x2, #1"); a("\tmov x3, #0"); a("\tmov x4, #0"); a("\tmov x5, #0"); a("\tmov x8, #98"); a("\tsvc #0")
    a("\tb 9f")
    a("8:"); a("\tbl _sign_par_rel")
    a("9:"); a("\tldp x29, x30, [sp], #32"); a("\tret")
    # spawn
    a("_sign_par_spawn:  // 労働者を %d 本作る(作れた数が _sign_par_nw)" % w)
    a("\tstp x29, x30, [sp, #-32]!"); a("\tmov x29, sp"); a("\tstr xzr, [x29, #16]")
    a("1:"); a("\tldr x9, [x29, #16]"); a("\tcmp x9, #%d" % w); a("\tb.hs 9f")
    a("\tmov x0, #0"); a("\tmov x1, #%d" % STACK); a("\tmov x2, #3"); a("\tmov x3, #0x4022"); a("\tmovk x3, #2, lsl #16"); a("\tmov x4, #-1"); a("\tmov x5, #0"); a("\tmov x8, #222"); a("\tsvc #0")
    a("\ttbnz x0, #63, 9f")
    a("\tmov x1, #%d" % STACK); a("\tadd x1, x0, x1")
    a("\tldr x9, [x29, #16]"); a("\tadd x9, x9, #1"); a("\tlsl x9, x9, #5")
    a("\tadrp x3, _sign_par_tls"); a("\tadd x3, x3, :lo12:_sign_par_tls"); a("\tadd x3, x3, x9")
    a("\tmovz x0, #0x0F00"); a("\tmovk x0, #0xD, lsl #16"); a("\tmov x2, #0"); a("\tmov x4, #0"); a("\tmov x8, #220"); a("\tsvc #0")
    a("\tcbz x0, _sign_par_worker"); a("\ttbnz x0, #63, 9f")
    a("\tadrp x9, _sign_par_nw"); a("\tadd x9, x9, :lo12:_sign_par_nw"); a("\tldr x10, [x9]"); a("\tadd x10, x10, #1"); a("\tstr x10, [x9]")
    a("\tldr x9, [x29, #16]"); a("\tadd x9, x9, #1"); a("\tstr x9, [x29, #16]"); a("\tb 1b")
    a("9:"); a("\tldp x29, x30, [sp], #32"); a("\tret")
    # worker
    a("_sign_par_worker:  // 労働者の本体。待ち行列から取り出して走らせ続ける(終わらない。プロセスの終了で消える)")
    a("1:"); a("\tbl _sign_par_acq")
    a("\tadrp x9, _sign_par_qh"); a("\tadd x9, x9, :lo12:_sign_par_qh"); a("\tldr x10, [x9]")
    a("\tadrp x11, _sign_par_qt"); a("\tadd x11, x11, :lo12:_sign_par_qt"); a("\tldr x11, [x11]")
    a("\tcmp x10, x11"); a("\tb.hs 3f")
    a("\tand x12, x10, #%d" % (QCAP - 1)); a("\tadrp x13, _sign_par_q"); a("\tadd x13, x13, :lo12:_sign_par_q"); a("\tadd x13, x13, x12, lsl #3"); a("\tldr x0, [x13]")
    a("\tadd x10, x10, #1"); a("\tstr x10, [x9]"); a("\tmov x14, #2"); a("\tstr x14, [x0]")
    a("\tsub sp, sp, #16"); a("\tstr x0, [sp]"); a("\tbl _sign_par_rel"); a("\tldr x0, [sp]")
    a("\tldr x9, [x0, #24]"); a("\tmrs x10, tpidr_el0"); a("\tstr x9, [x10, #8]"); a("\tstr xzr, [x10]")   # 新しい仕事では軽さの深さの覚えを消す(--par-relight)
    a("\tldr x9, [x0, #8]"); a("\tblr x9")
    a("\tbl _sign_par_acq"); a("\tadrp x6, _sign_par_load"); a("\tadd x6, x6, :lo12:_sign_par_load"); a("\tldr x7, [x6]"); a("\tsub x7, x7, #1"); a("\tstr x7, [x6]")
    if not spec:
        a("\tbl _sign_par_rel")
        a("\tldr x0, [sp]"); a("\tadd sp, sp, #16"); a("\tmov x9, #3"); a("\tstlr x9, [x0]")
    else:
        a("\tldr x0, [sp]"); a("\tadrp x9, _sign_spec_pool"); a("\tadd x9, x9, :lo12:_sign_spec_pool"); a("\tcmp x0, x9"); a("\tb.lo 6f")
        a("\tadrp x10, _sign_spec_end"); a("\tadd x10, x10, :lo12:_sign_spec_end"); a("\tcmp x0, x10"); a("\tb.hs 6f")
        a("\tldr x9, [x0, #128]"); a("\tcbz x9, 5f")   # 投機の仕事: 親が捨てたなら、錠の中で入れ物を空きに戻して誰も起こさない
        a("\tbl _sign_spec_putfree"); a("\tbl _sign_par_rel"); a("\tadd sp, sp, #16"); a("\tb 1b")
        a("5:"); a("\tmov x9, #3"); a("\tstlr x9, [x0]"); a("\tbl _sign_par_rel"); a("\tb 7f")
        a("6:"); a("\tbl _sign_par_rel"); a("\tmov x9, #3"); a("\tstlr x9, [x0]")
        a("7:"); a("\tldr x0, [sp]"); a("\tadd sp, sp, #16")
    a("\tmov x1, #129"); a("\tmov x2, #0x7FFFFFFF"); a("\tmov x3, #0"); a("\tmov x4, #0"); a("\tmov x5, #0"); a("\tmov x8, #98"); a("\tsvc #0")
    a("\tb 1b")
    a("3:"); a("\tadrp x13, _sign_par_seq"); a("\tadd x13, x13, :lo12:_sign_par_seq"); a("\tldr w14, [x13]")
    a("\tsub sp, sp, #16"); a("\tstr w14, [sp]"); a("\tbl _sign_par_rel"); a("\tldr w2, [sp]"); a("\tadd sp, sp, #16")
    a("\tadrp x0, _sign_par_seq"); a("\tadd x0, x0, :lo12:_sign_par_seq"); a("\tmov x1, #128"); a("\tmov x3, #0"); a("\tmov x4, #0"); a("\tmov x5, #0"); a("\tmov x8, #98"); a("\tsvc #0")
    a("\tb 1b")
    # join
    a("_sign_par_steal:  // x0 = 入れ物。まだ待ち行列にあれば奪って自分で走らせ、答えを入れ物に書いて状態 3 にする。走行中・終わりなら何もせず返る(待たない)")
    a("\tldar x9, [x0]"); a("\tcmp x9, #1"); a("\tb.ne 9f")
    a("\tstp x29, x30, [sp, #-32]!"); a("\tmov x29, sp"); a("\tstr x0, [x29, #16]")
    a("\tbl _sign_par_acq"); a("\tldr x0, [x29, #16]"); a("\tldr x9, [x0]"); a("\tcmp x9, #1"); a("\tb.ne 4f")
    a("\tadrp x9, _sign_par_qh"); a("\tadd x9, x9, :lo12:_sign_par_qh"); a("\tldr x10, [x9]")
    a("\tadrp x9, _sign_par_qt"); a("\tadd x9, x9, :lo12:_sign_par_qt"); a("\tldr x11, [x9]")
    a("\tadrp x13, _sign_par_q"); a("\tadd x13, x13, :lo12:_sign_par_q")
    a("6:"); a("\tcmp x10, x11"); a("\tb.hs 4f"); a("\tand x12, x10, #%d" % (QCAP - 1)); a("\tadd x14, x13, x12, lsl #3"); a("\tldr x15, [x14]"); a("\tcmp x15, x0"); a("\tb.eq 10f")
    a("\tadd x10, x10, #1"); a("\tb 6b")
    a("10:"); a("\tsub x11, x11, #1"); a("\tand x15, x11, #%d" % (QCAP - 1)); a("\tadd x15, x13, x15, lsl #3"); a("\tldr x15, [x15]"); a("\tstr x15, [x14]"); a("\tstr x11, [x9]")
    a("\tadrp x6, _sign_par_load"); a("\tadd x6, x6, :lo12:_sign_par_load"); a("\tldr x7, [x6]"); a("\tsub x7, x7, #1"); a("\tstr x7, [x6]")
    a("\tmov x9, #4"); a("\tstr x9, [x0]"); a("\tbl _sign_par_rel")
    a("\tldr x0, [x29, #16]"); a("\tldr x9, [x0, #8]"); a("\tblr x9")
    a("\tldr x1, [x29, #16]"); a("\tstr x0, [x1, #16]"); a("\tmov x9, #3"); a("\tstlr x9, [x1]"); a("\tb 8f")
    a("4:"); a("\tbl _sign_par_rel")
    a("8:"); a("\tldp x29, x30, [sp], #32")
    a("9:"); a("\tret"); a("")
    a("_sign_par_join:  // x0 = 入れ物。答え(x0)を返す。待ち行列に残っていれば奪って自分で走らせる")
    a("\tstp x29, x30, [sp, #-32]!"); a("\tmov x29, sp"); a("\tstr x0, [x29, #16]")
    a("\tldar x9, [x0]"); a("\tcbz x9, 5f"); a("\tcmp x9, #3"); a("\tb.eq 8f"); a("\tcmp x9, #1"); a("\tb.ne 2f")
    a("\tbl _sign_par_acq"); a("\tldr x0, [x29, #16]"); a("\tldr x9, [x0]"); a("\tcmp x9, #1"); a("\tb.ne 4f")
    a("\tadrp x9, _sign_par_qh"); a("\tadd x9, x9, :lo12:_sign_par_qh"); a("\tldr x10, [x9]")
    a("\tadrp x9, _sign_par_qt"); a("\tadd x9, x9, :lo12:_sign_par_qt"); a("\tldr x11, [x9]")
    a("\tadrp x13, _sign_par_q"); a("\tadd x13, x13, :lo12:_sign_par_q")
    a("6:"); a("\tcmp x10, x11"); a("\tb.hs 7f"); a("\tand x12, x10, #%d" % (QCAP - 1)); a("\tadd x14, x13, x12, lsl #3"); a("\tldr x15, [x14]"); a("\tcmp x15, x0"); a("\tb.eq 10f")
    a("\tadd x10, x10, #1"); a("\tb 6b")
    a("10:"); a("\tsub x11, x11, #1"); a("\tand x15, x11, #%d" % (QCAP - 1)); a("\tadd x15, x13, x15, lsl #3"); a("\tldr x15, [x15]"); a("\tstr x15, [x14]"); a("\tstr x11, [x9]")
    a("\tadrp x6, _sign_par_load"); a("\tadd x6, x6, :lo12:_sign_par_load"); a("\tldr x7, [x6]"); a("\tsub x7, x7, #1"); a("\tstr x7, [x6]")
    a("7:"); a("\tmov x9, #4"); a("\tstr x9, [x0]"); a("\tbl _sign_par_rel"); a("\tb 5f")
    a("4:"); a("\tbl _sign_par_rel")
    a("2:"); a("\tldr x0, [x29, #16]")
    if SPIN > 0:   # 眠る前に少し見る(軽い仕事なら眠らずに済む)。x10 だけ使う
        a("\tmov x10, #%d" % min(SPIN, 65535)); a("11:"); a("\tldar x9, [x0]"); a("\tcmp x9, #3"); a("\tb.eq 8f"); a("\tyield"); a("\tsubs x10, x10, #1"); a("\tb.ne 11b")
    a("3:"); a("\tldar x9, [x0]"); a("\tcmp x9, #3"); a("\tb.eq 8f"); a("\tmov w2, w9"); a("\tmov x1, #128"); a("\tmov x3, #0"); a("\tmov x4, #0"); a("\tmov x5, #0"); a("\tmov x8, #98"); a("\tsvc #0")
    a("\tldr x0, [x29, #16]"); a("\tb 3b")
    a("5:"); a("\tldr x0, [x29, #16]"); a("\tldr x9, [x0, #8]"); a("\tblr x9"); a("\tb 9f")
    a("8:"); a("\tldr x0, [x29, #16]"); a("\tldr x0, [x0, #16]")
    a("9:"); a("\tldp x29, x30, [sp], #32"); a("\tret"); a("")
    if spec:
        N = SPEC_N
        a("// ---- 投機(--par-spec): 静的な池の入れ物・巻き戻し ----")
        a("_sign_spec_putfree:  // 錠を持ったまま。x0 = 入れ物を空きの積みへ(x12-x14 だけ使う)")
        a("\tadrp x13, _sign_spec_fn"); a("\tadd x13, x13, :lo12:_sign_spec_fn"); a("\tldr x12, [x13]")
        a("\tadrp x14, _sign_spec_fs"); a("\tadd x14, x14, :lo12:_sign_spec_fs"); a("\tadd x14, x14, x12, lsl #3"); a("\tstr x0, [x14]")
        a("\tadd x12, x12, #1"); a("\tstr x12, [x13]"); a("\tret")
        a("_sign_spec_alloc:  // x0 = 空きの入れ物(無ければ 0)。投機の中・空きの労働者が無いときは 0")
        a("\tstp x29, x30, [sp, #-16]!")
        a("\tmrs x9, tpidr_el0"); a("\tldr x9, [x9, #16]"); a("\tcbnz x9, 8f")
        a("\tadrp x9, _sign_par_load"); a("\tadd x9, x9, :lo12:_sign_par_load"); a("\tldr x10, [x9]"); a("\tcmp x10, #%d" % max(w - SPEC_KEEP, 0)); a("\tb.hs 8f")   # 投機は労働者を SPEC_KEEP 本あけておく(--par=2 では投機しない)
        a("\tbl _sign_par_acq")
        a("\tadrp x9, _sign_spec_fn"); a("\tadd x9, x9, :lo12:_sign_spec_fn"); a("\tldr x10, [x9]"); a("\tcbz x10, 1f")
        a("\tsub x10, x10, #1"); a("\tstr x10, [x9]")
        a("\tadrp x11, _sign_spec_fs"); a("\tadd x11, x11, :lo12:_sign_spec_fs"); a("\tadd x11, x11, x10, lsl #3"); a("\tldr x0, [x11]"); a("\tb 3f")
        a("1:"); a("\tadrp x9, _sign_spec_bump"); a("\tadd x9, x9, :lo12:_sign_spec_bump"); a("\tldr x10, [x9]"); a("\tcmp x10, #%d" % N); a("\tb.hs 2f")
        a("\tadd x11, x10, #1"); a("\tstr x11, [x9]"); a("\tmov x12, #%d" % SPEC_BLK); a("\tmul x12, x10, x12")
        a("\tadrp x0, _sign_spec_pool"); a("\tadd x0, x0, :lo12:_sign_spec_pool"); a("\tadd x0, x0, x12"); a("\tb 3f")
        a("2:"); a("\tmov x0, #0")
        a("3:"); a("\tcbz x0, 4f"); a("\tstr xzr, [x0, #128]")
        a("4:"); a("\tbl _sign_par_rel"); a("\tldp x29, x30, [sp], #16"); a("\tret")
        a("8:"); a("\tmov x0, #0"); a("\tldp x29, x30, [sp], #16"); a("\tret")
        a("_sign_spec_join:  // x0 = 入れ物。x0 = 答え、x1 = 失敗の印(罠・巻き戻しなら 1)。入れ物は空きに戻す")
        a("\tstp x29, x30, [sp, #-48]!"); a("\tmov x29, sp"); a("\tstr x0, [x29, #16]")
        a("\tbl _sign_par_join")
        a("\tldr x9, [x29, #16]"); a("\tldr x1, [x9, #104]"); a("\tstr x0, [x29, #24]"); a("\tstr x1, [x29, #32]")
        a("\tbl _sign_par_acq"); a("\tldr x0, [x29, #16]"); a("\tbl _sign_spec_putfree"); a("\tbl _sign_par_rel")
        a("\tldr x0, [x29, #24]"); a("\tldr x1, [x29, #32]"); a("\tldp x29, x30, [sp], #48"); a("\tret")
        a("_sign_spec_cancel:  // x0 = 入れ物。要らなくなった。行列にあれば外し、走行中なら労働者が終わったとき空きに戻す、そうでなければ今戻す")
        a("\tstp x29, x30, [sp, #-32]!"); a("\tmov x29, sp"); a("\tstr x0, [x29, #16]")
        a("\tbl _sign_par_acq"); a("\tldr x0, [x29, #16]"); a("\tldr x9, [x0]")
        a("\tcmp x9, #1"); a("\tb.ne 5f")
        a("\tadrp x9, _sign_par_qh"); a("\tadd x9, x9, :lo12:_sign_par_qh"); a("\tldr x10, [x9]")
        a("\tadrp x9, _sign_par_qt"); a("\tadd x9, x9, :lo12:_sign_par_qt"); a("\tldr x11, [x9]")
        a("\tadrp x13, _sign_par_q"); a("\tadd x13, x13, :lo12:_sign_par_q")
        a("4:"); a("\tcmp x10, x11"); a("\tb.hs 6f"); a("\tand x12, x10, #%d" % (QCAP - 1)); a("\tadd x14, x13, x12, lsl #3"); a("\tldr x15, [x14]"); a("\tcmp x15, x0"); a("\tb.eq 3f")
        a("\tadd x10, x10, #1"); a("\tb 4b")
        a("3:"); a("\tsub x11, x11, #1"); a("\tand x15, x11, #%d" % (QCAP - 1)); a("\tadd x15, x13, x15, lsl #3"); a("\tldr x15, [x15]"); a("\tstr x15, [x14]"); a("\tstr x11, [x9]")
        a("\tadrp x6, _sign_par_load"); a("\tadd x6, x6, :lo12:_sign_par_load"); a("\tldr x7, [x6]"); a("\tsub x7, x7, #1"); a("\tstr x7, [x6]")
        a("\tb 6f")
        a("5:"); a("\tcmp x9, #2"); a("\tb.ne 6f"); a("\tmov x10, #1"); a("\tstr x10, [x0, #128]"); a("\tb 7f")
        a("6:"); a("\tbl _sign_spec_putfree")
        a("7:"); a("\tbl _sign_par_rel"); a("\tldp x29, x30, [sp], #32"); a("\tret")
        a("_sign_spec_rollback:  // 罠(.Ltrap)から。x16 = 走行中の投機の入れ物。失敗の印を立て、包みの積み・戻り先へ戻る")
        a("\tmov x9, #1"); a("\tstr x9, [x16, #104]"); a("\tldr x9, [x16, #112]"); a("\tmov sp, x9"); a("\tldr x9, [x16, #120]"); a("\tbr x9")
        a("_sign_spec_end_marker:")
    return L


def bss(n, sites, spec=False):
    sp = ["\t.balign 16", "_sign_spec_pool:", "\t.skip %d" % (SPEC_BLK * SPEC_N), "_sign_spec_end:", "_sign_spec_fs:", "\t.skip %d" % (8 * SPEC_N),
          "_sign_spec_fn:", "\t.skip 8", "_sign_spec_bump:", "\t.skip 8"] if spec else []
    return ["\t.section .bss", "\t.balign 16", "_sign_par_tls:", "\t.skip %d" % (32 * n)] + sp + [
            "_sign_par_q:", "\t.skip %d" % (8 * QCAP),
            "\t.balign 8", "_sign_par_qh:", "\t.skip 8", "_sign_par_qt:", "\t.skip 8", "_sign_par_init:", "\t.skip 8", "_sign_par_nw:", "\t.skip 8", "_sign_par_load:", "\t.skip 8",
            "\t.balign 4", "_sign_par_lock:", "\t.skip 4", "_sign_par_seq:", "\t.skip 4", "\t.balign 8"] + \
           sum((["_sign_ps%d:" % i, "\t.skip 8"] for i in range(sites)), [])
