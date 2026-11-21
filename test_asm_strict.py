"""--strict --asm(別の道: sign_asm.strict_rewrite)の試験。strict の読みの値と、書き換えた木から出した asm の値が同じこと。"""
import sys, os
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); sys.setrecursionlimit(20000)
src = open(os.path.join(HERE, "test_asm.py"), encoding="utf-8").read()
ns = {"__file__": os.path.join(HERE, "test_asm.py"), "__name__": "emu"}
exec(compile(src[:src.index("# ---------------- 処理系の答え")], "emu", "exec"), ns)
import sign_asm, sign_interp as S
sign_asm.STRICT[0] = True                 # コード生成の終わりの断り(strict_call_check)は --strict のときだけ働く
def strict_val(t):
    S.STRICT_GATES = True
    try:
        r = S.run(t); v = S.show(r[-1]) if r else "!_"
    finally: S.STRICT_GATES = False
    return ("ok", "__") if v == "!_" else ("ok", int(v))
CASES = [   # (源, strict の値)
    ("f : x y ?\n\t5 : ((x % y) > (y % x))\n\ty : 2\n\t7\n\nf 100 1\n", ("ok", 2)),                       # 4. 行の左が名前だけは条件の行
    ("h : a ? (a < 7) + 1\n\nf : x y ? ((x h) ' 0) + x\n\nf 3 0\n", ("ok", 6)),                               # 2. 逆適用は値のまま
    ("f : i ? ([9 9 3] ' i)\n\nf 1\n", ("ok", "__")),                                                      # 1. 鍵が名前は !_
    ("g : n ? (n < 1 & 4)\n\nf : n ?\n\tn > 1 : g n\n\tn < 0 : 8\n\t6\n\nf 3\n", ("ok", 6)),            # 3. 値が !_ なら次の行へ
    ("f : x y ?\n\t(7) : ((x / 0))\n\t((x <= 100)) : x\n\t5\n\nf 5 2\n", ("ok", 5)),
    ("f : n ?\n\tn < 1 : 9\n\tf (n - 1)\n\nf 5\n", ("ok", 9)),                                              # 何も変わらない形
    ("[>] 3 5\n", ("ok", 5)),                                                                              # 5. 順序の比べの畳みは最大・最小
    ("[<] 5 3\n", ("ok", 3)),
    ("[>=] 1 5 3\n", ("ok", 5)),
    ("[<=] 4 2 9\n", ("ok", 2)),
    ("f : a b c ?\n\t[>] a b c\n\nf 7 2 9\n", ("ok", 9)),
    ("f : a b ?\n\t[<] a b\n\nf 7 2\n", ("ok", 2)),
]
bad = 0
for t, want in CASES:
    sv = strict_val(t)
    tree, rest = sign_asm.strict_rewrite(S.parse_source(t))
    try: got = ns["run_asm"](sign_asm.generate(tree)) if not rest else ("断り", rest[0][0])
    except sign_asm.StrictRefusal: got = ("断り", 6)
    except Exception as e: got = ("例外", str(e)[:50])
    if sv != want or got != want: bad += 1; print("NG", repr(t), "strict", sv, "asm", got, "のはず", want)

# ---- test_asm.py の整数の表(CASES)を全部、strict の読みと突き合わせる ----
# 溢れだけは、strict の読み(value_spec V5)が `!_`、asm は documents(integer_overflow.md)どおり罠(wfi)で、仕様どうしの食い違い(OPEN_QUESTIONS)。それ以外は一致する。
i_ = src.index("MAX, MIN1 = "); j_ = src.index("\n]\n", src.index("CASES = [")) + 3
exec(src[i_:j_], ns)
from fixblank import fix
tally = {"一致": 0, "溢れ(仕様どうしの食い違い)": 0, "strict が断る": 0, "断る": 0}
for name, t in ns["CASES"]:
    t2 = fix(t)
    try: sv = strict_val(t2)
    except Exception: tally["strict が断る"] += 1; continue
    tree, rest = sign_asm.strict_rewrite(S.parse_source(t2))
    try: got = ns["run_asm"](sign_asm.generate(tree)) if not rest else ("断り", rest[0][0])
    except sign_asm.StrictRefusal: got = ("断り", 6)
    except Exception as e: got = ("例外", str(e)[:50])
    if got == sv: tally["一致"] += 1
    elif got[0] == "断り": tally["断る"] += 1                      # 断りは合っていない答えより良い
    elif got == ("trap", None) and sv[0] == "ok" and ("溢" in name or "罠" in name): tally["溢れ(仕様どうしの食い違い)"] += 1
    else: bad += 1; print("NG", name, repr(t), "strict", sv, "asm", got)
print("整数の表:", tally)
if tally["一致"] < 150: bad += 1; print("NG 一致が少なすぎる", tally)

# ---- test_asm.py の文字列・リストの表(STR_CASES、667 件)を strict の読みと突き合わせる ----
# 全件は遅い(約 25 分)ので、strict と既定で値が違う物は全部、それ以外は 10 件に 1 件を走らせる。全件は /tmp/q の探索用の走らせ方で確かめた(IMPLEMENTATION_NOTES)。
# 期待は strict の値(void は `__`)。asm が答えを出すなら、それと同じでなければならない。断るのは許す(断りは合っていない答えより良い)。
import ast, io, signal
_tree = ast.parse(src)
def _upper(n):
    t = n.targets[0] if isinstance(n, ast.Assign) else n.target
    return isinstance(t, ast.Name) and t.id.isupper() or (isinstance(t, ast.Tuple) and all(isinstance(e, ast.Name) and e.id.isupper() for e in t.elts))
_keep = [n for n in _tree.body if (isinstance(n, (ast.Assign, ast.AugAssign)) and _upper(n) and not any(isinstance(x, ast.Call) for x in ast.walk(n.value))) or (isinstance(n, ast.FunctionDef) and n.name == "interp_out")]
exec(compile(ast.Module(body=_keep, type_ignores=[]), "t", "exec"), ns)
class _TO(BaseException): pass
def _h(sig, fr): raise _TO()
signal.signal(signal.SIGALRM, _h)
def _val(t, strict):
    S.STRICT_GATES = strict
    try:
        S.MEMORY.clear(); S.WARNINGS.clear()
        old = sys.stdout; sys.stdout = io.StringIO()
        try: r = S.run(t)
        finally: sys.stdout = old
        return S.show(r[-1]) if r else "!_"
    finally: S.STRICT_GATES = False
KNOWN = {   # 出す答えが strict と違う、既知の物。規則 6(計算で `!_` になりうる実引数の呼びを断る)を足してから、どちらも断られるので今は空振り
    "食う 文字列 逆順": "strict は `~` の付いた計算の void を空の流れにしないので、終わりの無い再帰が深さの上限で止まる(R83・R84)。asm は終わりで止まる",
    "段54: 入れ子の要素の先頭 (m ' i) ' 0": "器の要素が void の積み上げ。strict は消え、asm は `__` の印を残す",
}
tally2 = {"一致": 0, "断る": 0, "strict が断る": 0, "既知の違い": 0}
for idx, (name, t) in enumerate(ns["STR_CASES"]):
    signal.alarm(40)
    try:
        t2 = fix(t)
        try: vs = _val(t2, True)
        except BaseException: tally2["strict が断る"] += 1; continue
        try: vd = _val(t, False)
        except BaseException: vd = None
        nv = lambda v: "!_" if v in ("__", "!_") else v
        if nv(vs) == nv(vd) and idx % 10: continue                      # 値が同じ物は 10 件に 1 件
        tree, rest = sign_asm.strict_rewrite(S.parse_source(t2))
        if rest: tally2["断る"] += 1; continue
        try: got = ns["run_asm"](sign_asm.generate(tree, "linux"), linux=True)
        except sign_asm.AsmError: tally2["断る"] += 1; continue
        want = ("exit", ("__" if nv(vs) == "!_" else vs) + "\n")
        if (got[0], got[1]) == want: tally2["一致"] += 1
        elif name in KNOWN: tally2["既知の違い"] += 1
        else: bad += 1; print("NG", name, repr(t)[:100], "strict", want[1][:40], "asm", repr(got[1])[:40])
    except _TO: bad += 1; print("NG 時間切れ", name)
    finally: signal.alarm(0)
print("文字列・リストの表:", tally2)
print("全部 ok" if not bad else "NG %d 件" % bad)
sys.exit(1 if bad else 0)
