"""--strict --asm(別の道: sign_asm.strict_rewrite)の試験。strict の読みの値と、書き換えた木から出した asm の値が同じこと。"""
import sys, os
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); sys.setrecursionlimit(20000)
src = open(os.path.join(HERE, "test_asm.py"), encoding="utf-8").read()
ns = {"__file__": os.path.join(HERE, "test_asm.py"), "__name__": "emu"}
exec(compile(src[:src.index("# ---------------- 処理系の答え")], "emu", "exec"), ns)
import sign_asm, sign_interp as S
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
]
bad = 0
for t, want in CASES:
    sv = strict_val(t)
    tree, rest = sign_asm.strict_rewrite(S.parse_source(t))
    try: got = ns["run_asm"](sign_asm.generate(tree)) if not rest else ("断り", rest[0][0])
    except Exception as e: got = ("例外", str(e)[:50])
    if sv != want or got != want: bad += 1; print("NG", repr(t), "strict", sv, "asm", got, "のはず", want)
print("全部 ok" if not bad else "NG %d 件" % bad)
sys.exit(1 if bad else 0)
