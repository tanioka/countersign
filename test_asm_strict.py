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

# ---- test_asm.py の整数の表(CASES)を全部、strict の読みと突き合わせる ----
# 溢れだけは、strict の読み(value_spec V5)が `!_`、asm は documents(integer_overflow.md)どおり罠(wfi)で、仕様どうしの食い違い(OPEN_QUESTIONS)。それ以外は一致する。
i_ = src.index("MAX, MIN1 = "); j_ = src.index("\n]\n", src.index("CASES = [")) + 3
exec(src[i_:j_], ns)
from fixblank import fix
tally = {"一致": 0, "溢れ(仕様どうしの食い違い)": 0, "strict が断る": 0}
for name, t in ns["CASES"]:
    t2 = fix(t)
    try: sv = strict_val(t2)
    except Exception: tally["strict が断る"] += 1; continue
    tree, rest = sign_asm.strict_rewrite(S.parse_source(t2))
    try: got = ns["run_asm"](sign_asm.generate(tree)) if not rest else ("断り", rest[0][0])
    except Exception as e: got = ("例外", str(e)[:50])
    if got == sv: tally["一致"] += 1
    elif got == ("trap", None) and sv[0] == "ok" and ("溢" in name or "罠" in name): tally["溢れ(仕様どうしの食い違い)"] += 1
    else: bad += 1; print("NG", name, repr(t), "strict", sv, "asm", got)
print("整数の表:", tally)
if tally["一致"] < 150: bad += 1; print("NG 一致が少なすぎる", tally)
print("全部 ok" if not bad else "NG %d 件" % bad)
sys.exit(1 if bad else 0)
