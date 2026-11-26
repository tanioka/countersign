"""test_asm_open.py — 終端の無い規則(`[a ~+ s]` 等差、`[a ~* k]` 等比)の `' n` を、機械語(エミュレータ)と処理系(--check-int)で突き合わせる。
運び方(等差 = {a, s, INT64_MIN}、等比 = {a, 0, k})は実装の選択(IMPLEMENTATION_NOTES.md)。取り出し以外(個数・並べ出し・表示)は罠。"""
import os, random, sys
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
_src = open(os.path.join(HERE, "test_asm.py"), encoding="utf-8").read().split("# ---------------- エミュレータ")[0] + "\n" + open(os.path.join(HERE, "test_asm.py"), encoding="utf-8").read().split("# ---------------- エミュレータ ----------------")[1].split("# ---------------- 処理系の答え")[0] + "\n# ---------------- 処理系の答え" + open(os.path.join(HERE, "test_asm.py"), encoding="utf-8").read().split("# ---------------- 処理系の答え ----------------")[1].split("MAX, MIN1")[0]
import types
T = types.ModuleType("T"); T.__file__ = os.path.join(HERE, "test_asm.py"); exec(compile(_src, "test_asm_head", "exec"), T.__dict__)

fails = 0
def agree(name, src):
    global fails
    want = T.interp(src)
    try: got = T.run_asm(T.asm_of(src))
    except Exception as e: got = ("err", repr(e)[:200])
    if got == want: print("ok ", name)
    else: fails += 1; print("NG ", name, "\n    asm   ", got, "\n    interp", want)

def refused(name, src):
    global fails
    try: T.asm_of(src); fails += 1; print("NG ", name, "(断られなかった)")
    except T.sign_asm.AsmError as e: print("ok ", name, "→ 断る")

AR = [(1, 2), (0, 1), (5, -3), (0, 0), (7, 0), (-9, 4), (9223372036854775807, 1), (4611686018427387904, 1), (1, 4611686018427387904)]
GE = [(3, 2), (3, -2), (1, 0), (0, 5), (5, 1), (5, -1), (1, 3), (-1, 3), (2, 2), (-7, -1), (1, 4611686018427387904), (3037000499, 3037000499)]
IDX = [0, 1, 2, 3, 5, 31, 62, 63, 64, 100, 1000, -1, -5, 1000000000000000000]
rnd = random.Random(5)
def lit(v): return "(0 - %d)" % -v if v < 0 else str(v)
for a, s in AR:
    for i in rnd.sample(IDX, 6):
        agree("等差 [%d ~+ %d] ' %d" % (a, s, i), "([%s ~+ %s]) ' %s\n" % (lit(a), lit(s), lit(i)))
for a, k in GE:
    for i in IDX:
        agree("等比 [%d ~* %d] ' %d" % (a, k, i), "([%s ~* %s]) ' %s\n" % (lit(a), lit(k), lit(i)))
# 名前・仮引数・名前の定義
agree("名前の定義(等差)", "b : [1 ~+ 2]\nb ' 5\n")
agree("名前の定義(等比)", "g : [3 ~* 2]\ng ' 4\n")
agree("名前の定義(等比・溢れ)", "g : [3 ~* 2]\ng ' 62\n")
agree("仮引数に等差", "f : r n ? r ' n\nf [1 ~+ 2] 6\n")
agree("仮引数に等比", "f : r n ? r ' n\nf [1 ~* -1] 7\n")
agree("仮引数に有限の規則(混ざる)", "f : r n ? r ' n\n(f [1 ~+ 2 ~ 9] 3) + (f [1 ~* 3] 3)\n")
agree("名前を渡す", "g : [3 ~* 2]\nf : r n ? r ' n\nf g 5\n")
agree("返す関数", "mk : a ? [a ~* 2]\n(mk 5) ' 3\n")
agree("led の閉じた式の代わり", "s : [1 ~* -1]\nf : n ? s ' n\nf 7\n")
# 取り出し以外は罠(数えられない)
for n, src in [("個数", "g : [3 ~* 2]\n||g||\n"), ("個数(等差)", "b : [1 ~+ 2]\n||b||\n")]:
    r = T.run_asm(T.asm_of(src))
    if r[0] == "trap": print("ok ", n, "→ 罠")
    else: fails += 1; print("NG ", n, r)
print("%d 件 NG" % fails if fails else "全部 ok"); sys.exit(1 if fails else 0)
