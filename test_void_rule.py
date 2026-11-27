"""test_void_rule.py — `!_` の規則(質問書 12): 規則の端点・歩幅が溢れで `!_` になると、規則全体が `!_`(operator_table: `~` は両辺の `!_` が零射)。
機械語は起点が niche の 3 つ組 {niche, 0, 0} で運び、数える(0 個)・取り出す(`!_`)。処理系の --strict(仕様の読み)と答えを突き合わせる。"""
import sys, subprocess, os
exec(open("test_inline.py", encoding="utf-8").read().split("SAME = [")[0])

def strict(src):
    d = os.path.join(os.environ.get("TMPDIR", "/tmp"), "t_void_rule.sn"); open(d, "w", encoding="utf-8").write(src)
    r = subprocess.run([sys.executable, "sign_interp.py", "--check-int", d], capture_output=True, text=True)
    return r.stdout.strip().splitlines()[-1] if r.stdout.strip() else ""

B = "4611686018427387904"
CASES = [
 ("端点が溢れ: 個数 0", "f : n ? ||[1 ~ (n * %s)]||\nf 4\n" % B),
 ("端点が溢れない: 個数(処理系は大きい範囲を数えない)", "f : n ? ||[1 ~ (n * %s)]||\nf 1\n" % B, B),
 ("歩幅つき・端点が溢れ", "f : n ? ||[1 ~+ 1 ~ (n * %s)]||\nf 4\n" % B),
 ("始まりが溢れ", "f : n ? ||[(n * %s) ~ 5]||\nf 4\n" % B),
 ("歩幅が溢れ", "f : n ? ||[1 ~+ (n * %s) ~ 5]||\nf 4\n" % B),
 ("取り出し: `!_` の規則は `!_`(右へ落ちる)", "f : n ? ([1 ~ (n * %s)] ' 0) | 7\nf 4\n" % B),
 ("取り出し: 溢れない(処理系は大きい範囲を作らない)", "f : n ? ([1 ~ (n * %s)] ' 0) | 7\nf 1\n" % B, "1"),
 ("端点が計算の規則の取り出し(添字を壊さない)", "f : n ? [1 ~ (n * 5)] ' 2\nf 2\n"),
 ("端点が計算の規則の取り出し 2", "f : n ? [1 ~ (n * 5)] ' 7\nf 2\n"),
 ("規則を返す関数の引数が溢れ", "g : n ? [1 ~ n]\nf : n ? ||g (n * %s)||\nf 4\n" % B),
 ("終端の無い規則の起点が溢れ", "f : n ? ([(n * %s) ~+ 1] ' 3) | 9\nf 4\n" % B),
 ("終端の無い規則の起点が溢れない", "f : n ? ([(n * %s) ~+ 1] ' 3) | 9\nf 1\n" % B),
]
for name, src, *want in CASES:
    try: a, _ = asm_run(src); a = a.splitlines()[-1] if a else ""
    except sign_asm.AsmError as e: a = "断る: " + str(e)[:80]
    except Exception as e: a = "例外 %s" % type(e).__name__
    w = want[0] if want else strict(src)
    check(name, a == w, "機械語=%r 期待=%r" % (a, w))
print("全部 ok" if not FAIL else "失敗 %d 件: %s" % (len(FAIL), ", ".join(FAIL)))
sys.exit(1 if FAIL else 0)
