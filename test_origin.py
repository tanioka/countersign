"""(2026-11-19 版 coproduct_spec 表の R27 `||i||`・`||(_)||` も同じ道具で見る)
type_system.md §6.2 `' _`(コンストラクタ由来の確認): --strict は、右辺を静的に遡れるとき `$Constructor`、遡れなければ `!_`。
値を見るため、strict でも最後の値を出す写しを一時フォルダに作って走らせる。"""
import os, subprocess, sys, tempfile, shutil
HERE = os.path.dirname(os.path.abspath(__file__))
d = tempfile.mkdtemp()
src = open(os.path.join(HERE, "sign_interp.py"), encoding="utf-8").read().replace("if res and not STRICT_GATES: print(show(res[-1]))", "if res: print(show(res[-1]))")
open(os.path.join(d, "sign_interp.py"), "w", encoding="utf-8").write(src)
for n in ("std.sn", "sign_st.py"):
    if os.path.exists(os.path.join(HERE, n)): shutil.copy(os.path.join(HERE, n), d)
HEAD = "#Point : a b ? [\n\tx : a\n\ty : b\n]\nVector2D : a b ? [\n\tx : a\n\ty : b\n\tz : 0\n]\np : Point 1 2\nv : Vector2D 1 2\nq : p\nr : [\n\tx : 1\n\ty : 2\n]\n"
CASES0 = [   # (名前, 最後の式, 期待する最後の行)
    ("遡れる(Point 経由)", "p ' _", "$Point"),
    ("`==` で $Point と等しい", "(p ' _) == $Point", "$Point"),
    ("別のコンストラクタ由来どうしは等しくない", "(p ' _) == (v ' _)", "!_"),
    ("名前の写し(q : p)も遡れる", "q ' _", "$Point"),
    ("裸の括りは遡るものが無い", "r ' _", "!_"),
    ("`==` は構造比較で由来を見ない", "p == v", "!_"),   # v は欄 z を持つので形が違う
]
CASES = CASES0
bad = 0
R27 = [("`||i||` は囲みごと !_(5 が残る)", "i : _\n||i|| 5", "5"), ("`||(_)||` も同じ", "i : _\n||(_)|| 5", "5"), ("`||_||` は口の穴(並び全体を数える)", "||_|| 3 4", "2")]
for name, body, want in R27:
    f = os.path.join(d, "m.sn"); open(f, "w", encoding="utf-8").write(body + "\n")
    r = subprocess.run([sys.executable, os.path.join(d, "sign_interp.py"), "--strict", f], capture_output=True, text=True, cwd=d)
    got = (r.stdout.strip().splitlines() or [""])[0]
    if got != want: bad += 1; print("NG", name, "got", repr(got), "want", repr(want))
for name, last, want in CASES:
    f = os.path.join(d, "m.sn"); open(f, "w", encoding="utf-8").write(HEAD + last + "\n")
    r = subprocess.run([sys.executable, os.path.join(d, "sign_interp.py"), "--strict", f], capture_output=True, text=True, cwd=d)
    got = (r.stdout.strip().splitlines() or [""])[-1]
    if got != want: bad += 1; print("NG", name, "got", repr(got), "want", repr(want), r.stderr[:100])
print("全部 ok" if not bad else "NG %d 件" % bad); sys.exit(1 if bad else 0)
