"""spec_tree.py の木の出力の確認。仕様 §1.3 の見本のうち、出す形が仕様と一字違わないことと、読まない形は None(誤った木を出さない)ことを見る。"""
import spec_tree as T, spec_audit as A
P = A.PRE.splitlines()
OK = [("inc 3 4", "(construct (apply inc 3) 4)"), ("d 1 2", "(construct (apply d 1) 2)"), ("inc i inc 5", "(apply (compose inc i inc) 5)"),
      ("inc # 5", "(# (unit inc) 5)"), ("inc (5 ' 1) 5", "(apply inc 5)"), ("inc (0x10 ' 1) 5", "(construct (apply inc [0x10 ' 1]) 5)"), ("[+ 1] 1 2 3", "(construct (apply [+ 1] 1) 2 3)"), ("inc add 5", "(unit (apply (compose inc add) 5))"), ("add 1 2", "(apply add (construct 1 2))"), ("$inc + 0x80", "(+ $inc 0x80)")]
NONE = ["inc _ 2", "i 1 2 3", "nosuchname 5"]
bad = 0
for s, t in OK:
    g = T.tree_of(s, P)
    if g != t: bad += 1; print("NG", s, g, t)
for s in NONE:
    g = T.tree_of(s, P)
    if g is not None: bad += 1; print("NG(未対応のはず)", s, g)
import subprocess, sys, tempfile, os
with tempfile.NamedTemporaryFile("w", suffix=".sn", delete=False, encoding="utf-8") as f: f.write("inc : x ? x + 1\ninc 3 4\nzz 1 2\n"); fn = f.name
out = subprocess.run([sys.executable, os.path.join(os.path.dirname(os.path.abspath(__file__)), "sign.py"), "--tree", fn], capture_output=True, text=True).stdout.split("\n")
os.unlink(fn)
if out[:3] != ["1: (: inc (? [x] (+ x 1)))", "2: (construct (apply inc 3) 4)", "3: 未対応"]: bad += 1; print("NG --tree", out)
print("全部 ok" if not bad else f"{bad} 件 NG"); raise SystemExit(1 if bad else 0)
