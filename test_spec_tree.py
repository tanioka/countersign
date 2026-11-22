"""spec_tree.py の木の出力の確認。仕様 §1.3 の見本のうち、出す形が仕様と一字違わないことと、読まない形は None(誤った木を出さない)ことを見る。"""
import spec_tree as T, spec_audit as A
P = A.PRE.splitlines()
OK = [("inc 3 4", "(construct (apply inc 3) 4)"), ("d 1 2", "(construct (apply d 1) 2)"), ("inc i inc 5", "(apply (compose inc i inc) 5)"),
      ("inc # 5", "(# (unit inc) 5)"), ("[+ 1] 1 2 3", "(construct (apply [+ 1] 1) 2 3)"), ("inc add 5", "(unit (apply (compose inc add) 5))"), ("add 1 2", "(apply add (construct 1 2))"), ("$inc + 0x80", "(+ $inc 0x80)")]
NONE = ["inc _ 2", "i 1 2 3", "inc (5 ' 1) 5", "nosuchname 5"]
bad = 0
for s, t in OK:
    g = T.tree_of(s, P)
    if g != t: bad += 1; print("NG", s, g, t)
for s in NONE:
    g = T.tree_of(s, P)
    if g is not None: bad += 1; print("NG(未対応のはず)", s, g)
print("全部 ok" if not bad else f"{bad} 件 NG"); raise SystemExit(1 if bad else 0)
