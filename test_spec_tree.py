"""spec_tree.py の木の出力の確認。仕様 §1.3 の見本のうち、出す形が仕様と一字違わないことと、読まない形は None(誤った木を出さない)ことを見る。"""
import spec_tree as T, spec_audit as A
P = A.PRE.splitlines()
OK = [("inc 3 4", "(construct (apply inc 3) 4)"), ("d 1 2", "(construct (apply d 1) 2)"), ("inc i inc 5", "(apply (compose inc i inc) 5)"),
      ("inc # 5", "(# (unit inc) 5)"), ("nosuchname 5", "5"), ("inc typo 5", "(apply inc 5)"), ("inc (5 ' 1) 5", "(apply inc 5)"), ("inc (0x10 ' 1) 5", "(construct (apply inc [0x10 ' 1]) 5)"), ("[+ 1] 1 2 3", "(construct (apply [+ 1] 1) 2 3)"), ("inc add 5", "(unit (apply (compose inc add) 5))"), ("add 1 2", "(apply add (construct 1 2))"), ("$inc + 0x80", "(+ $inc 0x80)")]
OK += [("inc add 5 g 3", "(apply g (apply add (construct (apply inc 5) 3)))"), ("[+] 1 2 inc 3", "(apply inc (apply [+] (construct 1 2 3)))"),     # 合成の連なり: 左から順に値を受け、前の結果を次へ(R11・R41)
       ("inc [+] 5 6", "(apply [+] (construct (apply inc 5) 6))"), ("f2 3 f2 5 6", "(apply f2 (construct (apply f2 (construct 3 5)) 6))"), ("[+] 5 g 3", "(apply g (apply [+] (construct 5 3)))")]
OK += [("i 1 2 3", "(apply i (construct 1 2 3))"), ("i inc 1 2", "(construct (apply inc 1) 2)"), ("i 5 inc", "(construct 5 (unit inc))")]     # 恒等射が頭: 関数が続けば単位律で消え、続かなければ並び全体を受ける(R29・R74)
OK += [("$[inc 5] + 1", "(+ $[inc 5] 1)"), ("$($inc + 1) + 2", "(+ $[$inc + 1] 2)"), ("$[1 +] == $inc", "(== $[1 +] $inc)"), ("$_ , $inc", "(, $_ $inc)"),     # 式の番地・恒等射の番地は値(R62・R101)
       ("@[$_] 1 2", "(apply @[$_] (construct 1 2))"), ("@[$_] inc 1 2", "(construct (apply inc 1) 2)")]
OK += [("fs : $inc , $double , 3", "(: fs (, $inc (, $double 3)))"), ("x : 1 , 2", "(: x (, 1 2))")]          # 右辺が `,` の連なりの値の定義
bad = 0
OK += [("[add] _ 2", "(unit (? [$p0] (apply [add] (construct $p0 2))))")]
for src_, defs_, want_ in [("p _ 2", ["p : add"], "(unit (? [$p0] (apply p (construct $p0 2))))"), ("q _ 2", ["q : f3 1"], "(unit (? [$p0] (apply q (construct $p0 2))))"), ("q 5 6", ["q : f3 1"], "(apply q (construct 5 6))")]:
    g_ = T.tree_of(src_, P + defs_)                                        # 別名・部分適用の名前は、残りの口の素の関数(R16)
    if g_ != want_: bad += 1; print("NG", src_, defs_, g_, want_)
OK += [("inc ([1 2] ' 5) 5", "(apply inc 5)"), ("inc (5 ' [1 ~ 3]) 5", "(apply inc 5)"), ("inc ([1 2] ' 1) 5", None)]     # 字面のデータを字面の鍵で引いて領域の外なら `!_`(R26・R112)
OK += [("inc (vs ' _) 5", "(apply inc 5)"), ("inc (b @ pw) 5", "(apply inc 5)")]     # 名前の鍵で引いて無ければ `!_`(R64・R115)
OK += [("[+ inc] 5", "(apply [+ inc] 5)"), ("[+ i] 5", "(apply [+ i] 5)"), ("[< _] 5", "(apply [< _] 5)")]     # 点なしの括りの片側が関数・恒等射(R87・R29・R48)
OK += [("[inc,] 1 2 3", "(apply [inc,] (construct 1 2 3))")]     # `[F,]` は口 1 つの F の写像(R50)
OK += [("~1 2 3", "(construct ~1 2 3)"), ("-_ 5", "(construct -_ 5)"), ("!inc 5", "(construct !inc 5)")]     # 値の印・前置 `~` の葉(R87・R77)
for src_, defs_, want_ in [("f -x", ["f : a ? a", "x : 3"], "(apply f -x)")]:
    g_ = T.tree_of(src_, P + defs_)
    if g_ != want_: bad += 1; print("NG", src_, g_, want_)     # 値の名前に前置 `-` は値(R2)
OK += [("[!_] 1 2 3 4 5", "(apply [!_] (construct 1 2 3 4 5))")]     # 前置・後置の点なしの席は口が並び全体(R35・R138)
OK += [("(5 inc) 3", "(construct [5 inc] 3)"), ("(3 | inc) 5", "(construct [3 | inc] 5)")]     # 字面の数に続く関数は余る(R52・R136)
OK += [("gd 3 (3 < 2) 7", "(apply gd (construct 3 [3 < 2] 7))")]     # 既定値のある関数に口より多く、`!_` でありうる括りを混ぜて渡す(R83)
OK += [("[* 2,] w", "(unit [* 2,])"), ("[* 2,] 1 2 3", "(apply [* 2,] (construct 1 2 3))")]     # 点なしの可変長の口が `!_` だけ受ければ関数が残る(R95)
NONE = ["gd 3 4 7", "inc ~1 5", "[add,] vs", "v : 1 , $v", "@[$[x ? x]] 1 2", "inc _ 2", "add 1 inc", "inc i [* 2,] 1 2"]
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
if out[:3] != ["1: (: inc (? [x] (+ x 1)))", "2: (construct (apply inc 3) 4)", "3: (construct 1 2)"]: bad += 1; print("NG --tree", out)
print("全部 ok" if not bad else f"{bad} 件 NG"); raise SystemExit(1 if bad else 0)
