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
for src_, defs_, want_ in [("(q 1) ' g 4", ["inc : x ? x + 1", "q : x ? [g : inc]"], "(construct (' [q 1] g) 4)")]:
    g_ = T.tree_of(src_, P + defs_)
    if g_ != want_: bad += 1; print("NG", src_, g_, want_)     # 呼んだ答えを欄の名前で引いた物は種類が未知で値を受けない(R125)
OK += [("io@\n$say + 1", "(+ $say 1)"), ("io@\n$say == 1", "(== $say 1)"), ("io@\nx : $say\nx + 1", "(+ x 1)")]     # 取り込み宣言の行は木に出ず、取り込んだ名前は未定義の名前と同じ読み(R99)
OK += [("tk : f ? $@f + 1", "(: tk (? [f] (+ $@f 1)))"), ("tw : f ? $f", "(: tw (? [f] $f))")]     # 裸の仮引数の持ち上げは値の葉のまま(R99・R100)
for src_, defs_, want_ in [("(fs ' [0 ~ 0]) # 5", ["fs : $inc , $double , 3"], "(# [fs ' [0 ~ 0]] 5)")]:
    g_ = T.tree_of(src_, P + defs_)
    if g_ != want_: bad += 1; print("NG", src_, g_, want_)     # 器の位置の切り出しは値で、`#` の左の書く場所(R62)
OK += [("@($inc ' -1) 5", "(apply @[$inc ' -1] 5)")]     # 関数の番地を負の鍵で引いた括りは値で、`@` が開く(R102)
OK += [("inc [w w] 5", "(apply inc 5)"), ("[w 5]", "[w 5]")]     # 括りの中の `!_` と分かる要素は単位として消え、全部なら `!_` と分かる括り(R137)
OK += [("[add,] vs", "(construct [add,] vs)")]     # `[F,]` で F の口が 2 つ以上は未知の葉(R50)
OK += [("(inc double) inc 5", "(apply (compose [inc double] inc) 5)")]     # 関数だけの括りは合成した 1 つの関数で、開かない(R8)
OK += [("inc i [* 2,] 1 2", "(apply [* 2,] (apply i (construct (apply inc 1) 2)))")]     # 合成の中の恒等射は並びを全部流す(R74)
OK += [("||_|| 1 2 inc", "(apply inc (apply ||_|| (construct 1 2)))"), ("|_| (0 - 5) inc", "(apply inc (apply |_| [0 - 5]))")]     # 囲みの中の関数の後ろの関数は結果を受ける(R27)
OK += [("g [width : 640]", "(apply g [width : 640])")]     # 欄を書いた構造体は値の葉(R49・R128)
for src_, defs_, want_ in [("h [s : $inc]", ["h : f ? @f 5"], "(apply h [s : $inc])")]:
    g_ = T.tree_of(src_, P + defs_)
    if g_ != want_: bad += 1; print("NG", src_, g_, want_)     # 欄を書いた構造体は値の葉で、関数が受ける(R49)
OK += [("0 <= 3 < 5", "(< (<= 0 3) 5)"), ("1 < 2 < 3", "(< (< 1 2) 3)")]     # 大小の比較の連なりは演算子が違っても左へ入れ子(R119)
OK += [("w , _", "(unit _)"), ("v : 1 , $v", "(: v 1)"), ("w , 5", "5")]     # `!_` と分かる辺は `,` で消える(R61・R103・R137)
OK += [("pb : [x] ? x + 1", "(: pb (? [[x]] (defer {x + 1})))"), ("hh : [x] ? zz", "(: hh (? [[x]] (defer {zz})))")]     # 括りの仮引数の関数の本体は呼ばなければ defer(R25)
OK += [("h : f x ? @f x inc", "(: h (? [f x] (construct (apply @f x) (unit inc))))")]     # 前置 `@` で開いた仮引数の後ろの関数は結果を受けない(R136)
for src_, defs_, want_ in [("p ' a 5", ["p : [a : inc]"], "(apply (' p a) 5)"), ("p ' a", ["p : [a : inc]"], "(' p a)")]:
    g_ = T.tree_of(src_, P + defs_)
    if g_ != want_: bad += 1; print("NG", src_, g_, want_)     # 構造体の欄の関数は引いた物が口を持つ関数(R26)
for src_, defs_, want_ in [("z 1 2", ["z : @$inc"], "(construct z 1 2)")]:
    g_ = T.tree_of(src_, P + defs_)
    if g_ != want_: bad += 1; print("NG", src_, g_, want_)     # 番地を開いた物をしまう名前は種類が未知(R120)
for src_, defs_, want_ in [("s 5", ["s : [+ inc]"], "(apply s 5)")]:
    g_ = T.tree_of(src_, P + defs_)
    if g_ != want_: bad += 1; print("NG", src_, g_, want_)     # 点なしの括りをしまう名前は、その口の関数(R87)
for src_, defs_, want_ in [("v 5", ["v : [* 2,] w"], "(apply v 5)")]:
    g_ = T.tree_of(src_, P + defs_)
    if g_ != want_: bad += 1; print("NG", src_, g_, want_)     # 点なしの可変長の括りが残った名前は、並びを受ける関数(R95)
OK += [("[+] inc w~", "(apply (compose [+] inc) w~)")]     # 撒いた流れを受ける合成(R95・R84)
OK += [("1 & (i w)", "(& 1 (unit [i w]))")]     # 恒等射が `!_` と分かる値だけ受けた括りは恒等射が残る(R95・R48)
NONE = ["gd 3 4 7", "inc ~1 5", "@[$[x ? x]] 1 2", "inc _ 2", "add 1 inc"]
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
