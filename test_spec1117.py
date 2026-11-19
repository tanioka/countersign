"""2026-11-17 の仕様(coproduct_spec 5996606f・value_spec d5718639)の、恒等射を `,`・`|`・`;` の関数の因子として読む規則の見本。--strict(仕様の読み)で値と知らせを確かめる"""
import sys, os, importlib.util
sys.setrecursionlimit(20000)
spec = importlib.util.spec_from_file_location("S", os.path.join(os.path.dirname(os.path.abspath(__file__)), "sign_interp.py"))
S = importlib.util.module_from_spec(spec); spec.loader.exec_module(S)
D = "inc : x ? x + 1\ndouble : x ? x * 2\ni : _\nw : 3 < 2\n"
def go(src):
    S.STRICT_GATES = True
    S.WARNINGS.clear()
    try: S.WARN_LINES.clear()
    except Exception: pass
    n0 = 0
    try: r = S.run(D + src); out = S.show(r[-1]) if r else ""
    except BaseException as e: out = "ERR " + str(e).split("\n")[0][:60]
    return out, [k[0] for k in S.WARNINGS[n0:]] if hasattr(S, "WARNINGS") else []
CASES = [   # (源, 値, 知らせに入る名前の集合(None なら見ない))
    ("(i i , inc) 5", "5", {"leftover-lambda"}), ("(inc , _) 5", "5", {"leftover-lambda"}), ("(_ , inc) 5", "5", {"leftover-lambda"}),
    ("(@[$_] , inc) 5", "5", {"leftover-lambda"}), ("(_ , _) 5", "5", set()), ("_ , 5", "5", set()), ("i i , 5", "5", set()),
    ("1 , _ , 2", "[1, 2]", set()), ("_ , _ ; 7", "7", set()), ("w , _", "!_", set()), ("i , i", "!_", set()),
    ("(_ | inc) 5", "5", None), ("(inc | _) 5", "5", None), ("(_ ; inc) 5", "5", None), ("(_ | _) 5", "5", None),
    ("(_ | 3) 5", "[3, 5]", None), ("(_ | (3 < 2)) 5", "5", None), ("7 ; i", "7", None), ("_ | 5", "5", None), ("5 ; _", "5", None),
    ("inc _ 5", "6", None), ("x : w , i i\nx 5", "5", None),
    ("$[inc , _]", "!_", {"dollar-non-function", "leftover-lambda"}), ("$[_ , _]", "!_", {"dollar-non-function"}), ("$_ , $inc", "[$_, $inc]", set()), ("$[i , inc]", "!_", {"dollar-non-function", "leftover-lambda"}),
    ("$[inc , double]", "!_", {"dollar-non-function", "leftover-lambda"}),
    # 2026-11-17 例の網羅照合(spec_audit.py)で直した形
    ("(3 | inc) 5", "[3, 5]", {"leftover-lambda"}), ("1 & (i w)", "!_", {"leftover-lambda"}), ("fp : [a b c] ? a\n\nfp i , 1 , 2", "[1, 2]", {"leftover-lambda"}),
    ("inc + $inc", "!_", {"leftover-lambda", "level-mismatch"}), ("[<] ($inc + 1) 3", "!_", {"level-mismatch"}), ("[<<] 1 4 2", "64", {"pointfree-not-folded"}),
    ("v : [* 2,] w\n\nv 5", "[10]", set()), ("gq :\n\t\tx\n\t\ty : 1\n\t? x + y\n\n(gq 1 , w) 5", "6", set()),
    ("tk : f ? $[@f , 1]", "<fn/1>", {"dollar-non-function"}), ("g2 : [a] ? (inc , a) 5\n\ng2 (3 < 2)", "!_", {"leftover-lambda"}),
    ("fq : [a ~r] ? $a == $a\n\nfq (3 < 2)", "!_", {"dollar-non-function"}), ("pw : [a : 1]\n\nw2 : pw ' zz\n\nfq : [a ~r] ? $a == $a\n\nfq w2", "!_", set()),
    ("(inc , double , double) 5", "5", {"leftover-lambda"}), ("(inc , (double , double)) 5", "6", None), ("((inc , double) , double) 5", "10", None),   # V4 の 3(V12 の「3つ以上は止める」は 21:30 版で消えた)
    ("lz : n ? (n < 1 & 9) | inc , lz (n - 1)\n\n(inc , lz 3) 5", "[9, 5]", None),   # 呼んだ答えが値なら `(inc , 3) 5` と同じ `3 5`
    ("say 5", "5", {"name-undefined"}), ("inc typo 5", "6", {"name-undefined"}), ("q : typo\n\nq 5", "5", {"name-undefined"}),       # R21(2026-11-18 版): 未定義の名前は `!_` と分かる値で、warning で知らせる(断らない)
    ("hh : [x] ? zz\n\n1", "1", {"name-undefined"}), ("f : x ?\n\tx > 0 : 1\n\ttypo\n\nf 0", "!_", {"name-undefined"}),
    ("f : x ?\n\ti : 7\n\tx\n\nf 3", "3", {"leftover-lambda"}),                                                                   # 条件に残った恒等射は G22 でなく次の枝へ(R128)
    ("add : a b ? a + b\n\nlq : n ? (n < 1 & 9) | (inc , double , (add 1 , lq (n - 1)))\n\nlq 5000", "9", None),   # value_spec V10: 前の関数が2つ以上の `,` の鎖は呼びが返す所(末尾呼び出し)
    ("lr2 : n ? (n < 1 & 9) | inc , double , double , lr2 (n - 1)\n\nlr2 5000", "9", None),
    ("f : x ? f x\n\ng : x ? g x\n\n$f == $g", "$f", set()), ("h : x ? h (h x)\n\nh2 : x ? h2 (h2 x)\n\n$h == $h2", "$h", set()),
]
bad = 0
for src, want, warns in CASES:
    out, w = go(src)
    ok = out == want and (warns is None or set(w) >= warns and (set(w) - warns <= {"name-shadow"}))
    if not ok: bad += 1; print("NG", repr(src), "値", out, "のはず", want, "知らせ", w)

REFUSE = [   # (源, 断りの名前)
    ("f : x ?\n\tx > 0 : typo\n\t7\n\n1", "G22"), ("pr : x ?\n\ty : x + 1\n\ty * 2\n\npr 3", "G22"), ("cfg : [width : 640]\n\nf : x ?\n\tx > 0 : cfg ' hieght\n\t7\n\n1", "G22"),   # R128: 枝の条件か値が `!_` と分かる値(未定義の名前も)は呼ばない定義でも G22
    ("g :\n\t\tx\n\t\ty : typo\n\t? x + y\n\n1", "G22"),
    ("vs : 1 2 3\nvs ' 0 @ vs", "infix-mixed-assoc"), ("vs : 1 2 3\n(0 @ vs) ' 0", "infix-mixed-assoc"),
    ("1 ! 2", "operator-unknown"), ("inc $", "operator-unknown"), ("1 === 1", "operator-removed"),
    ("[<<] _ 2", "G7"), ("fp : [a b c] ? a\n\nfp 1 _", "G5"), ("f9 : x ? @[$v]\n\nv : f9 1\n\nv", "name-cycle"), ("f3 : a b c ? a + b + c\n\ng : [~t] ? f3 t~\n\nw : 3 < 2\n\ng (3 < 2)", "G19"), ("inc : x ? x + 1\n\nf2 : x y ? x - y\n\n$[[x] ? f2 (5 inc) 1]", "G20"), ("f : x ?\n\t\ty : 1\n\t? x + y\n", "param-block-position"),
    ("f : x ?\n\tx + 1\nf 3", "definition-end-blank-line"), ("n : 1 +\n\t2\nn", "definition-end-blank-line"),
]
OKS = [("vs : [1 2]\nvs ' 0 ' 1", None), ("f : x ?\n\tx + 1\n\nf 3", "4"), ("f : x ?\n\tx + 1\n`c`\n\nf 3", "4"), ("p : [\n\t1\n\t2\n]\np", "[1, 2]")]
for src, name in REFUSE:
    S.STRICT_GATES = True
    try: S.run(src); got = "(通った)"
    except BaseException as e: got = str(e)
    if not got.startswith(name): bad += 1; print("NG", repr(src), "断り", name, "のはずが", got[:60])
for src, want in OKS:
    out, _w = go(src)
    if want is not None and out != want: bad += 1; print("NG", repr(src), out, "のはず", want)
    if want is None and out.startswith("ERR"): bad += 1; print("NG", repr(src), out)
ROWS = [   # List の行に1つだけ残った裸の関数(仮引数を使わず1つの関数に決まれば関数のまま返る。知らせ無し)
    ("q : x ? [\n\tinc\n\tx\n]\n\n((q 1) ' 0) 5", "6", set()),
    ("fs3 : [\n\tinc\n\t3\n]\n\nq : x ? fs3\n\n((q 1) ' 0) 5", "6", set()),
    ("q : x ? [\n\tinc\n\t[+ x]\n]\n\n((q 1) ' 0) 5", "6", {"bare-function-return"}),
    ("fs3 : [\n\tinc\n\t3\n]\n\nq : x ? fs3 ' 0\n\nq 1", "!_", {"bare-function-return"}),
]
for src, want, warns in ROWS:
    out, w = go(src)
    if out != want or set(w) != warns: bad += 1; print("NG", repr(src), out, w, "のはず", want, warns)
FS = "fs3 : [\n\tinc\n\t3\n]\n\nfd : [\n\tdouble\n\t3\n]\n\n"
S.STRICT_GATES = True; S.WARNINGS.clear(); S.run(D + FS + "q : x ?\n\tx > 0 : fs3\n\tfd\n\nq 1")
_n = sum(1 for k in S.WARNINGS if k[0] == "bare-function-return")
if _n != 2: bad += 1; print("NG 枝で違う List の行: bare-function-return は枝の行ごとに1つ(2つ)のはずが", _n)
out, w = go(FS + "q : x ?\n\tx > 0 : fs3\n\tfs3\n\n((q 1) ' 0) 5")
if out != "6" or w: bad += 1; print("NG 同じ木の枝は知らせ無しで 6 のはずが", out, w)
IDADDR = [("$i", "$_"), ("$[i]", "$_"), ("$[_]", "$_"), ("$$i", "$_"), ("$_ == $i", "$_"), ("@[$i] 1 2", "[1, 2]"), ("@[$[i]] 1 2", "[1, 2]"), ("@[$_] 1 2", "[1, 2]"), ("q : $i\n@q 1 2", "[1, 2]")]
for src, want in IDADDR:
    out, w = go(src)
    if out != want or "dollar-non-function" in w: bad += 1; print("NG 恒等射の番地", repr(src), out, w, "のはず", want)
print("全部 ok" if not bad else f"{bad} 件 NG")
sys.exit(1 if bad else 0)
