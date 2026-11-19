#!/usr/bin/env python3
"""速い道(run_pure)を List と『値か単位』を返す関数に広げた分の試験。速い道あり(既定)と無し(SIGN_NO_PURE=1)で、
同じ入力が同じ出力になることを、端の値(空・短すぎる List・負の添字・単位の実引数など)で確かめる。python test_pure_list.py"""
import os, random, subprocess, sys, tempfile, time
HERE = os.path.dirname(os.path.abspath(__file__))
bad = 0
def check(name, got, want):
    global bad
    ok = got == want; bad += not ok
    print(("ok  " if ok else "NG  ") + name + ("" if ok else f"\n    得た: {got!r}\n    期待: {want!r}"))
TMP = tempfile.mkdtemp()
def run(src, pure, timeout=120):
    p = os.path.join(TMP, "t.sn"); open(p, "w", encoding="utf-8").write(src)
    env = dict(os.environ); env["SIGN_NO_PURE"] = "0" if pure else "1"
    t = time.time()
    try: r = subprocess.run([sys.executable, os.path.join(HERE, "sign.py"), p], capture_output=True, text=True, timeout=timeout, env=env, cwd=HERE)
    except subprocess.TimeoutExpired: return ("timeout",), timeout
    return (r.returncode, r.stdout, r.stderr), time.time() - t
def same(name, src):
    a, _ = run(src, True); b, _ = run(src, False)
    check(name, a, b); return a

# --- 『値か単位』を返す関数 ---
P = "p : x ?\n\tx > 3 : x\n"
for x in (1, 3, 4, 100): same(f"最後の行に条件がある関数 p {x}", P + f"p {x}\n")
same("単位を返す関数を | で受ける", P + "(p 1) | 99\n")
same("単位を返す関数を条件に", P + "q : x ?\n\t(p x) : 1\n\t0\nseq2 (println_int (q 2)) (println_int (q 9))\n")
same("単位を実引数にした呼び出しは殺される", P + "h : a b ?\n\tseq2 (100 # 7) (a + b)\nh (p 1) 5\n")
same("単位を足し算に", P + "h : a ?\n\t(p a) + 1\nh 1\n")
LT = "lt : a b ?\n\ta < b\n"
for a, b in ((0, 5), (1, 5), (7, 5), (3, 3)): same(f"比べの値(witness) lt {a} {b}", LT + f"lt {a} {b}\n")

# --- List: 取り出し・長さ・残り ---
S = "s : rs ?\n\t||rs|| <= 1 : rs ' 0\n\t(rs ' 0) + (s (rs ' 1~))\n"
for l in ("[5]", "[1 2 3 4 5]", "[9 8]"): same(f"List の和 s {l}", S + f"s {l}\n")
same("空の List", S + "s []\n")
same("要素が整数でない List", S + "s [1 2.5 3]\n")
same("文字列の List", S + "s [1 `a` 3]\n")
same("負の添字", "f : rs ?\n\trs ' (0 - 1)\nf [1 2 3]\n")
same("範囲外の添字", "f : rs i ?\n\trs ' i\nseq2 (println_int (f [1 2 3] 2)) (println_int (f [1 2 3] 3))\n")
same("負の添字(変数)", "f : rs i ?\n\trs ' i\nf [1 2 3] (0 - 1)\n")
same("整数に添字", "f : x ?\n\tx ' 0\nf 7\n")
same("残りが空になる", "f : rs ?\n\t(rs ' 3~) | 77\nf [1 2 3]\n")
same("残りが空にならない", "f : rs ?\n\trs ' 1~\nf [1 2 3]\n")
same("||x|| (整数は 1)", "f : x ?\n\t||x||\nseq2 (println_int (f 5)) (println_int (f [1 2 3]))\n")

# --- 括りの仮引数 ---
D = "pr : [a b c] ? a + (b * 10) + (c * 100)\n"
for l in ("[1 2 3]", "[1 2]", "[1 2 3 4]", "7", "[]"): same(f"括りの仮引数 pr {l}", D + f"pr {l}\n")
same("括りを経由する呼び出し", D + "g : l ? (pr l) + 1\ng [4 5 6]\n")
same("括りの値で作る List", "mk : [a b] ? [(a + 1) (b + 1) a]\nmk [10 20]\n")
same("List を返す関数の結果を取り出し", "mk : [a b] ? [(a + 1) (b + 1) a]\nf : x ? (mk [x 5]) ' 1\nf 3\n")

# --- メモリの List ---
M = "R : 0x4000\nput : i v ? (R + (i * 4)) # v\nget : i ? @(R + (i * 4))\n"
same("List を書いて読む", M + "seq3 (put 0 [1 2 3]) (put 1 [4 5 6]) (((get 0) ' 1) + ((get 1) ' 2))\n")
same("未書き込みを読む", M + "f : i ? ((get i) ' 0) + 1\nf 5\n")
same("List を整数として使う", M + "seq2 (put 0 [1 2 3]) ((get 0) + 1)\n")
same("整数を List として使う", M + "seq2 (put 0 5) ((get 0) ' 0)\n")
same("書いたあと外れる: 取り消されて二重にならない", M + "f : i ?\n\tseq3 (put i [i i]) (put (i + 1) [7 8]) (((get (i + 2)) ' 0) + 1)\nseq2 (f 3) (println_int ((get 3) ' 0))\n")
same("List の書き込みを繰り返す", M + "fill : i n ?\n\ti >= n : 0\n\tseq2 (put i [i (i * i)]) (fill (i + 1) n)\nsum : i n ?\n\ti >= n : 0\n\t(((get i) ' 1)) + (sum (i + 1) n)\nseq2 (fill 0 20) (sum 0 20)\n")

# --- List の比べ ---
EQ = "eq : a b ?\n\ta = b : 1\n\t0\n"
for a, b in (("[1 2]", "[1 2]"), ("[1 2]", "[1 3]"), ("[1]", "1"), ("1", "[1]"), ("[1 2]", "5"), ("[1 2]", "[1 2 3]")): same(f"List の比べ eq {a} {b}", EQ + f"eq {a} {b}\n")
same("List の大小", "lt : a b ?\n\ta < b : 1\n\t0\nlt [1 2] [1 3]\n")

# --- 相互再帰・自分への再帰の中の List ---
same("List を回す再帰", "pt : [x y] ?\n\tx + y\nwalk : rs acc ?\n\t||rs|| < 2 : acc\n\twalk (rs ' 2~) (acc + (pt [(rs ' 0) (rs ' 1)]))\nwalk [1 2 3 4 5 6] 0\n")
same("関数が List を返す・返さない", "q : n ?\n\tn > 5 : [n n]\n\tn\nf : n ? ((q n) ' 0) + 1\nseq2 (println_int (f 9)) (println_int (f 2))\n")


# --- 括りの仮引数 + 自分への末尾呼び出し(回ごとに括りの名前を更新する) ---
same("括り + 末尾呼び出し", "f : [a b] n ?\n\tn = 0 : a + (b * 100)\n\tf [(a + 1) (b + 2)] (n - 1)\nf [1 1] 5\n")
same("括り + 末尾呼び出し(局所の定義つき)", "f : [a b] n ?\n\tc : a + b\n\td : c * 2\n\tn = 0 : d\n\tf [(a + 1) (b + 2)] (n - 1)\nf [1 1] 4\n")
same("List の引数 + 末尾呼び出し", "g : r i acc ?\n\ti >= ||r|| : acc\n\tg r (i + 1) (acc + (r ' i))\ng [3 4 5 6] 0 0\n")

# --- 足していく List(acc~ …): 輪の中で元の list を書き換える最適化。別の所に渡した list は書き換えない ---
BD = "bd : n acc ?\n\tn = 0 : acc\n\tbd (n - 1) (acc~ n)\n"
same("acc~ の基本", BD + "bd 6 [0]\n")
same("acc~ 呼び側の list は変わらない", BD + "xs : [7 8]\nseq3 (println_int (||bd 5 xs||)) (println_int (||xs||)) (xs ' 1)\n")
same("acc~ 同じ list を 2 回渡す", BD + "xs : [7 8]\nseq2 (println_int ((bd 3 xs) ' 4)) (println_int ((bd 4 xs) ' 5))\n")
same("acc~ 複数の項", "bm : n acc ?\n\tn <= 0 : acc\n\tbm (n - 1) (acc~ n (n * 2))\nbm 3 [0]\n")
same("acc~ 条件で長さを読む", "br : n acc ?\n\t||acc|| > 4 : acc\n\tbr (n - 1) (acc~ n)\nbr 9 [0]\n")
same("acc~ 条件で添字を読む", "br : n acc ?\n\t(acc ' 0) > 100 : acc\n\tn = 0 : acc\n\tbr (n - 1) (acc~ ((acc ' 0) + n))\nbr 5 [1]\n")
same("acc を別の関数へ渡す(書き換えない道)", "ln : l ? ||l||\nbd : n acc ?\n\tn = 0 : acc\n\tbd (n - 1) (acc~ (ln acc))\nbd 5 [9]\n")
same("acc をメモリへ置いてから足す(置いた list は変わらない)", "R : 0x5000\nbd : n acc ?\n\tn = 0 : acc\n\tseq2 ((R + (n * 4)) # acc) (bd (n - 1) (acc~ n))\nseq2 (bd 4 [9]) ((@(R + 12)) ' 0)\n")
same("acc をメモリへ置く(置いた list の長さ)", "R : 0x5000\nbd : n acc ?\n\tn = 0 : acc\n\tseq2 ((R + (n * 4)) # acc) (bd (n - 1) (acc~ n))\nseq3 (bd 4 [9]) (println_int ||(@(R + 4))||) (println_int ||(@(R + 16))||)\n")
same("acc を途中で別の値にする", "bd : n acc ?\n\tn = 0 : acc\n\tn = 3 : bd 2 [100]\n\tbd (n - 1) (acc~ n)\nbd 5 [0]\n")
same("acc が 2 つ", "bd : n a b ?\n\tn = 0 : (||a||) + (||b||) * 100\n\tbd (n - 1) (a~ n) (b~ (n * 2))\nbd 4 [0] [0]\n")
same("acc に整数を足したあと List を足す", BD + "bd 3 [1 2] \n")
same("acc が 1 つの整数のとき", BD + "bd 3 5\n")
same("足す値が単位", "bd : n acc ?\n\tn = 0 : acc\n\tbd (n - 1) (acc~ (n > 2))\nbd 4 [0]\n")
same("足す値が小数", "bd : n acc ?\n\tn = 0 : acc\n\tbd (n - 1) (acc~ 1.5)\nbd 3 [1]\n")
same("map(添字で回して足す)", BD + "mp : xs i acc ?\n\ti >= ||xs|| : acc\n\tmp xs (i + 1) (acc~ ((xs ' i) * 2))\nmp (bd 9 [0]) 0 [0]\n")
same("filter", BD + "fl : xs i acc ?\n\ti >= ||xs|| : acc\n\t((xs ' i) % 3) = 0 : fl xs (i + 1) (acc~ (xs ' i))\n\tfl xs (i + 1) acc\nfl (bd 20 [0]) 0 [0]\n")
same("2 回走らせて別々の結果", BD + "fl : xs i acc ?\n\ti >= ||xs|| : acc\n\tfl xs (i + 1) (acc~ ((xs ' i) + 1))\nys : bd 6 [0]\nseq2 (println_int (||fl ys 0 [0]||)) (println_int (||fl ys 2 [0]||))\n")

# --- 入れ子の List(整数の List の List) ---
MK = "mk : n acc ?\n\tn = 0 : acc\n\tmk (n - 1) (acc~ [n (n * n)])\n"
PS = "ps : xs i acc ?\n\ti >= ||xs|| : acc\n\tps xs (i + 1) (acc + ((xs ' i) ' 1))\n"
same("入れ子: 記録を足す", MK + "mk 4 [[0 0]]\n")
same("入れ子: 記録を足して読む", MK + PS + "ps (mk 12 [[0 0]]) 0 0\n")
same("入れ子: 呼び側の入れ子は変わらない", MK + "xs : [[1 2] [3 4]]\nseq3 (println_int (||mk 3 xs||)) (println_int (||xs||)) ((mk 2 xs) ' 3)\n")
same("入れ子: 要素を取り出して足す", "cp : xs i acc ?\n\ti >= ||xs|| : acc\n\tcp xs (i + 1) (acc~ (xs ' i))\ncp [[1 2] [3 4] [5 6]] 0 [[9 9]]\n")
same("入れ子: 整数を足す(型が混ざる)", MK + "mk 3 [[0 0]]\nbd : n acc ?\n\tn = 0 : acc\n\tbd (n - 1) (acc~ n)\nbd 3 [[0 0]]\n")
same("入れ子: 空の内側", PS + "ps [[1 2] []] 0 0\n")
same("入れ子: 長さのそろわない内側", PS + "ps [[1 2] [3]] 0 0\n")
same("入れ子: 小数の内側", PS + "ps [[1 2] [3 4.5]] 0 0\n")
same("入れ子: さらに深い", PS + "ps [[[1 2] 3] [[4 5] 6]] 0 0\n")
same("入れ子: ||xs|| と残り", "ln : xs ?\n\t||xs|| < 2 : ||xs||\n\t1 + (ln (xs ' 1~))\nln [[1 2] [3 4] [5 6] [7 8]]\n")
same("入れ子: 等しい比べ", "eq : a b ?\n\ta = b : 1\n\t0\nseq2 (println_int (eq [[1 2] [3 4]] [[1 2] [3 4]])) (println_int (eq [[1 2] [3 4]] [[1 2] [3 5]]))\n")
same("入れ子: メモリへ置いて読む", "R : 0x5000\nsv : xs ? (R # xs)\nrd : i ? (@R) ' i\nseq3 (sv [[1 2] [3 4]]) (println_int (||rd 1||)) (rd 0)\n")

# --- 括りの残り [x ~xs](位置で読む輪・切り出す道・底の無い形・型の外れ) ---
SX = "sx : [x ~xs] acc ?\n\t||xs|| = 0 : acc + x\n\tsx xs (acc + x)\n"
for l in ("[1 2 3 4]", "[7]", "5", "[]", "[1 2.5 3]", "[1 `a` 3]", "[[1 2] [3]]"): same(f"残り: 和 sx {l}", SX + f"sx {l} 0\n")
same("残り: 2 つずつ", "s2 : [x y ~r] acc ?\n\t||r|| = 0 : acc + x + y\n\ts2 r (acc + (x * y))\ns2 [1 2 3 4 5 6] 0\n")
same("残り: 2 つずつ(余る)", "s2 : [x y ~r] acc ?\n\t||r|| = 0 : acc + x + y\n\ts2 r (acc + (x * y))\ns2 [1 2 3 4 5] 0\n")
same("残り: 別の List の引数もある", "dt : [x ~xs] ys acc ?\n\t||xs|| = 0 : acc + (x * (ys ' 0))\n\tdt xs (ys ' 1~) (acc + (x * (ys ' 0)))\ndt [1 2 3] [4 5 6] 0\n")
same("残り: 条件で別の List を読む", "dt : [x ~xs] ys acc ?\n\t(ys ' 0) > 100 : acc\n\t||xs|| = 0 : acc + x\n\tdt xs ys (acc + (x * (ys ' 0)))\ndt [1 2 3] [4 5 6] 0\n")
same("残りを別の関数へ渡す(切り出す道)", "ln : l ? ||l||\nsx : [x ~xs] acc ?\n\t||xs|| = 0 : acc + x\n\tsx xs (acc + x + (ln xs))\nsx [1 2 3 4] 0\n")
same("残りを答えにする", "tl : [x ~xs] n ?\n\tn = 0 : xs\n\ttl xs (n - 1)\ntl [1 2 3 4 5] 2\n")
same("残りの先頭を読む", "hd : [x ~xs] acc ?\n\t||xs|| = 0 : acc + x\n\thd xs (acc + x + (xs ' 0))\nhd [1 2 3 4] 0\n")
same("残りが空のときに先頭を読む", "hd : [x ~xs] ?\n\t(xs ' 0) | 99\nhd [5]\n")
same("残りを新しい List に替える", "sx : [x ~xs] acc ?\n\tacc > 10 : acc\n\t||xs|| = 0 : sx [x x x x] (acc + x)\n\tsx xs (acc + x)\nsx [1 2 3] 0\n")
same("残り: 非末尾の再帰", "sm : [x ~xs] ?\n\t||xs|| = 0 : x\n\tx + (sm xs)\nsm [1 2 3 4 5]\n")
same("残り: 名前より短い List", "p3 : [a b c ~r] ?\n\t||r|| = 0 : a + b + c\n\t0\np3 [1 2]\n")
same("残り: 名前と同じ長さ", "p3 : [a b c ~r] ?\n\t||r|| = 0 : a + b + c\n\t0\np3 [1 2 3]\n")
same("残り: 数える", "cn : [x ~xs] n ?\n\t||xs|| < 3 : n\n\tcn xs (n + 1)\ncn [1 2 3 4 5 6] 0\n")
same("残り: 呼び側の List は変わらない", SX + "ys : [4 5 6]\nseq2 (println_int (sx ys 0)) (ys ' 2)\n")
a, _ = run(SX + "bd : n acc ?\n\tn = 0 : acc\n\tbd (n - 1) (acc~ n)\nsx (bd 20000 [0]) 0\n", True)
check("残り: 2 万個の和", a[1].strip(), "200010000")

# --- 乱数: List の取り出しと比べを混ぜた関数 ---
rnd = random.Random(20261031)
def ix(): return "(r ' %d)" % rnd.randint(0, 3)
def e(d=0):
    c = rnd.random()
    if d > 2 or c < 0.3: return rnd.choice(["x", "y", ix(), str(rnd.randint(0, 9))])
    return "(%s %s %s)" % (e(d + 1), rnd.choice("+-*"), e(d + 1))
progs = []
for i in range(40):
    rows = []
    for _ in range(rnd.randint(1, 3)):
        cmpop = rnd.choice(["<", ">", "=", "<=", ">="])
        rows.append("\t(%s %s %s) : %s" % (e(), cmpop, e(), e()))
    last = rnd.choice(["", "\t" + e() + "\n"])
    lst = lambda: "[" + " ".join(str(rnd.randint(0, 9)) for _ in range(rnd.choice([3, 4, 5, 4, 2]))) + "]"
    hlp = "g : x y r ?\n" + "\n".join(rows) + "\n" + last
    top = "f : x r ?\n\t(g x (x + 1) r) | 42\n"
    calls = "\n".join("println_int (f %d %s)" % (rnd.randint(0, 9), lst()) for _ in range(3))
    progs.append(hlp + top + "seq3 (" + calls.split("\n")[0] + ") (" + calls.split("\n")[1] + ") (" + calls.split("\n")[2] + ")\n")
bad_r = bad; n = 0
for i, src in enumerate(progs):
    a, _ = run(src, True, 20); b, _ = run(src, False, 20)
    if a == ("timeout",) or b == ("timeout",): continue
    n += 1
    if a != b: check(f"乱数の List の関数 {i}", a, b); print(src)
check("乱数の List の関数を 30 本以上比べた", n >= 30, True)
check("乱数の List の関数はすべて一致", bad == bad_r, True)

# --- 乱数: List を回す・足す再帰(括りの仮引数・acc~・添字・長さ) ---
rl = random.Random(31)
def ie(vs, d=0):
    c = rl.random()
    if d > 2 or c < 0.35: return rl.choice(vs + [str(rl.randint(0, 5))])
    if c < 0.5: return "(xs ' %s)" % rl.choice(["i", "0", "(i + 1)", "(||xs|| - 1)"])
    if c < 0.6: return "||acc||"
    if c < 0.7: return "(acc ' %s)" % rl.choice(["0", "(||acc|| - 1)"])
    return "(%s %s %s)" % (ie(vs, d + 1), rl.choice("+-*"), ie(vs, d + 1))
lp = []
for i in range(40):
    vs = ["i", "n"]
    rows = ["\ti >= ||xs|| : %s" % rl.choice(["acc", "||acc||", "(acc ' 0)", ie(vs)])]
    if rl.random() < 0.6: rows.append("\t(%s %s %s) : %s" % (ie(vs), rl.choice(["<", ">", "=", "<=", ">="]), ie(vs), rl.choice(["acc", ie(vs)])))
    adds = " ".join(ie(vs) for _ in range(rl.randint(1, 2)))
    other = "(acc~ %s)" % adds
    if rl.random() < 0.3: rows.append("\t(%s %s %s) : g xs (i + 1) n acc" % (ie(vs), rl.choice(["<", ">", "="]), ie(vs)))
    if rl.random() < 0.2: rows.append("\t(%s %s %s) : g xs (i + 1) n [%s]" % (ie(vs), rl.choice(["<", ">", "="]), ie(vs), ie(vs)))
    rows.append("\tg xs (i + 1) n %s" % other)
    xs = "[" + " ".join(str(rl.randint(0, 9)) for _ in range(rl.randint(1, 7))) + "]"
    lp.append("g : xs i n acc ?\n" + "\n".join(rows) + "\n\nseq2 (println_int (||g %s 0 %d [1]||)) (println_int ((g %s 0 %d [2 3]) ' 0))\n" % (xs, rl.randint(0, 4), xs, rl.randint(0, 4)))
bad_r = bad; n = 0
for i, src in enumerate(lp):
    a, _ = run(src, True, 20); b, _ = run(src, False, 20)
    if a == ("timeout",) or b == ("timeout",): continue
    n += 1
    if a != b: check(f"乱数の List を回す関数 {i}", a, b); print(src)
check("乱数の List を回す関数を 30 本以上比べた", n >= 30, True)
check("乱数の List を回す関数はすべて一致", bad == bad_r, True)

# --- 乱数: 括りの残り [x ~xs] を回す関数 ---
rr = random.Random(77)
def re_(vs, nm, d=0):
    c = rr.random()
    if d > 2 or c < 0.35: return rr.choice(vs + [str(rr.randint(0, 5))])
    if c < 0.5: return "||%s||" % rr.choice(["r", "r", "ys"])
    if c < 0.58: return "(ys ' %s)" % rr.choice(["0", "1", "(||ys|| - 1)"])
    if c < 0.66: return "(r ' %s)" % rr.choice(["0", "1"])
    return "(%s %s %s)" % (re_(vs, nm, d + 1), rr.choice("+-*"), re_(vs, nm, d + 1))
rp = []
for i in range(40):
    names = rr.choice(["x", "x y"]); vs = names.split() + ["acc"]
    rows = []
    if rr.random() < 0.7: rows.append("\t||r|| %s %d : %s" % (rr.choice(["=", "<", "<="]), rr.randint(0, 2), re_(vs, "r")))
    if rr.random() < 0.5: rows.append("\t(%s %s %s) : %s" % (re_(vs, "r"), rr.choice(["<", ">", "="]), re_(vs, "r"), rr.choice(["acc", re_(vs, "r")])))
    nxt = rr.choice(["r", "r", "r", "[%s]" % " ".join(re_(vs, "r") for _ in range(len(names.split()) + 1))])
    ys = rr.choice(["ys", "(ys ' 1~)", "ys"])
    rows.append("\tf %s %s (%s)" % (nxt, ys, re_(vs, "r")))
    xs = "[" + " ".join(str(rr.randint(0, 9)) for _ in range(rr.randint(1, 8))) + "]"
    ysl = "[" + " ".join(str(rr.randint(0, 9)) for _ in range(rr.randint(1, 8))) + "]"
    rp.append("f : [%s ~r] ys acc ?\n%s\nseq2 (println_int (f %s %s %d)) (println_int (f %s %s 0))\n" % (names, "\n".join(rows), xs, ysl, rr.randint(0, 3), ysl, xs))
bad_r = bad; n = 0
for i, src in enumerate(rp):
    a, _ = run(src, True, 20); b, _ = run(src, False, 20)
    if a == ("timeout",) or b == ("timeout",): continue
    n += 1
    if a != b: check(f"乱数の残りの関数 {i}", a, b); print(src)
check("乱数の残りの関数を 30 本以上比べた", n >= 30, True)
check("乱数の残りの関数はすべて一致", bad == bad_r, True)

print("\n全部 ok" if not bad else f"\n{bad} 件 NG"); sys.exit(1 if bad else 0)
