#!/usr/bin/env python3
"""整数の純粋な再帰関数を Python の関数にして走らせる速い道(sign_interp.py の run_pure)の試験。
速い道あり(既定)と無し(SIGN_NO_PURE=1)で、同じ入力が同じ出力になることを、型の違う関数・端の値で確かめる。python test_pure.py"""
import os, random, subprocess, sys, tempfile, time
HERE = os.path.dirname(os.path.abspath(__file__))
bad = 0
def check(name, got, want):
    global bad
    ok = got == want; bad += not ok
    print(("ok  " if ok else "NG  ") + name + ("" if ok else f"\n    得た: {got!r}\n    期待: {want!r}"))

TMP = tempfile.mkdtemp()
def run(src, pure, timeout=120, flags=()):
    p = os.path.join(TMP, "t.sn"); open(p, "w", encoding="utf-8").write(src)
    env = dict(os.environ); env["SIGN_NO_PURE"] = "0" if pure else "1"
    t = time.time()
    try: r = subprocess.run([sys.executable, os.path.join(HERE, "sign.py"), p, *flags], capture_output=True, text=True, timeout=timeout, env=env, cwd=HERE)
    except subprocess.TimeoutExpired: return ("timeout",), timeout
    return (r.returncode, r.stdout, r.stderr), time.time() - t

def same(name, src, show=None, flags=()):
    a, ta = run(src, True, flags=flags); b, tb = run(src, False, flags=flags)
    check(name, a, b)
    if show: print(f"      {show}: 速い道 {ta:.2f}s / 普通の道 {tb:.2f}s")
    return a

# --- 見本 ---
FIB = "fib : n ?\n\tn < 2 : n\n\t(fib (n - 1)) + (fib (n - 2))\n"
a = same("fib 20 = 6765", FIB + "fib 20\n", "fib 20")
check("fib 20 の答え", a[1].split()[-1], "6765")
same("fib 0 / 1 / 2", FIB + "seq3 (println_int (fib 0)) (println_int (fib 1)) (println_int (fib 2))\n".replace("seq3", "seq3"))
same("fib に負の数", FIB + "fib (0 - 5)\n")
same("fib に list を渡す(整数でないので普通の道)", FIB + "fib [1 2]\n")
same("fib に __ を渡す", FIB + "fib __\n")

ACK = "ack : m n ?\n\tm = 0 : n + 1\n\tn = 0 : ack (m - 1) 1\n\tack (m - 1) (ack m (n - 1))\n"
a = same("アッカーマン 2 3 = 9", ACK + "ack 2 3\n", "ack 2 3")
check("ack 2 3 の答え", a[1].split()[-1], "9")
same("アッカーマン 3 3", ACK + "ack 3 3\n")

# 0 で割る: 決まらない → 普通の道でやり直して同じ結果
DIV = "h : n ?\n\tn < 1 : 100\n\t(100 / (n - 3)) + (h (n - 1))\n"
for n in (2, 3, 4, 10): same(f"0 で割る関数 h {n}", DIV + f"h {n}\n")
MOD = "m : n ?\n\tn = 0 : 0\n\t(n % 7) + (m (n / 3))\n"
for n in (0, 100, -100, 12345, -7): same(f"剰余・商の符号 m {n}", MOD + f"m ({n})\n".replace("(-", "(0 - ") if n < 0 else MOD + f"m {n}\n")
same("負の数の商と剰余を直に", "q : n ?\n\tn = 99 : 0\n\t((n / 4) * 1000) + (n % 4) + (q 99)\nseq3 (println_int (q (0 - 7))) (println_int (q 7)) (println_int (q (0 - 8)))\n")

# 外の整数の名前
K = "K : 5\nf : n ?\n\tn < K : n\n\t(f (n - 1)) + (f (n - K))\n"
same("外の整数 K を使う", K + "f 15\n")
same("外の名前が整数でない(関数)とき", "K : 5\ng : x ? x + 1\nf : n ?\n\tn < 2 : n\n\t(f (n - 1)) + (g 0)\nf 5\n")

# 深い再帰(速い道が再帰の上限に当たっても、普通の道が同じ答え・同じ失敗を出す)
DEEP = "d : n ?\n\tn < 1 : 0\n\t1 + (d (n - 1))\n"
for n in (10, 3000): same(f"深い再帰 d {n}", DEEP + f"d {n}\n", f"d {n}")
a, ta = run(DEEP + "d 60000\n", True); b, tb = run(DEEP + "d 60000\n", False)
check("深い再帰 d 60000: 普通の道が『再帰が深すぎます』で失敗する深さでも、速い道は正しい答え 60000(同じ答えか、失敗が答えになるだけ)", a == b or (a[1].strip() == "60000" and b[0] == 1 and "再帰が深すぎます" in b[2]), True)

# 末尾再帰(従来の輪)との共存
same("末尾再帰 + 二重再帰の混ざり", "t : n acc ?\n\tn < 1 : acc\n\tt (n - 1) (acc + n)\nu : n ?\n\tn < 2 : n\n\t(u (n - 1)) + (t n 0)\nu 12\n")
same("本体に局所の定義がある関数(速い道の対象外)", "z : n ?\n\tk : n * 2\n\tn < 2 : n\n\t(z (n - 1)) + k\nz 6\n")
same("既定値つきの仮引数(対象外)", "z : [n : 3] ?\n\tn < 2 : n\n\t(z (n - 1)) + 1\nz\n")
same("2 つの関数が互いに呼ぶ(対象外)", "ev : n ?\n\tn = 0 : 1\n\tod (n - 1)\nod : n ?\n\tn = 0 : 0\n\tev (n - 1)\nev 10\n")
same("行が足りない(既定の行が無い)とき __", "w : n ?\n\tn > 5 : 1\nseq2 (println_int (w 9)) (println_int (w 1))\n")


# --- 他の純粋な関数を呼ぶ関数・相互再帰 ---
GCD = "gcd : a b ?\n\tb = 0 : a\n\tgcd b (a % b)\n"
LCM = GCD + "lcm : a b ? (a / (gcd a b)) * b\n"
a = same("gcd を呼ぶ lcm", LCM + "seq3 (println_int (lcm 4 6)) (println_int (lcm 21 6)) (println_int (lcm 7 0))\n")
check("lcm 4 6 = 12・lcm 21 6 = 42・lcm 7 0 = 0", a[1].strip(), "[12, 42, 0]")
MUT = "a : n ?\n\tn < 2 : n\n\t(b (n - 1)) + (a (n - 2))\nb : n ?\n\tn < 2 : 1\n\t(a (n - 1)) + (b (n - 2))\n"
for n in (0, 1, 2, 10, 20): same(f"相互再帰 a {n}", MUT + f"a {n}\n")
same("相互再帰 b に負の数", MUT + "b (0 - 3)\n")
EVOD = "ev : n ?\n\tn = 0 : 1\n\tod (n - 1)\nod : n ?\n\tn = 0 : 0\n\tev (n - 1)\n"
for n in (0, 7, 100, 2500): same(f"偶奇の相互再帰 ev {n}", EVOD + f"ev {n}\n")
same("三つの関数の輪", "p : n ?\n\tn < 1 : 0\n\t1 + (q (n - 1))\nq : n ?\n\tn < 1 : 0\n\t2 + (r (n - 1))\nr : n ?\n\tn < 1 : 0\n\t3 + (p (n - 1))\np 10\n")
same("途中で 0 で割る(別の関数の中)", "d : x ? 100 / x\nf : n ?\n\tn < 1 : 0\n\t(d (n - 2)) + (f (n - 1))\nseq2 (println_int (f 1)) (println_int (f 5))\n")
same("呼ぶ相手が対象外(list を使う)なら全体が普通の道", "h : x ? [x x]\nf : n ?\n\tn < 1 : 0\n\t(h n) + (f (n - 1))\nf 3\n")
same("呼ぶ相手が組み込みの関数", "f : n ?\n\tn < 1 : 0\n\t(abs (0 - n)) + (f (n - 1))\nf 10\n")
same("引数の数が合わない呼び出し(部分適用)", "g : x y ? x + y\nf : n ?\n\tn < 1 : 0\n\t(g n) + (f (n - 1))\nf 3\n")
same("局所の関数を外の関数が呼ぶ(呼ぶたびに別の環境)", "outer : k ?\n\tadd : x ? x + k\n\tadd (add k)\nrep : n ?\n\tn < 1 : 0\n\t(outer n) + (rep (n - 1))\nrep 20\n")
same("外の整数が呼び出しのあいだに変わらない(定義は 1 回)", "K : 3\nsq : x ? x * x\nf : n ?\n\tn < K : sq n\n\t(f (n - 1)) + (sq K)\nf 12\n")
MUTSPEED = MUT + "a 24\n"
a, ta = run(MUTSPEED, True); b, tb = run(MUTSPEED, False)
check("相互再帰 a 24: 同じ答えで 3 倍以上速い", (a == b, ta * 3 < tb), (True, True))
print(f"      相互再帰 a 24: 速い道 {ta:.2f}s / 普通の道 {tb:.2f}s")


# --- ビット演算(&& || ;; << >>) ---
PC = "pc : x ?\n\tx = 0 : 0\n\t(x && 1) + (pc (x >> 1))\n"
a = same("ビットを数える pc", PC + "seq4 (pc 0) (pc 255) (pc 1023) (pc 0xF0F0)\n")
for n in (0, 1, 255, 65535, 123456789): same(f"pc {n}", PC + f"pc {n}\n")
check("pc 255 = 8", run(PC + "pc 255\n", True)[0][1].strip(), "8")
REV = "rv : x acc n ?\n\tn = 0 : acc\n\trv (x >> 1) ((acc << 1) || (x && 1)) (n - 1)\nbr : x ? rv x 0 8\n"
for n in (0, 1, 6, 255, 0x81): same(f"ビットの逆順 br {n}", REV + f"br {n}\n")
XOR = "xs : n ?\n\tn < 1 : 0\n\t(n ;; (n << 2)) + (xs (n - 1))\n"
same("xor とシフトの和", XOR + "xs 50\n")
MASK = "M : 0xFF\nmk : x ?\n\tx < 1 : 0\n\t((x * 37) && M) + (mk (x - 1))\n"
same("外の整数を 0x… で定義(マスク)", MASK + "mk 40\n")
same("0x… の直書き", "g : x ?\n\tx < 1 : 0\n\t((x ;; 0xA5) && 0x7F) + (g (x - 1))\ng 30\n")
same("負の数のビット演算(2 の補数)", "nb : x ?\n\tx > 3 : 0\n\t(((0 - 8) >> x) ;; ((0 - 3) && 7)) + (nb (x + 1))\nnb (0 - 2)\n")
same("&& に -1(全部 1)", "m1 : x ?\n\tx < 1 : 0\n\t(x && (0 - 1)) + (m1 (x - 1))\nm1 10\n")
same("&& に巨大なマスク", "mb : x ?\n\tx < 1 : 0\n\t(x && 0xFFFFFFFFFFFF) + (mb (x - 1))\nmb 10\n")
same("負のシフトは普通の道に任せる(同じ失敗)", "ns : x ?\n\tx < 1 : 0\n\t(1 << (x - 3)) + (ns (x - 1))\nns 5\n")
same("巨大なシフトは普通の道に任せる", "hs : x ?\n\tx < 1 : 0\n\t((1 << 200000) && 1) + (hs (x - 1))\nhs 2\n")
BIT = PC + "pcs : n ?\n\tn < 1 : 0\n\t(pc n) + (pcs (n - 1))\n"
a, ta = run(BIT + "pcs 3000\n", True); b, tb = run(BIT + "pcs 3000\n", False)
check("pc を呼ぶ pcs 3000: 同じ答えで速い", (a == b, ta < tb), (True, True))
print(f"      pcs 3000: 速い道 {ta:.2f}s / 普通の道 {tb:.2f}s")


# --- @ で読むだけの関数・末尾再帰の輪 ---
STD = "`" + os.path.join(HERE, "std.sn") + "`@~\n"
FILL = "fill : p n i ?\n\ti >= n : 0\n\t(p + (i * 4)) # ((i * 7) % 13) : fill p n (i + 1)\n"
a = same("arr_sum / arr_max / arr_min", STD + FILL + "seq4 (fill 0x600000 3000 0) (println_int (arr_sum 0x600000 3000)) (println_int (arr_max 0x600000 3000)) (println_int (arr_min 0x600000 3000))\n", "arr_sum 3000")
check("arr_sum の答え", a[1].split()[0], str(sum((i * 7) % 13 for i in range(3000))))
same("書いたあとで読み直す(メモリの変化を見る)", STD + FILL + "seq5 (fill 0x600000 50 0) (println_int (arr_sum 0x600000 50)) ((0x600000 + 8) # 1000) (println_int (arr_sum 0x600000 50)) 0\n")
same("未書き込みの番地を読む(__ は普通の道に任せる)", STD + "arr_sum 0x640000 5\n")
same("途中に未書き込みがある", STD + "seq3 (0x600000 # 5) (0x600008 # 7) (arr_sum 0x600000 3)\n")
same("メモリに整数でない値(文字列)", STD + "seq2 (0x600000 # `ab`) (arr_sum 0x600000 1)\n")
same("str_len(0 終わりの文字列)", STD + "seq2 (str_put 0x600000 `hello world`) (str_len 0x600000)\n")
same("str_len の長い文字列(輪になっている)", STD + "seq3 (arr_fill 0x600000 80000 65) ((0x600000 + (80000 * 4)) # 0) (str_len 0x600000)\n", "str_len 8万")
check("str_len 8万 の答え", run(STD + "seq3 (arr_fill 0x600000 80000 65) ((0x600000 + (80000 * 4)) # 0) (str_len 0x600000)\n", True)[0][1].strip().split()[-1], "80000")
same("文字列の比較 str_eq / str_find", STD + "seq3 (str_put 0x600000 `hello world`) (str_put 0x610000 `world`) (str_find 0x600000 0x610000)\n")
same("arr_find・arr_count", STD + "seq5 (arr_fill 0x600000 100 3) ((0x600000 + 40) # 9) (arr_find 0x600000 100 9) (arr_count 0x600000 100 3) 0\n")
GETSUM = "g : p n ?\n\tn < 1 : 0\n\t(@(p + ((n - 1) * 4))) + (g p (n - 1))\n"
same("@ を式の一部に使う二重でない再帰", FILL + GETSUM + "seq2 (fill 0x600000 100 0) (g 0x600000 100)\n")
same("負の番地・大きな番地を読む", "r : a ? @a\nseq3 (r (0 - 4)) (r 0x7FFFFFFFFFF) 0\n")
same("装置の番地を読む(GPIO)は普通の道に任せる", "pin : n ?\n\tn < 1 : 0\n\t(@(0x9500000 + 68)) + (pin (n - 1))\nseq2 (0x9500044 # 1) (pin 3)\n", flags=("--gpio=fake",))
same("UART(標準入力)の読みは副作用を重ねない", "u : n ?\n\tn < 1 : 0\n\t(@0x9000000) + (u (n - 1))\nu 2\n")
LOOPS = "gc : a b ?\n\tb = 0 : a\n\tgc b (a % b)\n"
for x, y in ((12, 18), (17, 5), (0, 9), (1071, 462), (123456789, 987654321)): same(f"gcd の輪 {x} {y}", LOOPS + f"gc {x} {y}\n")
same("入れ替える引数が同時に評価される(輪)", "sw : a b n ?\n\tn = 0 : a - b\n\tsw b a (n - 1)\nseq2 (sw 10 3 5) (sw 10 3 4)\n")
same("輪の中で別の関数を呼ぶ", "sq : x ? x * x\ncs : n acc ?\n\tn < 1 : acc\n\tcs (n - 1) (acc + (sq n))\ncs 5000 0\n")
a, ta = run(STD + FILL + "seq2 (fill 0x600000 20000 0) (arr_sum 0x600000 20000)\n", True); b, tb = run(STD + FILL + "seq2 (fill 0x600000 20000 0) (arr_sum 0x600000 20000)\n", False)
check("arr_sum 2 万: 同じ答え", a == b, True)
print(f"      fill+arr_sum 2万(fill は対象外): 速い道 {ta:.2f}s / 普通の道 {tb:.2f}s")

# --- 条件に & と |・局所の定義 ---
GCD2 = "gcd : a b ?\n\tb = 0 : a\n\tgcd b (a % b)\n"
same("局所の定義(gcd を呼ぶ lcm)", GCD2 + "lcm : a b ?\n\tg : gcd a b\n\t(a / g) * b\nseq3 (lcm 4 6) (lcm 21 6) (lcm 9 9)\n")
same("局所の定義が連なる", GCD2 + "w : a b ?\n\tg : gcd a b\n\tq : a / g\n\tr : q * b\n\tr + g\nseq2 (w 12 18) (w 7 5)\n")
same("局所の定義 + 速さ", GCD2 + "lcm : a b ?\n\tg : gcd a b\n\t(a / g) * b\nsl : n ?\n\tn < 2 : 1\n\t(lcm n (n - 1)) + (sl (n - 1))\nsl 2000\n")
same("局所の名前が仮引数と同じ(条件の行になる)", GCD2 + "v : a b ?\n\ta : 5\n\ta + b\nv 1 2\n")
same("局所の名前が外の定義と同じ(条件の行になる)", GCD2 + "K : 7\nv : a ?\n\tK : 5\n\ta + K\nv 1\n")
same("局所の名前が重複", GCD2 + "v : a ?\n\tk : 1\n\tk : 2\n\ta + k\nv 1\n")
same("局所の定義が後の定義を使う", GCD2 + "v : a ?\n\tk : m + 1\n\tm : a * 2\n\tk + m\nv 3\n")
same("局所の定義が自分を使う(輪)", GCD2 + "v : a ?\n\tk : k + 1\n\tk + a\nv 3\n")
same("局所の定義が関数", GCD2 + "v : a ?\n\tdbl : x ? x * 2\n\tdbl a\nv 4\n")
same("局所の定義が 0 で割る", GCD2 + "v : a b ?\n\tk : 100 / b\n\tk + (gcd a b)\nseq2 (v 4 0) (v 4 5)\n")
same("局所の定義が未書き込みを読む", GCD2 + "v : a ?\n\tk : @a\n\t(gcd k 6) + a\nv 0x655000\n")
CND = "c : x ?\n\t((x > 1) & (x < 9)) | (x = 0) : 1\n\t0\n"
same("条件に & と |", CND + "seq5 (c 0) (c 1) (c 5) (c 9) (c (0 - 3))\n")
CNR = "cn : n ?\n\t(n < 1) | (n = 7) : 0\n\t((n % 2) = 0) & (n > 3) : (cn (n - 1)) + 2\n\t(cn (n - 1)) + 1\n"
for n in (0, 7, 8, 20): same(f"条件に & | を使う再帰 cn {n}", CNR + f"cn {n}\n")
same("条件の片方が 0 で割る(& で左が偽なら右は見ない)", "dz : x ?\n\t(x > 0) & ((100 / x) > 3) : 1\n\t0\nseq3 (dz 0) (dz 5) (dz 50)\n")
same("条件の片方が 0 で割る(| で左が真なら右は見ない)", "dz : x ?\n\t(x = 0) | ((100 / x) > 3) : 1\n\t0\nseq3 (dz 0) (dz 5) (dz 50)\n")
same("& の左右が違う型(比べ以外)は普通の道", "dz : x ?\n\t(x > 0) & x : 1\n\t0\nseq2 (dz 0) (dz 5)\n")
same("条件の中で関数を呼ぶ", GCD2 + "cp : a b ?\n\t((gcd a b) = 1) & (a > b) : 1\n\t0\nseq3 (cp 9 4) (cp 4 9) (cp 12 8)\n")
same("文字の数字判定(標準の std_atoi / str_is_int / str_to_int)", STD + "seq5 (str_put 0x600000 `12345`) (str_is_int 0x600000) (str_to_int 0x600000) (str_put 0x610000 `-42x`) (str_to_int 0x610000)\n")
same("文字列の大文字化・trim などの標準関数", STD + "seq4 (str_put 0x600000 `  Hello World  `) (str_upper 0x600000) (str_trim 0x600000) (println_mem 0x600000)\n")
NUMSTR = STD + "seq2 (str_put 0x600000 `1234567890`) (rep2 0 0)\nrep2 : k acc ?\n\tk >= 400 : acc\n\trep2 (k + 1) (acc + (str_to_int 0x600000))\n"
a, ta = run(NUMSTR, True); b, tb = run(NUMSTR, False)
check("str_to_int を 400 回: 同じ答え", a == b, True)
print(f"      str_to_int 400 回: 速い道 {ta:.2f}s / 普通の道 {tb:.2f}s")

# --- 書き込み(#): 差分表に溜め、最後まで成功したときだけ反映 ---
DUMP = "dump : p n i ?\n\ti >= n : 0\n\tseq2 (println_int (@(p + (i * 4)))) (dump p n (i + 1))\n"
Z = "seq2 (arr_fill 0x600000 12 0) "
a = same("arr_fill / arr_copy / arr_reverse", STD + DUMP + "seq5 (arr_fill 0x600000 6 3) ((0x600008) # 9) (arr_copy 0x700000 0x600000 6) (arr_reverse 0x700000 6) (dump 0x700000 6 0)\n")
check("arr_reverse の結果 [3,3,9,3,3,3] の逆順", a[1].split()[:6], ["3", "3", "3", "9", "3", "3"])
same("arr_swap / arr_sort", STD + DUMP + "seq5 (arr_fill 0x600000 8 0) (arr_set 0x600000 0 5) (arr_set 0x600000 3 2) (arr_sort 0x600000 8) (dump 0x600000 8 0)\n")
same("str_cpy / str_cat / str_upper / str_reverse", STD + "seq6 (str_put 0x600000 `abc`) (str_put 0x610000 `def`) (str_cat 0x600000 0x610000) (str_upper 0x600000) (str_reverse 0x600000) (println_mem 0x600000)\n")
same("重なる範囲の arr_copy(前から順に)", STD + DUMP + "seq5 (arr_fill 0x600000 8 1) (arr_set 0x600000 0 9) (arr_copy 0x600004 0x600000 6) (dump 0x600000 8 0) 0\n")
same("書いたあとで同じ番地を読む", "rw : p ? seq3 (p # 5) (p # ((@p) + 1)) (@p)\nrw 0x600000\n")
same("書き込みの値は番地(0 番地も __ ではない)", "wz : n ?\n\t(0 # n) : 1\n\t0\nseq2 (wz 5) (@0)\n")
same("書き込みを条件にした行だけの再帰(最後の行に条件)", "wl : p n ?\n\tn < 1 : 0\n\t((p + (n * 4)) # (n * n)) : wl p (n - 1)\nseq2 (wl 0x600000 10) (@(0x600000 + 40))\n")
same("前の値を読んで書く(累積和)", STD + DUMP + "ps : p n i ?\n\ti >= n : 0\n\t((p + (i * 4)) # ((@(p + ((i - 1) * 4))) + i)) : ps p n (i + 1)\nseq3 (arr_fill 0x600000 10 0) (ps 0x600000 10 1) (dump 0x600000 10 0)\n")
same("非末尾の再帰で左右が重なって書く", STD + DUMP + "tr : p n ?\n\tn < 1 : 0\n\tseq3 ((p + ((n % 3) * 4)) # n) (tr p (n - 1)) (tr p (n - 2))\nseq3 (arr_fill 0x600000 3 0) (tr 0x600000 8) (dump 0x600000 3 0)\n")
# 書いたあとで決まらなくなる → 全部取り消して普通の道: 書き込みが二重にならない
same("書いたあとに 0 で割る(差分表は捨てて最初から)", STD + DUMP + "wd : p n ?\n\tn < 1 : 0\n\tseq3 ((p + (n * 4)) # (100 / (n - 3))) (wd p (n - 1)) 0\nseq3 (arr_fill 0x600000 8 0) (wd 0x600000 6) (dump 0x600000 8 0)\n")
same("書いたあとに未書き込みを読む", STD + DUMP + "wu : p n ?\n\tn < 1 : 0\n\tseq3 ((p + (n * 4)) # n) (wu p (n - 1)) (@(0x680000 + (n * 4)))\nseq2 (arr_fill 0x600000 8 0) (wu 0x600000 4)\n")
same("途中で装置(GPIO)へ書く: 装置への書き込みは 1 回だけ", STD + "gw : n ?\n\tn < 1 : 0\n\tseq3 ((0x600000 + (n * 4)) # n) ((0x9500000 + 68) # (n % 2)) (gw (n - 1))\ngw 4\n", flags=("--gpio=fake",))
same("UART への書き込みは 1 回だけ", STD + "uw : n ?\n\tn < 1 : 0\n\tseq3 ((0x600000 + (n * 4)) # n) (0x9000000 # (64 + n)) (uw (n - 1))\nuw 3\n")
a = run(STD + "uw : n ?\n\tn < 1 : 0\n\tseq3 ((0x600000 + (n * 4)) # n) (0x9000000 # (64 + n)) (uw (n - 1))\nuw 3\n", True)[0]
check("UART には ABC の順に 1 回ずつ", a[1].count("C") == 1 and a[1].count("B") == 1 and a[1].count("A") == 1, True)
WB = "wb : p n ?\n\tn < 1 : 0\n\tseq3 ((p + (n * 4)) # n) (wb p (n - 1)) 0\n"
a, ta = run(STD + WB + "seq2 (wb 0x600000 60000) (arr_sum 0x600000 60000)\n", True); b, tb = run(STD + WB + "seq2 (wb 0x600000 60000) (arr_sum 0x600000 60000)\n", False)
check("深い非末尾再帰 + 書き込み(60000)", a[0] == 0 or b[0] == 1, True)
a, ta = run(STD + "seq3 (arr_fill 0x600000 100000 7) (arr_copy 0x700000 0x600000 100000) (println_int (arr_sum 0x700000 100000))\n", True)
b, tb = run(STD + "seq3 (arr_fill 0x600000 100000 7) (arr_copy 0x700000 0x600000 100000) (println_int (arr_sum 0x700000 100000))\n", False)
check("arr_fill + arr_copy + arr_sum 10 万: 同じ答えで 5 倍以上速い", (a == b, ta * 5 < tb), (True, True))
print(f"      arr_fill+arr_copy+arr_sum 10万: 速い道 {ta:.2f}s / 普通の道 {tb:.2f}s")
# 乱数で作った、書き込みを含む再帰
wrnd = random.Random(777)
wn = 0; wdiff = 0
for i in range(30):
    ex = lambda: wrnd.choice(["a", "n", "(a * 3)", "(a + n)", "((@0x600000) + 1)", "((@(0x600000 + ((a % 4) * 4))) + a)", "(a ;; 5)", "(a && 3)"])
    adr = lambda: "(0x600000 + ((%s %% 4) * 4))" % wrnd.choice(["a", "n", "(a + 1)", "(a * 3)"])
    op = wrnd.choice(["tail", "seq", "two"])
    if op == "tail":
        body = "\ta < 1 : @0x600000\n\t(%s # %s) : wf (a - 1) n\n" % (adr(), ex())
    elif op == "seq":
        body = "\ta < 1 : @0x600000\n\tseq3 (%s # %s) (%s # %s) (wf (a - 1) n)\n" % (adr(), ex(), adr(), ex())
    else:
        body = "\ta < 1 : @0x600000\n\tseq3 (%s # %s) (wf (a - 1) n) (wf (a - 2) n)\n" % (adr(), ex())
    src = STD + DUMP + "wf : a n ?\n" + body + "seq3 (arr_fill 0x600000 4 1) (println_int (wf %d %d)) (dump 0x600000 4 0)\n" % (wrnd.randint(0, 9), wrnd.randint(0, 9))
    a, _ = run(src, True, 20); b, _ = run(src, False, 20)
    if a == ("timeout",) or b == ("timeout",): continue
    wn += 1
    if a != b: wdiff += 1; check(f"乱数の書き込みつき関数 {i}", a, b); print(src)
check("乱数の書き込みつき関数を 20 本以上比べた", wn >= 20, True)
check("書き込みつきの乱数の関数がすべて一致", wdiff == 0, True)

# --- 乱数で作った二重再帰・条件つきの式 ---
rnd = random.Random(12345)
def expr(ps, depth=0):
    r = rnd.random()
    if depth > 2 or r < 0.35: return rnd.choice(ps + [str(rnd.randint(0, 5))])
    if rnd.random() < 0.25: return "(%s %s %d)" % (expr(ps, depth + 1), rnd.choice(["<<", ">>"]), rnd.randint(0, 5))
    return "(%s %s %s)" % (expr(ps, depth + 1), rnd.choice(["+", "-", "*", "&&", "||", ";;"]), expr(ps, depth + 1))
progs = []
for i in range(40):
    nps = rnd.choice([1, 2]); ps = ["a", "b"][:nps]
    args = lambda: " ".join("(%s)" % (rnd.choice(["a - 1", "a - 2", "b - 1", "a + b - 3"]).replace("b", ps[-1]) if nps == 2 or rnd.random() < 0.5 else "a - 1") for _ in ps)
    rows = []
    for _ in range(rnd.randint(1, 2)):
        one = lambda: "(%s %s %s)" % (expr(ps), rnd.choice(["<", "<=", ">", ">=", "=", "=="]), expr(ps))
        cnd = one() if rnd.random() < 0.5 else "(%s %s %s)" % (one(), rnd.choice("&|"), one())
        rows.append("\t%s : %s" % (cnd, expr(ps)))
    calls = " + ".join("(%s %s)" % (rnd.choice(["f", "f", "gg"]), args()) for _ in range(rnd.randint(1, 2)))
    guard = "\ta <= 0 : %s" % expr(ps)
    body = guard + "\n" + "\n".join(rows) + "\n\t" + calls + " + " + expr(ps)
    call = "f " + " ".join(str(rnd.randint(0, 9)) for _ in ps)
    helper = "gg : %s ?\n\t%s <= 0 : %s\n\t(f %s) %s %s\n" % (" ".join(ps), ps[0], expr(ps), " ".join(["(%s - 1)" % ps[0]] + ["(%s)" % ps[-1]] * (len(ps) - 1)), rnd.choice("+-*"), expr(ps))
    progs.append("f : %s ?\n%s\n%s%s\n" % (" ".join(ps), body, helper, call))
bad_r = bad
n_ok = 0
for i, src in enumerate(progs):
    a, ta = run(src, True, 20); b, tb = run(src, False, 20)
    if a == ("timeout",) or b == ("timeout",): continue
    n_ok += 1
    if a != b: check(f"乱数の関数 {i}", a, b); print(src)
check("乱数の関数を 20 本以上比べた(時間切れを除く)", n_ok >= 20, True)
check("乱数の関数はすべて速い道と普通の道で一致", bad == bad_r, True)


# --- 答えの記憶(メモ化): 同じ実引数の再帰が指数にならない。メモリに触れる関数は記憶しない ---
a, ta = run(FIB + "fib 90\n", True)
check("fib 90 = 2880067194370816120(記憶があれば一瞬)", a[1].split()[-1], "2880067194370816120")
check("fib 90 は 2 秒以内", ta < 2, True)
same("記憶: 相互再帰 ev/od", "ev : n ?\n\tn = 0 : 1\n\tod (n - 1)\nod : n ?\n\tn = 0 : 0\n\tev (n - 1)\nseq2 (println_int (ev 30)) (println_int (od 30))\n")
same("記憶しない: 数えてから答える(メモリを書く)関数は呼ぶたびに書く", "C : 0x5000\nh : n ?\n\tn < 2 : (C # ((@C) + 1))\n\t(h (n - 1)) + (h (n - 2))\nseq2 (C # 0) (seq2 (h 10) (@C))\n")
same("記憶: 外の整数を後で変えても古い答えを使わない", "K : 3\nf : n ?\n\tn < 2 : n\n\t(f (n - 1)) + (f (n - 2)) + K\nseq2 (println_int (f 10)) (println_int (f 10))\n")

# --- 速さ ---
a, ta = run(FIB + "fib 24\n", True); b, tb = run(FIB + "fib 24\n", False)
check("fib 24 は速い道のほうが速い(3 倍以上)", ta * 3 < tb, True)
print(f"      fib 24: 速い道 {ta:.2f}s / 普通の道 {tb:.2f}s")
# 番地を返す関数・番地どうしの差・括りの仮引数に番地(Addr の速い道の拡張)。答えが Addr のままか(あとの足し引きで域の規則が効くか)も見る
same("Addr: 返した番地にさらに足す(域の外は __)", "ra : p n ? p + n\nseq3 ((ra 0xFFFFFFFFFFFFFFF0 4) + 100) ((ra 0x10 4) + 1) ((ra 0x10 4) * 2)\n")
same("Addr: 番地どうしの差(負は __)", "rs : p q ? p - q\nseq3 (rs 0x20 0x10) (rs 0x10 0x20) ((rs 0x20 0x10) - 100)\n")
same("Addr: 番地どうしの和(域の外は __)", "rp : p q ? p + q\nseq2 (rp 0x10 0x20) (rp 0xFFFFFFFFFFFFFFF0 0x100)\n")
same("Addr: 番地を返す関数を別の関数が呼ぶ", "nx : p ? p + 8\ntw : p ? nx (nx p)\nseq2 (tw 0x10) (@(tw 0x600000))\n")
same("Addr: 括りの仮引数に番地(名前が 1 つ)", "rd : [p] ? p + 1\nseq2 (rd 0x10) (rd 0xFFFFFFFFFFFFFFFF)\n")
same("Addr: 括りの仮引数を輪で渡し直す", "rl : [p] n ?\n\tn < 1 : p\n\trl (p + 8) (n - 1)\nseq2 (rl 0x10 3) (rl 0xFFFFFFFFFFFFFFF0 5)\n")
same("Addr: 括りに名前が 2 つ・残りつきは普通の道", "r2 : [p q] ? p\nr3 : [~r] ? 1\nseq2 (r2 0x10) (r3 0x10)\n")
same("Addr: 番地と数を混ぜて返す関数は普通の道", "mx : p n ?\n\tn < 1 : p\n\t7\nseq2 (mx 0x10 0) (mx 0x10 1)\n")
same("Addr: どの行も当たらず __ になりうる関数", "mu : p n ?\n\tn > 0 : p + n\nseq2 (mu 0x10 4) (mu 0x10 0)\n")
same("Addr: 番地を返して比べる", "ra : p n ? p + n\nrc : p ? (ra p 4) > 0x10 : 1\nrc 0x10\n")

# 番地(Addr)の実引数も速い道に乗る。番地の域の規則(外へ出たら __・* は __・答えが Addr)は普通の道と同じ答えになること
same("Addr: 番地を返す関数", "ra : p n ? p + n\nra 0x10 4\n")
same("Addr: 番地の差と掛け算", "rs : p q ? p - q\nrm : p n ? p * n\nseq2 (rs 0x20 0x10) (rm 0x10 2)\n")
same("Addr: 域の外へ出る足し引き", "ro : p n ? @(p + n)\nrn : p n ? (p - n) | 7\nseq2 (ro 0xFFFFFFFFFFFFFFF0 100) (rn 0x10 0x20)\n")
same("Addr: 比べと再帰で渡す", "rc : p n ?\n\tn < 1 : 0\n\tp > 0x8 : rc p (n - 1)\n\t1\nrc 0x10 5\n")
same("Addr: 書き込みの番地に p + i", "rw : p n i ?\n\ti >= n : 0\n\t((p + (i * 4)) # i) : rw p n (i + 1)\nseq2 (rw 0x600000 5 0) (@0x600008)\n")
same("Addr: 括りの仮引数に番地", "rd : [p] ? p + 1\nrd 0x10\n")
# --- 整数 op 番地(左が整数なら整数の域): 速い道ありとなしで同じ答え ---
INTADDR = "f : a n ?\n\tn < 1 : 0\n\t(n - a) + ((3 * a) + (n + (f a (n - 1))))\n"
for a_, n_ in (("0x10", 5), ("0", 4), ("0xFFFFFFFFFFFFFFF0", 3), ("0x7FFFFFFFFFFFFFFF", 6)):
    same(f"整数 op 番地 f {a_} {n_}", "`std.sn`@~\n" + INTADDR + f"println_int (f {a_} {n_})\n")
    same(f"整数 op 番地 f {a_} {n_} (--strict)", "`std.sn`@~\n" + INTADDR + f"println_int (f {a_} {n_})\n", flags=("--strict",))
same("整数 op 番地 は掛け算も(番地 * 整数 は普通の道の __)", "`std.sn`@~\ng : a n ?\n\tn < 1 : 0\n\t(a * n) + (g a (n - 1))\nprintln_int (g 0x10 3)\n")

# --- 番地を返す関数: 番地・整数・__ が混ざる物(X)と、番地の字面(0x…)。速い道ありとなし・既定と --strict で突き合わせる ---
MIXA = '`std.sn`@~\nf : a n ?\n\tn < 1 : a\n\tn > 100 : 7\n\tf (a + 4) (n - 1)\ng : a ?\n\ta > 0x20 : a\n\ta = 0x10 : __\n\ta - 1\nh : a ?\n\ta < 0x100 : 0\n\ta\nk : a n ?\n\tn < 1 : 5\n\ta + n\nprintln_int (f 0x10 5)\nprintln_int (f 0x10 500)\nprintln_int (g 0x30)\nprintln_int (g 0x10)\nprintln_int (g 0x18)\nprintln_int (h 0x50)\nprintln_int (h 0x500)\nprintln_int (k 0x10 0)\nprintln_int (k 0x10 3)\nprintln_int ((g 0x30) | 99)\nprintln_int ((g 0x10) | 99)\n'
MIXB = '`std.sn`@~\nh : a ?\n\ta < 0x100 : 0\n\ta\ng : a ?\n\ta > 0x20 : a\n\ta - 1\nw : n ?\n\tn < 1 : 0x10\n\tn < 3 : n + 0x10\n\t0x20 + n\nprintln_int (h 0x50)\nprintln_int (h 0x500)\nprintln_int (g 0x30)\nprintln_int (g 0x10)\nprintln_int (w 0)\nprintln_int (w 2)\nprintln_int (w 9)\nprintln_int ((0x10 + 0x20) - 0x08)\nprintln_int (5 - 0x10)\nprintln_int (0x10 - 0x20)\n'
for nm_, src_ in (("番地・整数が混ざる答え", MIXA), ("番地の字面と整数 op 番地", MIXB)):
    same(nm_, src_)
    same(nm_ + " (--strict)", src_, flags=("--strict",))
# 乱数で作った関数(番地・整数・__ の行、境界の値)を、速い道ありとなしで比べる(種は固定)
_rs = random.Random(7)
_AD = ["0", "1", "0x10", "0xFFFFFFFFFFFFFFFF", "0xFFFFFFFFFFFFFFF0", "0x7FFFFFFFFFFFFFFF", "0x8000000000000001", "0x500000"]
_IN = ["0", "1", "5", "(0 - 3)", "100"]
def _ex(d=0):
    r = _rs.random()
    if r < .3: return "a"
    if r < .45: return _rs.choice(_IN)
    if r < .6: return _rs.choice(_AD)
    if r < .8: return "(%s %s %s)" % (_ex(d + 1), _rs.choice("+-"), _ex(d + 1)) if d < 2 else "a"
    if r < .9: return "(%s * %s)" % (_ex(d + 1), _ex(d + 1)) if d < 2 else "n"
    return "n"
for _t in range(8):
    rows_ = ["\t%s %s %s : %s" % (_ex(1), _rs.choice(["<", ">", "=", "<=", ">="]), _ex(1), "__" if _rs.random() < .15 else _ex()) for _ in range(_rs.randint(1, 3))] + ["\t" + _ex()]
    src_ = "`std.sn`@~\nf : a n ?\n" + "\n".join(rows_) + "\n" + "".join("println_int ((f %s %s) | 99)\n" % (a_, n_) for a_ in _rs.sample(_AD, 3) for n_ in ("0", "3"))
    same(f"乱数の関数 {_t}", src_)
    same(f"乱数の関数 {_t} (--strict)", src_, flags=("--strict",))


# --- 混ざって返る関数の答えを式の中で使う(比べ・足し算・実引数) ---
XSRC = open("/tmp/b1f/m3.sn").read() if False else """`std.sn`@~
w : n ?
\tn < 1 : 0x10
\tn < 3 : n + 0x10
\t0x20 + n
cmpx : n ?
\t(w n) > 0x15 : 1
\t0
addx : n ?
\t(w n) + 4
subx : n ?
\t10 - (w n)
mulx : n ?
\t3 * (w n)
use : x ?
\tx + 1
argx : n ?
\tuse (w n)
seq3 (println_int (cmpx 0)) (println_int (cmpx 9)) (println_int (addx 0))
seq3 (println_int (addx 9)) (println_int (subx 9)) (println_int (mulx 9))
println_int (argx 0)
"""
for fl in ((), ("--strict",)):
    same("混ざる答えを式の中で " + "".join(fl), XSRC, flags=fl)

print("\n全部 ok" if not bad else f"\n{bad} 件 NG"); sys.exit(1 if bad else 0)
