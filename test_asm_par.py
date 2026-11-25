"""test_asm_par.py — --asm --par(sign_asmpar.py。純粋な整数関数の兄弟の呼び出しを、スレッドの池に渡す)。
疑似カーネルの協調スレッド(fake_kernel.py。clone(CLONE_THREAD)・futex・sched_yield・mmap)で、直列版と答えが同じか、
命令の途中でスレッドを強制的に切り替えても(preempt)同じか、軽い所は直列に戻るか、スレッドを作れない時は直列で動くかを確かめる。
本物の Linux・本物のスレッドではない(実機では未実行)。clang があれば、生成物が組み立てられることも確かめる。"""
import os, shutil, subprocess, sys, tempfile
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import emu_dev, fake_kernel, sign_asm, sign_interp
fails = 0
def check(name, got, want):
    global fails
    if got == want: print("ok ", name)
    else: fails += 1; print("NG ", name, "\n    want", repr(want), "\n    got ", repr(got))
CPU = emu_dev.load_cpu_class()["Cpu"]
LIMIT = 60_000_000
def build(src, par, target="linux"): return sign_asm.generate(sign_interp.parse_source(src), target, par=par)
def run(src, par=None, seed=None, every=None, **kw):
    k = fake_kernel.Kernel(); k.sched_seed = seed; k.thread_limit = LIMIT
    for a, v in kw.items(): setattr(k, a, v)
    class KC(CPU):
        def syscall(self, n): return k.handle(self, n)
    text = build(src, par); cpu = KC(text)
    if every: k.preempt(cpu, every)
    cpu.run("_start", limit=LIMIT)
    return cpu, k, text
def wsteps(cpu, k): return sum(c["cpu"].steps for c in getattr(k, "ctxs", []) if c["cpu"] is not cpu)

FIB = "fib : n ?\n\tn < 2 : n\n\t(fib (n - 1)) + (fib (n - 2))\n"
progs = {
    "fib 14 + fib 15": FIB + "(fib 14) + (fib 15)\n",
    "fib 17(再帰の中で分ける)": FIB + "fib 17\n",
    "積 fib 11 * fib 12": FIB + "(fib 11) * (fib 12)\n",
    "差 fib 16 - fib 14": FIB + "(fib 16) - (fib 14)\n",
    "2 引数": "g : a b ?\n\ta < 1 : b\n\t(g (a - 1) (b + 1)) + (g (a - 1) (b + 2))\ng 9 0\n",
    "別の関数の兄弟": FIB + "sq : n ? n * n\nw : n ? (sq (fib n)) + (fib (n + 1))\nw 12\n",
    "引数に式": FIB + "a : 5\n(fib (a + 8)) + (fib (a * 2 + 1))\n",
    "軽い": FIB + "(fib 3) + (fib 4)\n",
    "割り算": FIB + "(fib 15) / (fib 7)\n",
    "剰余": FIB + "(fib 16) % (fib 8)\n",
    "0 で割る(__)": FIB + "z : n ? n - n\n(fib 12) / (z 5)\n",
    "ビット and": FIB + "(fib 14) && (fib 13)\n",
    "シフト": FIB + "(fib 10) << (fib 5)\n",
    "混ぜた 右が式": FIB + "sq : n ? n * n\n(fib 16) + ((sq 12) * 2)\n",
    "混ぜた 左が式": FIB + "sq : n ? n * n\n((sq 12) * 2) + (fib 16)\n",
    "混ぜた 左が式 引き算": FIB + "sq : n ? n * n\n((sq 30) - (sq 3)) - (fib 16)\n",
    "混ぜた 右が式 メモリを読む": FIB + "0x7000000 # 5\nrd : n ? @0x7000000\n(fib 16) + (rd 1) + 3\n",
    "混ぜた 右が定数だけ": FIB + "(fib 16) + 3\n",
    "連なり + 4 個": FIB + "(fib 12) + (fib 13) + (fib 14) + (fib 15)\n",
    "連なり * 3 個": FIB + "(fib 9) * (fib 10) * (fib 11)\n",
    "連なり 混ぜた演算": FIB + "(fib 15) - (fib 13) + (fib 12) * (fib 6)\n",
    "連なり - 4 個": FIB + "(fib 16) - (fib 12) - (fib 11) - (fib 10)\n",
    "連なり 再帰の中": "h : n ?\n\tn < 2 : n\n\t(h (n - 1)) + (h (n - 2)) + (h (n - 3))\nh 15\n",
    "連なり 2 引数": "g : a b ?\n\ta < 1 : b\n\t(g (a - 1) (b + 1)) + (g (a - 1) (b + 2)) + (g (a - 1) (b + 3))\ng 7 0\n",
    "連なり / と %": FIB + "(fib 17) / (fib 5) % (fib 6)\n",
    "実引数の呼び出しどうし 2 個": FIB + "ad : a b ? a - b\nad (fib 16) (fib 14)\n",
    "実引数の呼び出しどうし 3 個": FIB + "t3 : a b c ? a * 10000 + b * 100 + c\nt3 (fib 8) (fib 9) (fib 10)\n",
    "実引数 呼び出し + 式": FIB + "ad : a b c ? a - b * c\nk : 7\nad (fib 16) (k + 1) (fib 12)\n",
    "実引数 再帰の中": "pl : a b ? a + b\nh : n ?\n\tn < 2 : n\n\tpl (h (n - 1)) (h (n - 2))\nh 15\n",
    "連なり 呼び出しでない項が混じる": FIB + "k : 5\n(fib 12) + k + (fib 13) + 7 + (fib 14)\n",
    "連なり 先頭が定数": FIB + "3 * (fib 10) - (fib 11) + (fib 9)\n",
    "連なり 最後が式": FIB + "k : 4\n(fib 14) + (fib 15) + (k * 2 + 1)\n",
    "実引数の中の呼び出し": FIB + "(fib ((fib 6) + 2)) + (fib 13)\n",
    "実引数の中の呼び出し 仕事に出す側": FIB + "sq : n ? n * n\nad : a b ? a - b\nad (fib (sq 4)) (fib (fib 7))\n",
    "実引数の式の中の呼び出し 2 個": FIB + "ad : a b ? a - b\nad ((fib 15) + 1) ((fib 14) * 2)\n",
    "実引数の式の中 3 引数": FIB + "t3 : a b c ? a * 100 + b * 10 + c\nt3 ((fib 8) + 1) 5 ((fib 7) * 2)\n",
    "実引数の式の中 末尾の自分への呼び": FIB + "g : n acc ?\n\tn < 1 : acc\n\tg (n - 1) (acc + (fib 10) + (fib 9))\ng 4 0\n",
    "木 積の和": FIB + "(fib 15) * 2 + (fib 14) * 3\n",
    "木 負と括りの中": FIB + "-((fib 15) * 2) + ((fib 14) - 5) * (fib 10)\n",
    "木 関数の中で仮引数と混ぜる": FIB + "g : n ? ((fib n) * 2) - ((fib (n - 1)) * 3) + n\ng 16\n",
    "木 割り算と余り": FIB + "((fib 16) / 3) + ((fib 15) % 7) * (fib 8)\n",
    "木 3 つの葉が別の段": FIB + "((fib 12) * 2 + 1) * ((fib 11) + 3) - (fib 13) * 4\n",
    "木 | の右は入れない": FIB + "g : n ? ((fib n) | 5) + ((fib (n - 1)) | 7) * 2\ng 14\n",
    "実引数 入れ子": FIB + "ad : a b ? a - b\nad (ad (fib 14) (fib 12)) (fib 13)\n",
}
for name, src in progs.items():
    base = run(src)[0]; want = base.out
    for n in (2, 3, 4, 8):
        ok = True
        for seed, every in ((None, None), (1, 11), (2, 29), (3, 7)):
            cpu, k, _ = run(src, n, seed, every)
            if (cpu.out, cpu.exit, k.thread_error is None if hasattr(k, "thread_error") else True) != (want, 0, True): ok = False; print("   NG", name, n, seed, every, cpu.out, cpu.exit, getattr(k, "thread_error", None))
        check("%s: --par=%d で 直列と答えが同じ(順番・強制切り替え 3 通り)" % (name, n), ok, True)

# 連なり: 溢れの罠・`__` は直列と同じ(左から元の演算で畳む)
pw = "pw : n ? n < 1 : 1 ; 3 * (pw (n - 1))\n"
tr = {
    "罠 途中の和": FIB + "big : n ? 9223372036854775800 + n\n(big 1) + (big 2) + (fib 12)\n",
    "罠 途中の積": FIB + "big : n ? 4611686018427387904 + n - n\n(big 1) * (big 2) * (fib 12)\n",
    "__ の割り算が途中": FIB + "z : n ? n - n\n(fib 12) / (z 5) + (fib 11) + (fib 10)\n",
}
def outcome(*a):
    try: c = run(*a)[0]; return (c.out, c.exit)
    except Exception as e: return ("例外", type(e).__name__)
for name, src_ in tr.items():
    b = outcome(src_); ok = True
    for n in (2, 4):
        for seed, every in ((None, None), (1, 11), (3, 7)):
            c = outcome(src_, n, seed, every)
            if c != b: ok = False; print("   NG", name, n, seed, every, c, b)
    check("%s: 直列と出力・終了(罠)が同じ(%r)" % (name, b), ok, True)
for name, src_ in {
    "実引数 罠(溢れ)": FIB + "big : n ? 9223372036854775800 + n\nad : a b ? a + b\nad (big 1) (big 2)\n",
    "実引数 __(0 で割る)": FIB + "z : n ? n - n\nad : a b ? a + b\nad (fib 12) ((fib 5) / (z 5))\n",
}.items():
    b = outcome(src_); ok = True
    for n in (2, 4):
        for seed, every in ((None, None), (1, 11), (3, 7)):
            c = outcome(src_, n, seed, every)
            if c != b: ok = False; print("   NG", name, n, seed, every, c, b)
    check("%s: 直列と出力・終了が同じ(%r)" % (name, b), ok, True)
LP = "lp : i acc ?\n\ti < 1 : acc\n\tlp (i - 1) (acc + i)\n"
cl = FIB + "k : 5\n(fib 15) + k + (fib 16) + 7\n"
cpu, k_, tx = run(cl, 4, 1, 17)
check("連なりに呼び出しでない項が混じっても、呼び出しは仕事に出る(答えが直列と同じ・労働者が計算)", (cpu.out == run(cl)[0].out, wsteps(cpu, k_) > 10000), (True, True))
import sign_asmpar
for L_ in (1000, 20000, 200000):          # --par-light=N(軽さの境。4095 を超えたら movz/movk で作る)でも答えと労働者の数は同じ
    sign_asmpar.LIGHT = L_
    cpu, k, tx = run(LP + "(lp 2000 0) + (lp 2000 0) + (lp 2000 0) + (lp 2000 0)\n", 4, 1, 17)
    check("--par-light=%d: 連なり(再帰しない 4 本)の答え 8004000・労働者 3 本・境の比べ(movz は 4095 超のとき)" % L_, (cpu.out, getattr(k, "threads_made", 0), "movz x15" in tx), (b"8004000\n", 3, L_ > 4095))
sign_asmpar.LIGHT = 1000
for n_ in (2, 4):          # 第104段(実機の結果): 重さの同じ 4 つの葉は、スレッド 2 本なら 2 つずつ・4 本なら 1 つずつ(行列に残る葉を先に奪う)
    cpu, k, tx = run(LP + "(lp 20000 0) + (lp 20000 0) + (lp 20000 0) + (lp 20000 0)\n", n_, 1, 17)
    ws = [c["cpu"].steps for c in k.ctxs if c["cpu"] is not cpu]; tot = cpu.steps + sum(ws)
    check("葉 4 つを --par=%d で: 答え 800040000・主の仕事の割合が 1/%d に近い(%.2f)" % (n_, n_, cpu.steps / tot), (cpu.out, abs(cpu.steps / tot - 1 / n_) < 0.08), (b"800040000\n", True))
ca = LP + "ad : a b ? a - b\nad (lp 3000 0) (lp 2000 0)\n"
cpu, k, _ = run(ca, 2, 1, 17)
check("実引数の呼び出しどうし: 1 つを仕事に出し(労働者 1 本・計算した)、答えは直列と同じ", (getattr(k, "threads_made", 0), wsteps(cpu, k) > 10000, cpu.out == run(ca)[0].out), (1, True, True))
check("実引数が呼び出し 1 つだけなら仕事に出さない(労働者 0 本)", getattr(run(LP + "ad : a b ? a - b\nad (lp 2000 0) 3\n", 4, 1, 17)[1], "threads_made", 0), 0)
cs = FIB + "(fib 13) + (fib 14) + (fib 15) + (fib 16)\n"
cpu, k, text = run(cs, 4, 1, 17)
check("連なり 4 個: 3 つを仕事に出し(submit の呼び出しが 3 つ。連なり 1 か所)・答え 3382+… と同じ", (cpu.out == run(cs)[0].out, text.count("bl _sign_par_submit") - 0 >= 3, wsteps(cpu, k) > 10000), (True, True, True))
check("連なり 4 個: 労働者を 3 本作る", run(cs, 4, 1, 17)[1].threads_made, 3)

# 本当に別のスレッドが仕事をしている
src = FIB + "(fib 14) + (fib 15)\n"
cpu, k, text = run(src, 4, 1, 17)
check("N=4: 労働者を 3 本作った(clone のフラグ・積み・TLS)", (k.threads_made, [c[0] for c in k.clones], all(c[1] & 15 == 0 and c[1] > 0 for c in k.clones), len({c[2] for c in k.clones})), (3, [0xD0F00] * 3, True, 3))
check("N=4: 積は 64 MiB の無名 mmap を 3 回", [(m[1], m[2], m[3]) for m in k.maps if m[3] & 0x20], [(0x4000000, 3, 0x24022)] * 3)
check("労働者が実際に計算した(命令数 > 10000)", wsteps(cpu, k) > 10000, True)
check("futex は WAIT(128)・WAKE(129)の 2 種類だけ", {f[0] for f in k.futexes} <= {0, 1}, True)
cm = FIB + "sq : n ? n * n\n((sq 12) * 2) + (fib 17)\n"
cpu, k, tx = run(cm, 4, 1, 17)
check("片方だけ呼び出し(左が式)でも右の呼び出しを仕事に出す(答えが同じ・労働者が計算)", (cpu.out == run(cm)[0].out, wsteps(cpu, k) > 10000), (True, True))
LP = "lp : i acc ?\n\ti < 1 : acc\n\tlp (i - 1) (acc + i)\n"
check("右が定数だけなら仕事に出さない(労働者 0 本)", getattr(run(LP + "(lp 2000 0) + 3\n", 4, 1, 17)[1], "threads_made", 0), 0)
cpu, k, _ = run(LP + "(lp 3000 0) + ((lp 2000 0) * 2)\n", 2, 1, 17)
check("呼び出し + 呼び出しを含む式(再帰の兄弟が無い関数でも)仕事に出す: 労働者 1 本・答え 4501500+… と同じ", (getattr(k, "threads_made", 0), cpu.out), (1, run(LP + "(lp 3000 0) + ((lp 2000 0) * 2)\n")[0].out))
check("N=2: 労働者は 1 本", run(src, 2, 1, 17)[1].threads_made, 1)
check("終了は exit_group(94)で、直列版の exit(93)は使わない", ("mov x8, #94" in text, "mov x8, #93" in text), (True, False))

# 軽い所は 3 回で直列に戻る: 100 回回しても仕事に出すのは数回だけ
def loopsrc(n): return FIB + "drv : i acc ?\n\ti < 1 : acc\n\tdrv (i - 1) (acc + ((fib 3) + (fib 4)))\ndrv %d 0\n" % n
w100 = sum(1 for f in run(loopsrc(100), 4)[1].futexes if f[0] == 1); w400 = sum(1 for f in run(loopsrc(400), 4)[1].futexes if f[0] == 1)
cpu, k, _ = run(loopsrc(100), 4, 1, 13)
check("軽い式の繰り返しは直列に戻る(答えは 500。100 回でも 400 回でも仕事に出す回数は同じで 10 回以下)", (cpu.out.strip(), w100 == w400, w100 <= 10), (b"500", True, True))

# 第106段: リストの要素の呼び出し・値が計算で決まる定義(`a : fib 16`)・既定値のある関数(局所の値)・Int でない仮引数
LPS = "lp : n acc ?\n\tn < 1 : acc\n\tlp (n - 1) (acc + n % 7)\n"
SM = "sm : l i ?\n\ti >= ||l|| : 0\n\t(l ' i) + (sm l (i + 1))\n"
G106 = "g :\n\t\tn\n\t\ta : fib n\n\t\tb : fib (n - 1)\n\t? a + b\n"
def interp(src):
    d = tempfile.mkdtemp(); p = os.path.join(d, "x.sn"); open(p, "w").write(src)
    return subprocess.run([sys.executable, os.path.join(HERE, "sign.py"), p], capture_output=True, text=True).stdout
def submits(text): return text.split("_sign_par_boot:")[0].count("bl _sign_par_submit")
cases106 = {
    "リストの要素の呼び出し(最上位の印字)": (LPS + "(lp 3000 0) (lp 2000 0)\n", 1),
    "リストの要素を引数に": (LPS + "sm2 : l ? (l ' 0) + (l ' 1)\nsm2 ((lp 3000 0) (lp 2000 0))\n", 1),
    "関数の返す器の要素": (LPS + "f : n ? (lp n 0) (lp (n - 1) 0) (lp (n - 2) 0)\nf 3000\n", 1),
    "最上位の定義 a : fib n (2 つ)": (FIB + "a : fib 16\nb : fib 15\na + b\n", 1),
    "最上位の定義を関数から": (FIB + "a : fib 12\nh : n ? n + a\nh 3\n", 0),
    "最上位の定義を式の中で2回": (FIB + "a : fib 12\na + a * 2\n", 0),
    "最上位の定義が定義を使う": (FIB + "a : fib 12\nb : (a + (fib 10))\nb\n", 0),
    "定義だけのファイル(最後の値)": (FIB + "a : fib 10\n", 0),
    "既定値(局所の値) 基本": (FIB + G106 + "g 14\n", 1),
    "既定値 全部渡す": (FIB + G106 + "g 14 3 4\n", 0),
    "既定値が前の既定値を使う": (FIB + "g :\n\t\tn\n\t\ta : fib n\n\t\tb : a + 1\n\t? a * b\ng 10\n", 1),
    "既定値のある関数の再帰": ("lp :\n\t\tn\n\t\tacc\n\t\tc : n % 3\n\t?\n\t\tn < 1 : acc\n\t\tlp (n - 1) (acc + c)\nlp 20 0\n", 0),
    "既定値のある関数を式の中で": (FIB + G106 + "(g 12) + (g 11)\n", 1),
    "既定値の実引数を名前に置いて": (FIB + G106 + "x : fib 6\ng x\n", 1),
    "リストの仮引数の関数どうし": (SM + "xs : 1 2 3 4 5\nys : 10 20\n(sm xs 0) + (sm ys 0) + (sm xs 3)\n", 1),
    "リストを渡す関数の中で": (SM + "xs : 1 2 3 4 5\nf : l ? (sm l 0) + (sm l 2)\nf xs\n", 1),
    "文字列の仮引数": ("ln : s i ?\n\ti >= ||s|| : 0\n\t1 + (ln s (i + 1))\ns1 : `hello`\ns2 : `abc`\n(ln s1 0) + (ln s2 0)\n", 1),
    "Int とリストの仮引数が混ざる": ("wt : l k i ?\n\ti >= ||l|| : 0\n\t(k * (l ' i)) + (wt l k (i + 1))\nxs : 1 2 3\n(wt xs 2 0) + (wt xs 3 1)\n", 1),
    "末尾の切り出しで食う関数": ("st : l ?\n\t||l|| < 1 : 0\n\t(l ' 0) + (st (l ' 1~))\nxs : 1 2 3 4 5\nys : 10 20 30\n(st xs) + (st ys)\n", 1),
    "Char の仮引数(関数の中で)": ("cnt : s c i ?\n\ti >= ||s|| : 0\n\t(s ' i) = c : 1 + (cnt s c (i + 1))\n\tcnt s c (i + 1)\nw : `banana`\nf : s c ? (cnt s c 0) + (cnt s c 2)\nf w (w ' 1)\n", 1),
    "Char の実引数が文字列の要素 w ' 1": ("cnt : s c i ?\n\ti >= ||s|| : 0\n\t(s ' i) = c : 1 + (cnt s c (i + 1))\n\tcnt s c (i + 1)\nw : `banana`\nv : `xyzx`\n(cnt w (w ' 1) 0) + (cnt v (v ' 0) 0)\n", 1),
    "Char の実引数が仮引数の文字列の要素": ("cnt : s c i ?\n\ti >= ||s|| : 0\n\t(s ' i) = c : 1 + (cnt s c (i + 1))\n\tcnt s c (i + 1)\nw : `banana`\nf : s k ? (cnt s (s ' k) 0) + (cnt s (s ' 0) 0)\nf w 1\n", 1),
    "Char の実引数が範囲の外(__)なら仕事に出さず答えは同じ": ("cnt : s c i ?\n\ti >= ||s|| : 0\n\t(s ' i) = c : 1 + (cnt s c (i + 1))\n\tcnt s c (i + 1)\nw : `banana`\n(cnt w (w ' 9) 0) + (cnt w (w ' 1) 0)\n", 0),
    "実引数が溢れで __ になる呼び出し(包みが見て答えは __)": (LPS + "w : n d ? (lp n 0) + d\nm : x ? x * 4611686018427387904\n(w 3000 (m 3)) + (w 2000 (m 1))\n", 1),
    "答えが __ になる呼び出し(足す・先)": (LPS + "w : n d ? (lp n 0) / d\n(w 3000 0) + (w 2000 5)\n", 1),
    "答えが __ になる呼び出し(足す・後)": (LPS + "w : n d ? (lp n 0) / d\n(w 3000 5) + (w 2000 0)\n", 1),
    "答えが __ になる呼び出し(どちらも)": (LPS + "w : n d ? (lp n 0) / d\n(w 3000 0) + (w 2000 0)\n", 1),
    "答えが __ になる呼び出し(かける・引く・3 本)": (LPS + "w : n d ? (lp n 0) / d\n((w 3000 0) * (w 2000 5)) + ((w 3000 5) - (w 2000 0)) + (w 1000 0)\n", 1),
    "答えが __ になる呼び出しが並びの要素": (LPS + "w : n d ? (lp n 0) / d\n(w 3000 0) (w 2000 5) (w 1000 7)\n", 1),
    "答えが __ になる定義(最上位)": (LPS + "w : n d ? (lp n 0) / d\na : w 3000 0\nb : w 2000 5\nc : a * b\nc + a\n", 1),
    "答えが __ になる定義を関数から": (LPS + "w : n d ? (lp n 0) / d\na : w 3000 0\nb : w 2000 5\nh : k ? k + a\nh 1\n", 1),
    "答えが __ になる定義の印字": (LPS + "w : n d ? (lp n 0) / d\na : w 3000 0\na\n", 0),
    "実引数の中の呼び出し(2 本・段に分ける)": (LPS + "g : n ? lp n 0\nf : m ? (lp m 1) + 1\n(f (g 3000)) + (f (g 2000))\n", 2),
    "実引数の中の呼び出し(3 本)": (LPS + "g : n ? lp n 0\nf : m ? (lp m 1) + 1\n(f (g 3000)) + (f (g 2000)) + (f (g 1000))\n", 2),
    "実引数の中の式つき": (LPS + "g : n ? lp n 0\nf : m ? (lp m 1) + 1\n(f ((g 3000) + 1)) + (f ((g 2000) * 2))\n", 2),
    "実引数の中の呼び出し(3 段)": (LPS + "g : n ? lp n 0\nf : m ? (lp m 1) + 1\n(f (f (g 3000))) + (f (f (g 2000)))\n", 2),
    "実引数の中の呼び出しと素の呼び出し": (LPS + "g : n ? lp n 0\nf : m ? (lp m 1) + 1\n(f (g 3000)) + (g 2000)\n", 1),
    "実引数の中の呼び出しを呼び出しの実引数に": (LPS + "g : n ? lp n 0\nf : m ? (lp m 1) + 1\nad : a b ? a - b\nad (f (g 3000)) (f (g 2000))\n", 2),
    "実引数の中の呼び出しが並びの要素": (LPS + "g : n ? lp n 0\nf : m ? (lp m 1) + 1\n(f (g 3000)) (f (g 2000))\n", 2),
    "実引数の中の呼び出しが定義": (LPS + "g : n ? lp n 0\nf : m ? (lp m 1) + 1\na : f (g 3000)\nb : f (g 2000)\na + b\n", 2),
    "実引数の中の呼び出しが __ になる": (LPS + "g : n d ? (lp n 0) / d\nf : m ? (lp m 1) + 1\n(f (g 3000 5)) + (f (g 2000 3))\n", 0),   # 内側が __ になりうる(割る数が字面でない)ので、外側の実引数が __ になりうる: 仕事に出さず直列(答えは同じ)
    "比べの両側が呼び出し(値)": (LPS + "(lp 2000 0) < (lp 3000 0)\n", 1),
    "比べの両側が呼び出し(外れ)": (LPS + "(lp 3000 0) < (lp 2000 0)\n", 1),
    "比べの両側が呼び出し(枝の条件)": (LPS + "f : n ?\n\t(lp n 0) > (lp (n - 1) 0) : 1\n\t0\nf 3000\n", 1),
    "比べ = の両側が呼び出し": (LPS + "f : n ?\n\t(lp n 0) = (lp n 0) : 7\n\t0\nf 2000\n", 1),
    "比べの両側が __ になりうる呼び出し": (LPS + "w : n d ? (lp n 0) / d\n(w 3000 0) != (w 2000 5)\n", 1),
    "比べの両側が入れ子の呼び出し": (LPS + "g : n ? lp n 0\nf : m ? (lp m 1) + 1\n(f (g 2000)) < (f (g 3000))\n", 2),
    "仮引数が 5 つ": ("p5 : a b c d e ?\n\ta < 1 : e\n\tp5 (a - 1) b c d (e + b + c + d)\n(p5 3000 1 2 3 0) + (p5 2000 1 1 1 0)\n", 1),
    "仮引数が 7 つ": ("p7 : a b c d e f g ?\n\ta < 1 : g\n\tp7 (a - 1) b c d e f (g + b + c + d + e + f)\n(p7 3000 1 2 3 4 5 0) + (p7 2000 1 1 1 1 1 0)\n", 1),
    "入れ子の器の仮引数": ("tot : ls i ?\n\ti >= ||ls|| : 0\n\t||ls ' i|| + (tot ls (i + 1))\nxs : [1 2] [3 4 5]\nys : [1 1] [2 2] [3 3]\n(tot xs 0) + (tot ys 0)\n", 1),
    "入れ子の器を関数の中で": ("tot : ls i ?\n\ti >= ||ls|| : 0\n\t||ls ' i|| + (tot ls (i + 1))\nxs : [1 2] [3 4 5]\nf : l ? (tot l 0) + (tot l 1)\nf xs\n", 1),
    "器を返す最上位の定義(使う所へ書き込む)": ("mk : n ? n (n + 1) (n + 2)\nxs : mk 3\nys : mk 7\n(xs ' 0) + (ys ' 2) + ||xs||\n", 0),
    "器を返す最上位の定義を関数から": (SM + "mk : n ? n (n + 1) (n + 2)\nxs : mk 3\nf : k ? (sm xs 0) + k\nf 4\n", 0),
    "器を返す最上位の定義の印字": ("mk : n ? n (n + 1) (n + 2)\nxs : mk 3\nxs\n", 0),
    "リストの関数の呼び出しを定義に": (SM + "xs : 1 2 3\nys : 4 5 6\na : sm xs 0\nb : sm ys 0\na * b\n", 1),
}
for name, (s_, wantsub) in cases106.items():
    want = interp(s_).strip()
    c0, k0, t0 = run(s_)
    cpu, k, text = run(s_, 4, 1, 17)
    ok_out = (cpu.out.decode().strip() == want and c0.out.decode().strip() == want)
    check("%s: 処理系・直列・並列の答えが同じ(%s)" % (name, want.replace("\n", " ")), ok_out, True)
    if wantsub: check("%s: 仕事に出す所が %d 以上ある" % (name, wantsub), submits(text) >= wantsub, True)
    else: check("%s: 直列と同じで、この式自身は仕事に出さない(あっても内部の再帰だけ)" % name, cpu.out == c0.out, True)
for src_, why in ((FIB + "g :\n\t\tn\n\t\ta : fib n\n\t? a\ng (fib 5)\n", "既定値が使う実引数に呼び出し"), (FIB + "m : __\nq : fib (m)\nq\n", "__ になる右辺"), (FIB + "t : n\n\t\ta : 1\n\t? a\nt 1\n", "")):
    if not why: continue
    try: build(src_, 4); r = "通った"
    except sign_asm.AsmError as e: r = "断った"
    check("%s は断る(黙って違う答えにしない)" % why, r, "断った")

# 第106段の形を、命令の途中の強制切り替え(12 通り)でも
bad = 0
for nm, s_ in (("リストの仮引数", SM + "xs : 1 2 3 4 5\nys : 10 20\n(sm xs 0) + (sm ys 0) + (sm xs 3)\n"),
               ("最上位の定義", FIB + "a : fib 14\nb : fib 13\nc : fib 12\na + b * c\n"),
               ("既定値", FIB + G106 + "(g 12) + (g 11)\n"),
               ("リストの要素", LPS + "(lp 600 0) (lp 400 0) (lp 200 0)\n"),
               ("実引数の中の呼び出し", LPS + "g : n ? lp n 0\nf : m ? (lp m 1) + 1\n((f (g 600)) + (f (g 400))) * ((f (g 300)) - (g 200))\n"),
               ("比べの両側", LPS + "f : n ?\n\t(lp n 0) > (lp (n - 1) 0) : 1\n\t0\n(f 600) + (f 300) + ((lp 200 0) < (lp 400 0))\n"),
               ("__ になる呼び出し", LPS + "w : n d ? (lp n 0) / d\n((w 600 0) + (w 400 5)) * ((w 300 3) - (w 200 0))\n")):
    base = run(s_)[0].out
    for seed in range(12):
        cpu, k, _ = run(s_, 4, seed, 5 + seed % 11)
        if cpu.out != base or getattr(k, "thread_error", None): bad += 1; print("   NG", nm, seed, cpu.out, base)
check("第106段の形は 12 通りの切り替えでも直列と同じ答えでデッドロックなし", bad, 0)

# 多めの乱数の切り替え
bad = 0
for seed in range(25):
    cpu, k, _ = run(FIB + "(fib 11) + (fib 12)\n", 3, seed, 5 + seed % 13)
    if cpu.out != b"233\n" or getattr(k, "thread_error", None): bad += 1; print("   NG seed", seed, cpu.out, getattr(k, "thread_error", None))
check("25 通りの切り替えで fib 11 + fib 12 = 233 とデッドロックなし", bad, 0)

# スレッドを作れない・積みが取れない → 直列で動く
for what in ("clone_fail", "anon_fail"):
    cpu, k, _ = run(src, 4, None, None, **{what: True})
    check("%s のとき直列で動く(答え・労働者 0)" % what, (cpu.out, getattr(k, "threads_made", 0)), (b"987\n", 0))

# 並列にしない式: メモリを触る・__ になりうる・単独の呼び出し
nop = {
    "メモリを読む": "0x7000000 # 5\nrd : n ?\n\tn < 1 : @0x7000000\n\t(rd (n - 1)) + (rd (n - 1))\nrd 3\n",
    "単独の呼び出し": FIB + "fib 12\n" if False else "sq : n ? n * n\nsq 12\n",
}
for name, s_ in nop.items():
    cpu, k, text = run(s_, 4)
    base = run(s_)[0]
    check("%s: 直列と同じ答えで、仕事に出さない" % name, (cpu.out == base.out, "_sign_par_submit" in text.split("_sign_par_boot:")[0]), (True, False))

# 誤用
try: build(FIB + "fib 3\n", 4, "bare"); r = "通った"
except sign_asm.AsmError as e: r = "断った"
check("--par は --target=linux だけ", r, "断った")
# clang
if shutil.which("clang"):
    d = tempfile.mkdtemp(); s_ = os.path.join(d, "p.s"); open(s_, "w").write(build(FIB + "(fib 14) + (fib 15)\n", 4))
    rr = subprocess.run(["clang", "--target=aarch64-linux-gnu", "-c", s_, "-o", os.path.join(d, "a.o")], capture_output=True, text=True)
    check("clang で組み立てられる(--par)", (rr.returncode, rr.stderr.strip()), (0, ""))
    if shutil.which("ld.lld"):
        open(os.path.join(d, "p.sn"), "w").write(FIB + "(fib 14) + (fib 15)\n")
        rr = subprocess.run([sys.executable, os.path.join(HERE, "sign.py"), "--asm", os.path.join(d, "p.sn"), "--par=4", "--elf=" + os.path.join(d, "p")], capture_output=True, text=True)
        check("--elf で静的な ELF までできる", (rr.returncode, os.path.exists(os.path.join(d, "p"))), (0, True))
else: print("-- clang が無いので、本物のアセンブラでの確認は省く")
print("\n全部 ok" if not fails else "\n失敗 %d 件" % fails); sys.exit(1 if fails else 0)
