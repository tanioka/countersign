"""test_inline.py — 特殊化(sign_inline.py)と、括りの仮引数の残り `[h ~t]` の AArch64 出力の試験。
各プログラムを (a) 処理系(sign_interp.py、既定モード) と (b) AArch64 出力(疑似カーネル)で走らせ、最後の行が同じことを見る。
断る形は、エラーの文に決まった言葉が入っていることを見る。"""
import subprocess, sys, tempfile, os
import emu_dev, fake_kernel, sign_asm, sign_interp, sign_inline
CPU = emu_dev.load_cpu_class()["Cpu"]
FAIL = []

def asm_run(src, par=None, limit=30_000_000):
    k = fake_kernel.Kernel(); k.thread_limit = limit
    class KC(CPU):
        def syscall(self, n): return k.handle(self, n)
    text = sign_asm.generate(sign_interp.parse_source(src), "linux", par=par)
    cpu = KC(text)
    try: cpu.run("_start", limit=limit)
    except SystemExit: pass
    return cpu.out.decode("utf-8", "replace").strip(), text

def interp(src):
    d = tempfile.mkdtemp(); p = os.path.join(d, "t.sn"); open(p, "w", encoding="utf-8").write(src)
    r = subprocess.run([sys.executable, os.path.join(os.path.dirname(os.path.abspath(__file__)), "sign_interp.py"), p], capture_output=True, text=True)
    return r.stdout.strip().splitlines()[-1] if r.stdout.strip() else ""

def check(name, ok, detail=""):
    if not ok: FAIL.append(name); print("NG  %s  %s" % (name, detail))

SAME = [
 ("多種類: 長さ(リストと文字列)", "sz : x ? ||x||\n(sz [1, 2, 3]) + (sz `abc`)\n"),
 ("多種類: Int を受ける関数と別の関数", "f : x ? ||x||\ng : x ? x + 1\n(f [1, 2]) + (g 4)\n"),
 ("多種類: 2 番目の引数だけ", "h : x y ? x + (||y||)\n(h 1 [1,2,3]) + (h 2 `ab`)\n"),
 ("多種類: 再帰", "cnt : x n ?\n\tn = 0 : 0\n\t(||x||) + (cnt x (n - 1))\n(cnt [1,2] 3) + (cnt `abc` 2)\n"),
 ("多種類: 2 つの仮引数", "q : a b ? (||a||) * 10 + (||b||)\n(q [1,2] `abc`) + (q `x` [1,2,3,4])\n"),
 ("多種類: 経由する関数", "len2 : x ? ||x||\nw : x ? (len2 x) + 1\n(w [1,2]) + (w `abc`)\n"),
 ("多種類: リストと規則", "sz : x ? ||x||\n(sz [1, 2, 3]) + (sz [1 ~ 5])\n"),
 ("部分適用", "add : a b ? a + b\nadd3 : add 3\nadd3 5\n"),
 ("部分適用を 2 か所", "add : a b ? a + b\nadd3 : add 3\n(add3 1) + (add3 2) * 10\n"),
 ("部分適用の上の部分適用", "f : a b c ? a + b * c\nf1 : f 1\nf12 : f1 2\nf12 5\n"),
 ("部分適用して 2 引数が残る", "f : a b c ? a * 100 + b * 10 + c\ng : f 7\ng 8 9\n"),
 ("部分適用を高階関数へ渡す", "add : a b ? a + b\nadd3 : add 3\nap : f x ? @f x\nap $add3 4\n"),
 ("部分適用を 2 回通す", "add : a b ? a + b\nadd3 : add 3\ntw : f x ? @f (@f x)\ntw $add3 4\n"),
 ("名前の関数を渡す", "sq : x ? x * x\nap : f x ? @f x\nap $sq 3\n"),
 ("2 回呼ぶ", "sq : x ? x * x\ntw : f x ? @f (@f x)\ntw $sq 3\n"),
 ("別の高階関数へ渡す", "sq : x ? x * x\nap : f x ? @f x\nap2 : f x ? ap f x\nap2 $sq 3\n"),
 ("別の高階関数へ 2 段", "sq : x ? x * x\nap : f x ? @f x\nap2 : f x ? ap f x\nap3 : f x ? ap2 f (ap f x)\nap3 $sq 2\n"),
 ("囲む仮引数を捕まえる", "ap : f x ? @f x\ng : k ? ap $[x ? x + k] 10\ng 5\n"),
 ("捕まえた関数を別の高階関数へ", "ap : f x ? @f x\ntw : f x ? ap f (ap f x)\ng : a b ? tw $[x ? x * a + b] 1\ng 3 4\n"),
 ("切片 右", "ap : f x ? @f x\nap $[+ 2] 3\n"),
 ("切片 左", "ap : f x ? @f x\nap $[2 -] 3\n"),
 ("切片が仮引数を捕まえる", "ap : f x ? @f x\ng : k ? ap $[* k] 7\ng 6\n"),
 ("2 引数の関数", "add : a b ? a + b\nap2 : f x y ? @f x y\nap2 $add 3 4\n"),
 ("名前の無い 2 引数", "ap2 : f x y ? @f x y\nap2 $[p q ? p * q + 1] 3 4\n"),
 ("関数を 2 つ渡す", "sq : x ? x * x\ninc : x ? x + 1\ncomp : f g x ? @f (@g x)\n(comp $sq $inc 3) + (comp $inc $sq 3)\n"),
 ("同じ実体を 2 か所から", "ap : f x ? @f x\nsq : x ? x * x\n(ap $sq 2) + (ap $sq 3) + (ap $[* 10] 1)\n"),
 ("残る仮引数がゼロ", "sq : x ? x * x\napply5 : ref ? @ref 5\napply5 $sq\n"),
 ("残る仮引数がゼロ(式の中)", "sq : x ? x * x\napply5 : ref ? @ref 5\n(apply5 $sq) + 1\n"),
 ("再帰する高階関数(回数)", "rep : f n x ?\n\tn = 0 : x\n\trep f (n - 1) (@f x)\ninc : x ? x + 1\nrep $inc 1000 5\n"),
 ("map(残りの括り)", "sq : x ? x * x\nmap : f [h ~t] ? (@f h) (map f t)~\nmap $sq (1 2 3)\n"),
 ("map に名前の無い関数", "map : f [h ~t] ? (@f h) (map f t)~\nmap $[+ 2] (1 2 3 4)\n"),
 ("map が仮引数を捕まえる", "map : f [h ~t] ? (@f h) (map f t)~\nsc : k xs ? map $[x ? x * k] xs\nsc 3 (1 2 3)\n"),
 ("fold(末尾再帰)", "fold : f acc [h ~t] ?\n\t||t|| = 0 : @f acc h\n\tfold f (@f acc h) t\nadd : a b ? a + b\nfold $add 0 (1 2 3 4 5)\n"),
 ("畳んで足す", "sum : f [h ~t] ? (@f h) + (sum f t)\nsq : x ? x * x\nsum $sq (1 2 3)\n"),
 ("map と fold の組み合わせ", "map : f [h ~t] ? (@f h) (map f t)~\nfold : f acc [h ~t] ?\n\t||t|| = 0 : @f acc h\n\tfold f (@f acc h) t\nadd : a b ? a + b\nfold $add 0 (map $[* 2] (1 2 3))\n"),
 ("残り: 和", "sum : [h ~t] ? h + (sum t)\nsum (1 2 3 4)\n"),
 ("残り: 作り直す", "inc : [h ~t] ? (h + 1) (inc t)~\ninc (1 2 3 4)\n"),
 ("残り: 角括弧の実引数", "inc : [h ~t] ? (h + 1) (inc t)~\ninc [1 2 3 4]\n"),
 ("残り: 前に 2 つ", "f : [a b ~t] ? a + b + ||t||\nf (1 2 3 4 5)\n"),
 ("残り: 残りが空", "f : [a b ~t] ? a + b\nf (1 2)\n"),
 ("残り: 残りだけ", "f : [~s] ? ||s||\nf (1 2 3)\n"),
 ("残り: ほかの仮引数と", "g : n [h ~t] ? n * h + (g n t)\ng 3 (1 2 3)\n"),
 ("残り: 累積", "len : [h ~t] acc ?\n\t||t|| = 0 : acc + 1\n\tlen t (acc + 1)\nlen (5 6 7) 0\n"),
]
for name, src in SAME:
    want = interp(src)
    try: got, _ = asm_run(src)
    except Exception as e: got = "ERR " + str(e)[:150]
    check(name, got == want, "処理系 %r / AArch64 %r" % (want, got))

# 並列と一緒に(答えが変わらない)
PAR = "fib : n ?\n\tn < 2 : n\n\t(fib (n - 1)) + (fib (n - 2))\nap : f x ? @f x\n(ap $fib 15) + (ap $fib 14)\n"
want = interp(PAR)
for par in (None, 2, 4):
    try: got, _ = asm_run(PAR, par=par)
    except Exception as e: got = "ERR " + str(e)[:150]
    check("並列 par=%s" % par, got == want, "処理系 %r / AArch64 %r" % (want, got))

# 書き換えた木の形
nodes = sign_inline.specialize(sign_interp.parse_source("sq : x ? x * x\nap : f x ? @f x\nap $sq 3\n"))
names = [n[1] for n in nodes if n[0] == "def"]
check("実体の名前 ap$sq", "ap$sq" in names and "ap" not in names, str(names))
check("呼び出しの付け替え", nodes[-1] == ("seq", [("id", "ap$sq"), ("lit", 3)]), str(nodes[-1]))
src0 = "f : x ? x + 1\nf 3\n"; n0 = sign_interp.parse_source(src0)
check("対象が無ければ同じ木", sign_inline.specialize(n0) is n0)
_, text = asm_run("sq : x ? x * x\nap : f x ? @f x\nap $sq 3\n")
check("間接呼び出しが無い", "blr" not in text.split("_start:")[0])

# 断る形(名指し)
REFUSE = [
 ("部分適用の実引数が名前", "add : a b ? a + b\nk : 4\nadd4 : add k\nadd4 5\n", "字面でない定義"),
 ("関数を値として持ち回る", "sq : x ? x * x\nk : f x ? f + x\nk $sq 3\n", "値として持ち回る"),
 ("当てる引数が足りない", "add : a b ? a + b\nap : f x ? @f x\nap $add 3\n", "しか当てていません"),
 ("引数を当てない @", "sq : x ? x * x\nk : f x ? (@f) + x\nk $sq 3\n", "引数を当てていません"),
 ("外の局所の名前", "ap : f x ? @f x\ng : k ? ap $[x ? x + zz] 1\ng 2\n", "外の局所の名前"),
 ("残りの後ろに名前", "f : [~i l] ? l\nf (1 2 3)\n", "残りの後ろの名前"),
]
for name, src, word in REFUSE:
    try: asm_run(src); msg = "(断らなかった)"
    except sign_asm.AsmError as e: msg = str(e)
    except Exception as e: msg = "別の例外 %s: %s" % (type(e).__name__, str(e)[:100])
    check("断る: " + name, word in msg, msg[:160])

print("全部 ok" if not FAIL else "失敗 %d 件: %s" % (len(FAIL), ", ".join(FAIL)))
sys.exit(1 if FAIL else 0)
