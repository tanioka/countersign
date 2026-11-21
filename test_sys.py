#!/usr/bin/env python3
"""システムコール装置(sign_sys.py)の試験。python test_sys.py"""
import os, sys, subprocess, tempfile, time
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); sys.setrecursionlimit(20000)
import sign_interp as S, sign_sys as Y

bad = 0
def check(name, got, want):
    global bad
    ok = got == want; bad += not ok
    print(("ok  " if ok else "NG  ") + name + ("" if ok else f"\n    得た: {got!r}\n    期待: {want!r}"))

_parent = tempfile.mkdtemp(); root = os.path.join(_parent, "work"); os.makedirs(os.path.join(root, "sub"))          # 親は空の新しい物(共有の /tmp に昔の x.txt があっても「外へ書けていない」の確かめが狂わない)
outside = tempfile.mkdtemp(); open(os.path.join(outside, "secret.txt"), "w").write("secret")
open(os.path.join(root, "a.txt"), "wb").write(b"abcdef")
try: os.symlink(outside, os.path.join(root, "link")); HAVE_LINK = True
except (OSError, NotImplementedError): HAVE_LINK = False
S.DEVICES.clear(); S.MEMORY.clear()
dev = Y.Sys(root); S.DEVICES.append(dev)
B = Y.SYS_BASE
def put(addr, data):
    for i, b in enumerate(data): S.MEMORY[addr + 4 * i] = b
def get(addr, n): return bytes(S.MEMORY.get(addr + 4 * i, 0) for i in range(n))
def call(nr, a0=0, a1=0, a2=0):
    for off, v in ((Y.NR, nr), (Y.A0, a0), (Y.A1, a1), (Y.A2, a2)): S.write_addr(B + off, v)
    S.write_addr(B + Y.GO, 1)
    return S.ev_read(B + Y.RET) if hasattr(S, "ev_read") else dev.read(Y.RET)
PATH, BUF = 0x600000, 0x610000
def op(name, mode):
    put(PATH, name.encode()); return call(3, PATH, len(name.encode()), mode)

# --- ファイル ---
fd = op("a.txt", 0)
check("OPEN(読む)は fd(3 以上)", fd >= 3, True)
check("READ は読んだバイト数", call(1, fd, BUF, 4), 4)
check("READ の中身", get(BUF, 4), b"abcd")
check("READ は続きから(残り 2 バイト)", (call(1, fd, BUF, 10), get(BUF, 2)), (2, b"ef"))
check("READ は終わりで 0", call(1, fd, BUF, 10), 0)
check("CLOSE", call(4, fd), 0)
check("閉じた fd は EBADF", call(1, fd, BUF, 1), -Y.EBADF)
check("開いていない fd の CLOSE は EBADF", call(4, 99), -Y.EBADF)
fd = op("new.txt", 1); put(BUF, b"hello"); check("WRITE は書いたバイト数", call(2, fd, BUF, 5), 5); call(4, fd)
check("書いたファイルの中身(本物のファイル)", open(os.path.join(root, "new.txt"), "rb").read(), b"hello")
fd = op("new.txt", 2); put(BUF, b" world"); call(2, fd, BUF, 6); call(4, fd)
check("足して書く(mode 2)", open(os.path.join(root, "new.txt"), "rb").read(), b"hello world")
fd = op("new.txt", 1); call(4, fd)
check("書く(mode 1)は作り直す(空になる)", os.path.getsize(os.path.join(root, "new.txt")), 0)
check("SIZE", (put(PATH, b"a.txt"), call(7, PATH, 5))[1], 6)
check("サブフォルダのファイル", (op("sub/x.txt", 1) >= 3), True)
check("見つからない読みは ENOENT", op("nothing.txt", 0), -Y.ENOENT)
check("SIZE の見つからないは ENOENT", (put(PATH, b"zzz"), call(7, PATH, 3))[1], -Y.ENOENT)
check("フォルダを開くのは EINVAL", op("sub", 0) in (-Y.EINVAL, -Y.EACCES, -Y.EIO), True)
# --- 作業フォルダの外 ---
check("../ で外へ出るのは EACCES", op("../x.txt", 1), -Y.EACCES)
check("途中の .. で外へ出るのも EACCES", op("sub/../../x.txt", 1), -Y.EACCES)
check("絶対パスは EACCES", op(os.path.join(outside, "secret.txt"), 0), -Y.EACCES)
check("外へは書けていない", os.path.exists(os.path.join(os.path.dirname(root), "x.txt")), False)
if HAVE_LINK: check("外を指すシンボリックリンクは EACCES", op("link/secret.txt", 0), -Y.EACCES)
check("中の .. は通る(sub/../a.txt)", op("sub/../a.txt", 0) >= 3, True)
# --- 引数 ---
check("長さ 0 のパスは EINVAL", call(3, PATH, 0, 0), -Y.EINVAL)
check("長すぎるパスは EINVAL", call(3, PATH, 5000, 0), -Y.EINVAL)
check("おかしい mode は EINVAL", (put(PATH, b"a.txt"), call(3, PATH, 5, 9))[1], -Y.EINVAL)
check("バイトでない値(300)のバッファは EINVAL", (S.MEMORY.__setitem__(BUF, 300), call(2, 1, BUF, 1))[1], -Y.EINVAL)
check("負の長さは EINVAL", call(2, 1, BUF, -1), -Y.EINVAL)
check("知らない番号は ENOSYS", call(99), -Y.ENOSYS)
for _ in range(20): fd = op("a.txt", 0)
check("開きすぎは EMFILE(同時に 16 まで)", fd, -Y.EMFILE)
dev.release()
# --- 時刻 ---
t = call(5); check("TIME_S は今の秒", abs(t - time.time()) < 3, True)
t = call(6); check("TIME_MS は今のミリ秒", abs(t - time.time() * 1000) < 3000, True)
# --- 標準入出力(本物のプロセス) ---
def run_sn(src, data="", args=(), cwd=None):
    d = cwd or tempfile.mkdtemp(); p = os.path.join(d, "t.sn"); open(p, "w", encoding="utf-8").write(src)
    return subprocess.run([sys.executable, os.path.join(HERE, "sign.py"), p, *args], input=data.encode(), capture_output=True, cwd=d, timeout=60)
demo = open(os.path.join(HERE, "sys_demo.sn"), encoding="utf-8").read()
d = tempfile.mkdtemp(); r = run_sn(demo, args=["--sys"], cwd=d)
check("見本: 書いて読み直して標準出力へ出し、大きさを答える", (r.stdout.decode(), r.stderr.decode()), ("hello from Sign\n16\n", ""))
check("見本: out.txt が作業フォルダにできる", open(os.path.join(d, "out.txt")).read(), "hello from Sign\n")
d2 = tempfile.mkdtemp(); r = run_sn(demo, args=[], cwd=d2)
check("--sys が無ければ装置が無く、ファイルはできない", os.path.exists(os.path.join(d2, "out.txt")), False)
prelude = open(os.path.join(HERE, "sys_demo.sn"), encoding="utf-8").read().split("`1. out.txt")[0]
echo = prelude + "main : z ? seq3 (sys 2 1 BUF (sys 1 0 BUF 64)) 0 0\nmain 0\n"
r = run_sn(echo, data="stdin line\n", args=["--sys"])
check("標準入力を READ して、標準出力へ WRITE する", r.stdout.decode().startswith("stdin line\n"), True)
r = run_sn(prelude + "main : z ? seq3 (sys 2 2 BUF (sys 1 0 BUF 64)) 0 0\nmain 0\n", data="to err\n", args=["--sys"])
check("fd 2 は標準エラーへ", (r.stderr.decode().startswith("to err"), "to err" in r.stdout.decode()), (True, False))
d = tempfile.mkdtemp(); os.makedirs(os.path.join(d, "box"))
r = run_sn(demo, args=["--sys=box"], cwd=d)
check("--sys=DIR で作業フォルダを替える(DIR の中にできる)", (os.path.exists(os.path.join(d, "box", "out.txt")), os.path.exists(os.path.join(d, "out.txt"))), (True, False))
# --- ゲーム機から ---
import sign_console as sc
disp, timer, inp = sc.setup("null", True, "", "")
check("ゲーム機: setup に sys_root を渡すと装置が付く", any(isinstance(x, Y.Sys) for x in S.DEVICES), True)
disp, timer, inp = sc.setup("null", True, "")
check("ゲーム機: 渡さなければ付かない", any(isinstance(x, Y.Sys) for x in S.DEVICES), False)
print("\n" + ("全部通った" if not bad else f"{bad} 件 食い違い")); sys.exit(1 if bad else 0)
