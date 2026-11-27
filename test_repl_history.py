"""test_repl_history.py — REPL で ↑(ヒストリー)・履歴ファイルが使える(Linux/macOS。readline が要る。Windows は読み飛ばす)。"""
import os, select, sys, tempfile, time
HERE = os.path.dirname(os.path.abspath(__file__))
if os.name != "posix": print("(posix でないので読み飛ばし)"); sys.exit(0)
try: import readline  # noqa
except ImportError: print("(readline が無いので読み飛ばし)"); sys.exit(0)
import pty
home = tempfile.mkdtemp()
fails = 0
def check(name, got, want):
    global fails
    if got == want: print("ok ", name)
    else: fails += 1; print("NG ", name, "\n   got ", repr(got), "\n   want", repr(want))
pid, fd = pty.fork()
if pid == 0:
    os.environ["HOME"] = home; os.environ["TERM"] = "xterm"
    os.chdir(HERE); os.execvp(sys.executable, [sys.executable, "sign.py"])
def rd(t=1.5):
    out = b""; end = time.time() + t
    while time.time() < end:
        r, _, _ = select.select([fd], [], [], 0.2)
        if r:
            try: out += os.read(fd, 4096)
            except OSError: break
    return out.decode(errors="replace")
rd(2); os.write(fd, b"1 + 2\n"); rd()
os.write(fd, b"\x1b[A\n"); out = rd()                      # ↑ で前の入力が戻り、Enter でもう一度走る
check("↑ で前の入力 `1 + 2` を呼び戻して実行できる(答え 3 が出る)", "1 + 2\r\n3\r\n" in out, True)
os.write(fd, b"\x04"); rd(1)
try: os.waitpid(pid, 0)
except OSError: pass
h = os.path.join(home, ".sign_history")
txt = open(h, encoding="utf-8", errors="replace").read().replace("\\040", " ") if os.path.exists(h) else ""      # readline の版で空白の書き方が違う(\\040 か空白)
check("履歴ファイル ~/.sign_history に残る", "1 + 2" in txt, True)
if "1 + 2" not in txt: print("   ディレクトリ:", os.listdir(home), repr(txt[:80]))
print("%d 件 NG" % fails if fails else "全部 ok"); sys.exit(1 if fails else 0)
