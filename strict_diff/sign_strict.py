#!/usr/bin/env python3
# sign.py の代わり: 読みは --strict、最後の行の値も出す(比較用)。`__` は `!_` に、トップレベルの定義の間には空行を入れる
import sys, os, tempfile, io, contextlib
sys.path.insert(0, "/tmp/strictmods"); sys.path.insert(1, "/mnt/user-data/outputs"); sys.setrecursionlimit(20000)
args = sys.argv[1:]; path = args[0]
t = open(path, encoding="utf-8").read().replace("__", "!_")
out = []
for ln in t.split("\n"):
    if out and ln and not ln[0].isspace() and out[-1].strip(): out.append("")
    out.append(ln)
fd, tmp = tempfile.mkstemp(suffix=".sn"); os.write(fd, "\n".join(out).encode()); os.close(fd)
import sign_interp_sv as S
sys.argv = ["sign_strict", tmp, "--strict"] + args[1:]
buf = io.StringIO()
try:
    with contextlib.redirect_stdout(buf): S._cli()
finally:
    sys.stdout.write(buf.getvalue().replace("!_", "__")); os.unlink(tmp)
