"""law_map.md の法則52・53(coproduct_spec R21・R27・R49・R84・R95・R128・R139)を `--strict` で見る。
52: 未定義の名前 qq と `!_` と分かる名前 w を入れ替えた綴りは、値が同じで、qq の側だけ name-undefined が書いた所ごとに1つ増える。
53: 点なしの頭の後ろの並びで w と w~ を入れ替えた綴りは、値が同じ。"""
import os, subprocess, sys, tempfile, shutil
HERE = os.path.dirname(os.path.abspath(__file__))
d = tempfile.mkdtemp()
src = open(os.path.join(HERE, "sign_interp.py"), encoding="utf-8").read().replace("if res and not STRICT_GATES: print(show(res[-1]))", "if res: print(show(res[-1]))")
open(os.path.join(d, "sign_interp.py"), "w", encoding="utf-8").write(src)
for n in ("std.sn", "sign_st.py"):
    if os.path.exists(os.path.join(HERE, n)): shutil.copy(os.path.join(HERE, n), d)
PRE = "pw : [a : 1]\nw : pw ' zz\ninc : x ? x + 1\n"
def run(body):
    f = os.path.join(d, "m.sn"); open(f, "w", encoding="utf-8").write(PRE + body + "\n\n")
    r = subprocess.run([sys.executable, os.path.join(d, "sign_interp.py"), "--strict", f], capture_output=True, text=True, cwd=d)
    return (r.stdout.strip().splitlines() or [""])[0], (r.stdout + r.stderr).count("name-undefined"), r.stdout + r.stderr
bad = 0
F52 = ["1 + %s", "inc %s", "[+] 1 %s", "[<] 2 %s", "[,] 1 %s", "[1 %s]", "(%s) | 3", "[+] %s 2"]
for f in F52:
    a, na, _ = run(f % "w"); b, nb, _ = run(f % "qq")
    if a != b or na != 0 or nb != 1: bad += 1; print("NG 52", f, repr(a), repr(b), na, nb)
F53 = ["[+] 1 %s", "[+] 1 %s 2", "[<] %s 5", "||_|| %s 3", "[+] %s", "||_|| %s"]
for f in F53:
    a, _, _ = run(f % "w"); b, _, _ = run(f % "w~")
    if a != b: bad += 1; print("NG 53", f, repr(a), repr(b))
print("全部 ok" if not bad else "NG %d 件" % bad); sys.exit(1 if bad else 0)
