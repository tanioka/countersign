"""`--emit-st`(sign_st.py): documents(type_system.md §6)の綴りで、公開(#)のデータだけを書き出す。"""
import os, subprocess, sys, tempfile
HERE = os.path.dirname(os.path.abspath(__file__))
SRC = "#pi : 3.14\n#greeting : `hello`\n#bump : n ? n + 1\n#p : [\n\tx : 1\n\ty : 2\n]\n#xs : [1 2 3]\n#ch : 0u0061\n#uart : 0x9000000\n#addrs : [0x10 0x20]\nprivate : 5\n#q : [\n\tname : `add`\n\ttier : 14\n\tassoc : 0\n]\n#mixed : [1 [2 3]]\n#empty : [ ]\n"
WANT = ["#pi : Float=3.14", "#greeting : String=`hello`", "#p : Struct{`x` : Int=1 , 0  `y` : Int=2 , 1}", "#xs : List(Int)", "#ch : Char=`a`", "#uart : Address=0x9000000", "#addrs : List(Address)",
        "#q : Struct{`assoc` : Int=0 , 2  `name` : String=`add` , 0  `tier` : Int=14 , 1}", "#mixed : List"]
d = tempfile.mkdtemp(); bad = 0
def run(args, cwd=d): return subprocess.run([sys.executable, os.path.join(HERE, "sign.py")] + args, capture_output=True, text=True, cwd=cwd)
open(os.path.join(d, "a.sn"), "w", encoding="utf-8").write(SRC)
r = run(["--emit-st", "a.sn"])
st = open(os.path.join(d, "a.st"), encoding="utf-8").read() if os.path.exists(os.path.join(d, "a.st")) else ""
lines = [l for l in st.splitlines() if l and not l.startswith("`")]
for w in WANT:
    if w not in lines: bad += 1; print("NG 欲しい行が無い:", w)
for l in lines:
    if l.startswith("#bump") or l.startswith("private") or l.startswith("#private"): bad += 1; print("NG 出してはいけない行:", l)
if not any("bump" in l and l.startswith("`") for l in st.splitlines()): bad += 1; print("NG 関数をコメントで言っていない")
if "bump" not in r.stderr: bad += 1; print("NG 書かなかった名前を言っていない")
r2 = run(["--emit-st", "a.sn", "-o", "out.st"])
if not os.path.exists(os.path.join(d, "out.st")): bad += 1; print("NG -o が効かない")
for args, why in ((["--emit-st", "nofile.sn"], "ファイルが無い"), (["--emit-st"], "引数が無い"), (["--emit-st", "a.sn", "-o"], "-o の後が無い")):
    r3 = run(args)
    if r3.returncode == 0 or "Traceback" in r3.stderr: bad += 1; print("NG", why, r3.returncode, r3.stderr[:80])
open(os.path.join(d, "b.sn"), "w", encoding="utf-8").write("#s : `a\nb`\n#t : 1\n")
open(os.path.join(d, "c.sn"), "w", encoding="utf-8").write("#u : 5\nu 1 2 +\n")
r4 = run(["--emit-st", "c.sn"])
if "Traceback" in r4.stderr: bad += 1; print("NG 落ちた")
print("全部 ok" if not bad else "NG %d 件" % bad); sys.exit(1 if bad else 0)
