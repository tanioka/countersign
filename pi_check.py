"""Raspberry Pi 実機での機械語の突き合わせ。
  python3 pi_check.py make DIR [N SEED]   DIR に cases/NNNN.s(linux 足場つきの asm)・cases/NNNN.t(源)・expected.tsv(strict 評価器とエミュレータの観測)・run.sh を作る
  python3 pi_check.py compare DIR         実機の出力(DIR/out/NNNN.out)を expected.tsv と突き合わせる(間違った答えがあれば exit 1)
実機側は DIR の run.sh(as・ld、または gcc が要る)だけを実行する。"""
import sys, os, random, json
import sign_interp as S, sign_asm, fuzz_sir as F
from fixblank import fix

def load_int_cases():
    here = os.path.dirname(os.path.abspath(__file__))
    src = open(os.path.join(here, "test_asm.py"), encoding="utf-8").read()
    ns = {}
    i_ = src.index("MAX, MIN1 = "); j_ = src.index("\n]\n", src.index("CASES = [")) + 3
    exec(src[i_:j_], ns)
    return [(nm, t) for nm, t in ns["CASES"]]

def make(d, n=300, seed=1):
    os.makedirs(os.path.join(d, "cases"), exist_ok=True)
    progs = [("case:" + nm, fix(t)) for nm, t in load_int_cases()]
    r = random.Random(seed)
    F.FLOW_RATE[0] = 0.3; F.LIST_RATE[0] = 0.3
    for k in range(n): progs.append((f"fuzz{seed}-{k}", fix(F.program(r))))
    rows = []; made = 0
    for nm, t in progs:
        a = F.obs_strict(t)
        sir_asm_ok = True
        try:
            sign_asm.STRICT[0] = True
            tree, rest = sign_asm.strict_rewrite(S.parse_source(t))
            if rest: continue
            asm = sign_asm.generate(tree, "linux")
        except BaseException: continue
        e = F.obs_asm(t, linux=True)
        idx = "%04d" % made; made += 1
        open(os.path.join(d, "cases", idx + ".s"), "w", encoding="utf-8").write(asm)
        open(os.path.join(d, "cases", idx + ".t"), "w", encoding="utf-8").write(t)
        rows.append([idx, nm, json.dumps(a), json.dumps(e)])
    with open(os.path.join(d, "expected.tsv"), "w", encoding="utf-8") as f:
        for r_ in rows: f.write("\t".join(x.replace("\t", " ").replace("\n", " ") for x in r_) + "\n")
    open(os.path.join(d, "run.sh"), "w", newline="\n").write(RUN_SH)
    print(f"{made} 件を {d} に作りました(うち strict が答える形 {sum(1 for r_ in rows if json.loads(r_[2])[0] != 'refuse')})")

RUN_SH = r'''#!/bin/sh
# Raspberry Pi(AArch64 の Linux)で、cases/*.s を組んで実行し、標準出力を out/NNNN.out に書く
cd "$(dirname "$0")" || exit 1
mkdir -p out build
uname -m > out/_arch.txt
if command -v as >/dev/null 2>&1 && command -v ld >/dev/null 2>&1; then BUILD=asld
elif command -v gcc >/dev/null 2>&1; then BUILD=gcc
else echo "as/ld も gcc も無い" >&2; exit 2; fi
n=0; bad=0
for s in cases/*.s; do
  b=$(basename "$s" .s)
  if [ "$BUILD" = asld ]; then
    as -o build/$b.o "$s" 2>build/$b.err && ld -o build/$b build/$b.o 2>>build/$b.err
  else
    gcc -nostdlib -static -o build/$b "$s" 2>build/$b.err
  fi
  if [ -x build/$b ]; then
    timeout 5 ./build/$b > out/$b.out 2>/dev/null; echo "exit=$?" >> out/$b.out
  else
    echo "BUILDFAIL" > out/$b.out; bad=$((bad+1))
  fi
  n=$((n+1))
done
echo "$n 件を実行、組めなかった $bad 件" | tee out/_summary.txt
'''

def compare(d):
    tot = {"一致": 0, "断り・罠(許容)": 0, "組めず": 0, "strict が断る": 0}; wrong = []
    for line in open(os.path.join(d, "expected.tsv"), encoding="utf-8"):
        idx, nm, a, e = line.rstrip("\n").split("\t")
        norm = lambda x: tuple(tuple(y) if isinstance(y, list) else y for y in json.loads(x))      # JSON は組を配列にするので戻す
        a = norm(a); e = norm(e)
        p = os.path.join(d, "out", idx + ".out")
        if not os.path.exists(p): tot["組めず"] += 1; continue
        txt = open(p, encoding="utf-8", errors="replace").read()
        if txt.startswith("BUILDFAIL"): tot["組めず"] += 1; continue
        body = txt.rsplit("exit=", 1)[0]; code = txt.rsplit("exit=", 1)[1].strip() if "exit=" in txt else "?"
        got = F._got(("exit", body))
        if a[0] == "refuse": tot["strict が断る"] += 1; continue
        if got[0] == "refuse" or code not in ("0",) and got[0] != "val": tot["断り・罠(許容)"] += 1; continue
        if got == a or (got[0] == "void" and a[0] == "void"): tot["一致"] += 1
        else: wrong.append((idx, nm, a, got, e))
    print(tot)
    for w in wrong[:20]: print("間違い:", w)
    print("間違った答え:", len(wrong))
    return 1 if wrong else 0

if __name__ == "__main__":
    c = sys.argv[1]
    if c == "make": make(sys.argv[2], int(sys.argv[3]) if len(sys.argv) > 3 else 300, int(sys.argv[4]) if len(sys.argv) > 4 else 1)
    elif c == "compare": raise SystemExit(compare(sys.argv[2]))
