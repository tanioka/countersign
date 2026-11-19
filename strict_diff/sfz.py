# 使い方: python3 /tmp/sfz.py fuzz_xxx.py 種 本数   — 処理系の答えを --strict の読みで取って、asm と比べる
import sys, re, os
sys.setrecursionlimit(20000)
os.chdir("/mnt/user-data/outputs"); sys.path.insert(0, "/mnt/user-data/outputs")
f = sys.argv[1]; sys.argv = [f] + sys.argv[2:]
src = open(f, encoding="utf-8").read()
import sign_interp as S
def sinterp(s):
    t = s.replace("__", "!_")
    out = []
    for ln in t.split("\n"):
        if out and ln and not ln[0].isspace() and out[-1].strip(): out.append("")
        out.append(ln)
    t = "\n".join(out)
    S.STRICT_GATES = True; S.WARNINGS.clear()
    try: S.INTCHK[0] = True
    except Exception: pass
    try:
        r = S.run(t)
    except BaseException as e:
        S.STRICT_GATES = False
        m = str(e)
        if "Int の溢れ" in m or "罠" in m: return ("trap", None)
        raise
    v = S.show(r[-1]) if r else "!_"
    S.STRICT_GATES = False
    if v == "!_": return ("ok", "__")
    return ("ok", int(v))
SSTAT = {"refused": 0}
def wrapped(s):
    try: return sinterp(s)
    except Exception as e:
        SSTAT["refused"] += 1; SSTAT.setdefault("why", {}); k = str(e).split("\n")[0][:40]; SSTAT["why"][k] = SSTAT["why"].get(k, 0) + 1
        raise
src = src.replace("interp(s)", "wrapped(s)")
import re as _re
src = _re.sub(r"sign_asm\.generate\(sign_interp\.parse_source\((\w+)\)", r"sign_asm.generate(sign_asm.strict_rewrite(sign_interp.parse_source(\1))[0]", src)
ns = {"__file__": os.path.abspath(f), "__name__": "__main__", "wrapped": wrapped}
try: exec(compile(src, f, "exec"), ns)
finally: print("strict 断り", SSTAT["refused"], sorted(SSTAT.get("why", {}).items(), key=lambda x: -x[1])[:4])
