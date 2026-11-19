import sys, os
sys.path.insert(0, "/tmp/strictmods"); sys.path.insert(1, "/mnt/user-data/outputs"); sys.setrecursionlimit(20000)
f = sys.argv[1]; sys.argv = [f] + sys.argv[2:]
src = open("/mnt/user-data/outputs/" + f if not f.startswith("/") else f, encoding="utf-8").read()
src = src.replace('os.path.join(HERE, "sign.py")', '"/tmp/strictmods/sign_strict.py"')
import re as _re
src = _re.sub(r'sign_asm\.generate\(sign_interp\.parse_source\((\w+)\)', r'sign_asm.generate(sign_asm.strict_rewrite(sign_interp.parse_source(\1))[0]', src)
os.chdir("/mnt/user-data/outputs")
ns = {"__file__": "/mnt/user-data/outputs/" + os.path.basename(f), "__name__": "__main__"}
exec(compile(src, f, "exec"), ns)
