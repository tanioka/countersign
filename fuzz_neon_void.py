"""fuzz_neon_void.py — `__` の持ち回り(Vector の割り算の 0 のレーン)の乱数試験: 処理系と --target=linux の通しを比べる。
使い方: python3 fuzz_neon_void.py 種 本数"""
import os, sys, random
HERE = os.path.dirname(os.path.abspath(__file__)); os.chdir(HERE); sys.path.insert(0, HERE)
seed = int(sys.argv[1]); N = int(sys.argv[2]); sys.argv = ["x"]
src = open("test_neon.py", encoding="utf-8").read().split("V1, V2 =")[0]
exec(compile(src, "tn", "exec"))
import sign_asm
def run_linux(prog):
    text = sign_asm.generate(sign_interp.parse_source(prog), target="linux")
    c = NeonCpu(text); c.r["sp"] = 0x7fff0000; c.run("_start", limit=80_000_000); return bytes(c.out).decode(), c.exit
rnd = random.Random(seed); n = bad = ref = voids = 0
def vec(): return "[%s]" % " ".join(rnd.choice(["0.0", "0.0", "1.0", "2.5", "0.1", "3.0"]) for _ in range(4))
def ex(d, vs):
    if d == 0 or rnd.random() < .25: return rnd.choice(vs)
    a, b = ex(d - 1, vs), ex(d - 1, vs)
    return "(%s %s %s)" % (a, rnd.choice("+-*//"), b)
for i in range(N):
    kind = rnd.random()
    if kind < .7:
        body = ex(3, ["a", "b", "c"]); args = [vec(), vec(), vec()]
        if rnd.random() < .3: body = "(%s) ' %d" % (body, rnd.randrange(4))
    else:                                    # Float と Vector を割り算の相手に
        body = ex(2, ["a", "b", "2.0", "0.0"]); args = [vec(), vec(), vec()]
    prog = "f : a b c ? %s\nf %s\n" % (body, " ".join(args))
    w = interp(prog)
    try: got = run_linux(prog)
    except (sign_neon.NeonError, sign_asm.AsmError): ref += 1; continue
    n += 1; voids += w == "__"
    if got != (w + "\n", 0): bad += 1; print("NG", repr(prog), got, w)
print("`__` の持ち回りの乱数: 比べた %d(うち結果が __: %d)、断り %d、不一致 %d" % (n, voids, ref, bad))
