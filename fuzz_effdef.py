"""fuzz_effdef.py — 出力を含む値の定義(`h : println `x``)の差分ファジング。処理系と asm 版(emu_dev)で標準出力を突き合わせる。使い方: python3 fuzz_effdef.py seed 本数"""
import sys, os, random
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); os.chdir(HERE)
import emu_dev, sign_asm
rnd = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 1); N = int(sys.argv[2]) if len(sys.argv) > 2 else 60
def prog():
    L = ["`std.sn`@~"]; names = []; ints = []
    for i in range(rnd.randint(1, 4)):
        k = rnd.choice(["str", "str", "int", "seq", "ival"])
        nm = "h%d" % i
        if k == "str": L.append("%s : println `%s`" % (nm, rnd.choice(["x", "ab", "q"]))); names.append(nm)
        elif k == "seq": L.append("%s : seq3 (print `%s`) (print `%s`) %d" % (nm, rnd.choice("ab"), rnd.choice("cd"), rnd.randint(0, 9))); names.append(nm)
        elif k == "ival": L.append("%s : println_int (%s %s %d)" % (nm, rnd.choice(ints + ["3", "4"]), rnd.choice("+-*"), rnd.randint(0, 9))); names.append(nm)
        else: L.append("%s : %d" % (nm, rnd.randint(0, 20))); ints.append(nm)
    k = rnd.random()
    if k < 0.2: pass
    elif k < 0.5 and names: L.append(rnd.choice(names))
    elif k < 0.8 and names: L.append("seq3 %s %s %d" % (rnd.choice(names), rnd.choice(names), rnd.randint(0, 9)))
    elif k < 0.9 and names: L.append("(%s) %s %d" % (rnd.choice(names), rnd.choice("+-*"), rnd.randint(0, 9)))
    else:
        L.append("g : n ? seq3 %s (println_int n) 0" % (rnd.choice(names) if names else "0")); L.append("g %d" % rnd.randint(0, 9))
    return "\n".join(L) + "\n"
bad = []; n = 0; ref = 0
for i in range(N):
    s = prog(); open("_t_eff.sn", "w", encoding="utf-8").write(s)
    try: want, got = emu_dev.compare("_t_eff.sn", [], b"")
    except sign_asm.AsmError: ref += 1; continue
    except Exception as e: want, got = "処理系の失敗", str(e)[:40]
    n += 1
    if want != got: bad.append((s, want, got))
os.remove("_t_eff.sn")
print("比べた", n, "断り", ref, "食い違い", len(bad))
for s, w, g in bad[:6]: print(repr(s), "\n  処理系", repr(w)[:80], "asm", repr(g)[:80])
