"""fuzz_voidlist.py — `__` の定数を要素に持つ並び(`(c 4) ' 0`、`||(c 4 5)||`、`[c 4 5]`)の差分ファジング。処理系と asm 版(emu_dev)の標準出力を突き合わせる。使い方: python3 fuzz_voidlist.py seed 本数"""
import sys, os, random
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); os.chdir(HERE)
import emu_dev, sign_asm
rnd = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 1); N = int(sys.argv[2]) if len(sys.argv) > 2 else 80
def prog():
    L = ["v0 : (5 < 3)", "v1 : (2 != 2)", "n0 : %d" % rnd.randint(0, 9), "n1 : (n0 + %d)" % rnd.randint(1, 5)]
    pool = ["v0", "v1", "n0", "n1", "7", "(n0 * 2)", "__"]
    items = [rnd.choice(pool) for _ in range(rnd.randint(1, 5))]
    body = "(%s)" % " ".join(items)
    k = rnd.random()
    if k < 0.3: e = "%s ' %d" % (body, rnd.choice([0, 1, 2, 3, -1]))
    elif k < 0.45: e = "||%s||" % body
    elif k < 0.6: e = body
    elif k < 0.7: e = "[%s]" % " ".join(items)
    elif k < 0.75: e = "g : x ? (%s) ' %d\ng %d" % (" ".join(["x"] + items), rnd.choice([0, 1, 2]), rnd.randint(0, 9))
    elif k < 0.85:
        sc = rnd.choice(["x ' %d" % rnd.choice([0, 1, -1, 2]), "||x||", "(x + 1) ' 0", "(x < 3) ' 0", "||(x < 3)||", "(x v0) ' %d" % rnd.choice([0, 1]), "||(v0 x v1)||"])
        e = "g : x ? %s\ng %d" % (sc, rnd.randint(0, 9))
    else: e = "(%s ' %d) + 1" % (body, rnd.choice([0, 1]))
    return "\n".join(L) + "\n" + e + "\n"
bad = []; n = 0; ref = {}
for i in range(N):
    s = prog(); open("_t_vl.sn", "w", encoding="utf-8").write(s)
    try: want, got = emu_dev.compare("_t_vl.sn", [], b"")
    except sign_asm.AsmError as e: ref[str(e)[:44]] = ref.get(str(e)[:44], 0) + 1; continue
    except Exception as e: want, got = "処理系の失敗", str(e)[:40]
    n += 1
    if want != got: bad.append((s, want, got))
os.remove("_t_vl.sn")
print("比べた", n, "断り", sum(ref.values()), "食い違い", len(bad))
for k, v in sorted(ref.items(), key=lambda x: -x[1])[:4]: print("  断り", v, k)
for s, w, g in bad[:6]: print(repr(s), "\n  処理系", repr(w)[:80], "asm", repr(g)[:80])
