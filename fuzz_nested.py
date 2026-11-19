"""fuzz_nested.py — 入れ子の並びの定数の添字・長さ(`((x 2) 3) ' 1`、`(((x 2) 3) ' 0) ' 1`)の差分ファジング。処理系と asm 版を突き合わせる。
使い方: python3 fuzz_nested.py [seed] [本数]"""
import os, sys, random
os.chdir(os.path.dirname(os.path.abspath(__file__))); sys.path.insert(0, ".")
src_t = open("test_asm.py", encoding="utf-8").read().split("MAX, MIN1 =")[0]
exec(compile(src_t.replace("__file__", repr(os.path.abspath("test_asm.py"))), "h", "exec"))
rnd = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 1); N = int(sys.argv[2]) if len(sys.argv) > 2 else 200
def prog():
    consts = ["c%d" % i for i in range(rnd.randint(0, 2))]; L = ["%s : %d" % (c, rnd.choice([0, 1, 4, 9, -3])) for c in consts]
    params = rnd.choice([["x"], ["x", "y"]])
    def leaf(): return rnd.choice(params + consts + [str(rnd.choice([0, 3, 7])), "(0 - 2)"])
    def lst(d):
        n = rnd.randint(2, 4)
        return "(" + " ".join(lst(d - 1) if d > 0 and rnd.random() < 0.4 else leaf() for _ in range(n)) + ")"
    def idx(): return rnd.choice([0, 1, 2, 3, 5, -1, -2, -6])
    def ix(k): return "(0 - %d)" % -k if k < 0 else str(k)
    r = rnd.random()
    if r < 0.35:                                        # 入れ子の並びを選ぶ形(結果が並び。位置は静的に決まる)
        n = rnd.randint(2, 4); j = rnd.randrange(n)
        sub = lambda: "(" + " ".join(leaf() for _ in range(rnd.randint(2, 3))) + ")"
        outer = "(" + " ".join(sub() if i == j else (sub() if rnd.random() < 0.3 else leaf()) for i in range(n)) + ")"
        jj = j if rnd.random() < 0.5 else j - n
        pick = "%s ' %s" % (outer, ix(jj))
        body = rnd.choice([pick, pick, "len (%s)" % pick, "(%s) ' %s" % (pick, ix(rnd.choice([0, 1, -1])))])
        if "len (" in body: L.insert(0, "len : a ? ||a||")
    elif r < 0.55: body = "%s ' %s" % (lst(2), ix(idx()))
    elif r < 0.7: body = "||%s||" % lst(2)
    elif r < 0.9: body = "(%s ' %s) ' %s" % (lst(2), ix(idx()), ix(idx()))
    else: body = "((%s ' %s) ' %s) ' %s" % (lst(3), ix(idx()), ix(idx()), ix(idx()))
    L.append("f : %s ? %s" % (" ".join(params), body))
    L.append("f " + " ".join(rnd.choice(["7", "0", "(0 - 1)", "100", "__"]) for _ in params))
    return "\n".join(L) + "\n"
import emu_dev
bad = []; n = 0; ref = {}; lst = 0
for i in range(N):
    s = prog()
    open("_t_fz.sn", "w", encoding="utf-8").write(s)
    try: want, got = emu_dev.compare("_t_fz.sn", [], b"")          # 標準出力どうしを比べる(結果が並びでもよい)
    except sign_asm.AsmError as e: ref[str(e)[:46]] = ref.get(str(e)[:46], 0) + 1; continue
    except Exception as e: want, got = "?", ("例外", str(e)[:40])
    n += 1; lst += want.startswith("[")
    if got != want: bad.append((s, want, got))
os.remove("_t_fz.sn")
print("比べた", n, "(うち並びの結果", lst, ") 断り", sum(ref.values()), "食い違い", len(bad))
for k, v in sorted(ref.items(), key=lambda x: -x[1])[:4]: print("  断り", v, k)
for s, w, g in bad[:8]: print(repr(s), "\n   処理系", w, "asm", g)
