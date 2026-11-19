"""fuzz_seqparam.py — 仮引数・定数・字面を要素に持つ並びの添字と長さ(`(x c 4) ' 1`、`||(x y)||`)の差分ファジング。処理系と asm 版を突き合わせる。
使い方: python3 fuzz_seqparam.py [seed] [本数]"""
import os, sys, random
os.chdir(os.path.dirname(os.path.abspath(__file__))); sys.path.insert(0, ".")
src_t = open("test_asm.py", encoding="utf-8").read().split("MAX, MIN1 =")[0]
exec(compile(src_t.replace("__file__", repr(os.path.abspath("test_asm.py"))), "h", "exec"))
rnd = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 1); N = int(sys.argv[2]) if len(sys.argv) > 2 else 200
def prog():
    consts = ["c%d" % i for i in range(rnd.randint(0, 2))]; L = ["%s : %d" % (c, rnd.choice([0, 1, 4, 9, -3])) for c in consts]
    params = rnd.choice([["x"], ["x", "y"]])
    use_g = rnd.random() < 0.5
    if use_g: L.append("g : a ? (a %s %d)" % (rnd.choice("<>="), rnd.choice([0, 3, 7])))
    use_h = rnd.random() < 0.6
    if use_h: L.append("h : a ? (a %s %d) + 1" % (rnd.choice("<>"), rnd.choice([0, 3, 7])))
    def opd(): return rnd.choice(params + consts + [str(rnd.choice([0, 3, 7]))])
    def item():
        r = rnd.random()
        if r < 0.25: return "(%s %s %s)" % (opd(), rnd.choice(["<", ">", "="]), opd())            # `__` になりうる要素(比べ)
        if r < 0.4 and use_g: return "(g %s)" % opd()                                          # `__` を返しうる関数の呼び
        if r < 0.5: return "(%s %s %s)" % (opd(), rnd.choice("+-*"), opd())
        return rnd.choice(params + consts + [str(rnd.choice([0, 3, 7])), "(0 - 2)"])
    def seq():
        r = rnd.random()
        if use_h and r < 0.2: return "(h %s %s)" % (opd(), " ".join(item() for _ in range(rnd.randint(1, 3))))      # 先頭の呼びと余りの実引数
        if use_h and r < 0.3: return "(%s h)" % opd()                                                         # 逆適用
        n = rnd.choice([2, 3, 4, 4, 9, 12])
        return "(" + " ".join(item() for _ in range(n)) + ")"
    k = rnd.choice([0, 1, 2, 3, 5, -1, -2, -5])
    dyn = rnd.random() < 0.5                                       # 添字を定数でなく、実行時の式にする
    if dyn:
        params = params + ["i"]
        k = rnd.choice(["i", "(i - 2)", "(i * 0 - 1)", "(i < 2)", "(0 - i)"])
    kk = "%s" % k if dyn else "(0 - %d)" % -k if k < 0 else "%d" % k
    body = rnd.choice(["%s ' %s" % (seq(), kk), "||%s||" % seq(), "(%s ' %s) + %s" % (seq(), kk, rnd.choice(params)), "%s ' %s" % (seq(), kk)])
    L.append("f : %s ? %s" % (" ".join(params), body))
    arg = lambda: rnd.choice(["7", "0", "(0 - 1)", "100", "__"])
    L.append("f " + " ".join(arg() for _ in params))
    return "\n".join(L) + "\n"
bad = []; n = 0; ref = {}
for i in range(N):
    s = prog()
    try: want = interp(s)
    except Exception: continue
    try: got = run_asm(sign_asm.generate(sign_interp.parse_source(s)))
    except sign_asm.AsmError as e: ref[str(e)[:50]] = ref.get(str(e)[:50], 0) + 1; continue
    except Exception as e: got = ("例外", str(e)[:40])
    n += 1
    if got != want: bad.append((s, want, got))
print("比べた", n, "断り", sum(ref.values()), "食い違い", len(bad))
for k, v in sorted(ref.items(), key=lambda x: -x[1])[:5]: print("  断り", v, k)
for s, w, g in bad[:8]: print(repr(s), "\n   処理系", w, "asm", g)
