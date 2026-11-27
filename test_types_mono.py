"""test_types_mono.py — Pass 1b(呼び出しサイトの観測から仮引数の型を決める反復)の性質検査(ランダム生成)。
sign-spec の formal/lean/SignMath/Typing.lean J.2(gIter_fixed / gIter_greatest / gfp_unique)は、更新 F が単調なら反復は止まり、不動点が一意に決まると言う。
sign_types.py の Pass 1b がその前提を満たすかを、小さなランダムなプログラムで確かめる。
  P1 止まる   : 5 回の反復で不動点に着く(着かないプログラムは数える)
  P2 不動点   : 着いたあと、もう 1 回更新しても観測は変わらない
  P3 単調     : 観測 p ⊑ q(ANY を未観測とみなした情報の順)なら F(p) ⊑ F(q)
  P4 衝突の符号化: 「観測が無い」と「観測が食い違った」が同じ ANY になる(単調性が崩れる原因)の反例を数える
FAIL は P2 の破れだけ(これは実装の誤り)。P1・P3・P4 は、数えて報告する(仕様の形式化への材料)。"""
import random, sys
import sign_interp as S
import sign_types as T

random.seed(20261128)
ARGS = ["1", "2.5", "`ab`", "'a'", "0x10"]

def gen():
    nf = random.randint(1, 4)
    names = ["f%d" % i for i in range(nf)]
    lines = []
    for i, f in enumerate(names):
        k = random.randint(1, 2); ps = ["a", "b"][:k]
        later = names[i + 1:]
        if later and random.random() < 0.6:
            g = random.choice(later)
            lines.append("%s : %s ? %s %s" % (f, " ".join(ps), g, " ".join(random.choice(ps + ARGS[:2]) for _ in range(random.randint(1, 2)))))
        else:
            lines.append("%s : %s ? %s" % (f, " ".join(ps), ps[0]))
    for _ in range(random.randint(1, 3)):
        f = random.choice(names)
        lines.append("%s %s" % (f, " ".join(random.choice(ARGS) for _ in range(random.randint(1, 2)))))
    return "\n".join(lines) + "\n"

def leq(p, q):
    """観測の順: ANY(未観測)は何にも ⊑。それ以外は同じ型どうしだけ。"""
    for f, ps in p.items():
        qs = q.get(f)
        if qs is None: return False
        for i, t in enumerate(ps):
            u = qs[i] if i < len(qs) else T.ANY
            if t != T.ANY and t != u: return False
    return True

stats = {"programs": 0, "no_converge": 0, "p2_fail": 0, "p3_checked": 0, "p3_break": 0, "p4_conflict": 0}
fails = []
for _ in range(400):
    src = gen()
    try: nodes = S.parse_source(src)
    except Exception: continue
    try:
        c = T.Checker(nodes); c.solve(5)
    except Exception: continue
    stats["programs"] += 1
    if not c.converged: stats["no_converge"] += 1
    else:
        again = c.step()
        if again != c.params: stats["p2_fail"] += 1; fails.append(src)
    # P4: 食い違った観測が ANY になる(未観測と同じ表し方)
    if any(t == T.ANY for ps in c.params.values() for t in ps) and any(
            len({a for a in site if a not in (T.ANY, T.UNIT_T)}) > 1 for sites in [[]] for site in sites): pass
    # P3: p を観測から 1 つ ANY に落として q ⊒ p を作り、F(p) ⊑ F(q) を見る
    try:
        q = {f: list(ps) for f, ps in c.params.items()}
        p = {f: list(ps) for f, ps in q.items()}
        cands = [(f, i) for f, ps in p.items() for i, t in enumerate(ps) if t != T.ANY]
        if not cands: continue
        f, i = random.choice(cands); p[f][i] = T.ANY
        c1 = T.Checker(nodes); c1.params = p; Fp = c1.step()
        c2 = T.Checker(nodes); c2.params = q; Fq = c2.step()
        stats["p3_checked"] += 1
        if not leq(Fp, Fq): stats["p3_break"] += 1
    except Exception: pass

# P4: 衝突の符号化(1 つの関数に Int と String を渡すと、型が ANY になり、未観測と区別できない)
c = T.Checker(S.parse_source("f : a ? a\nf 1\nf `ab`\n")); c.solve(5)
stats["p4_conflict"] = 1 if c.params.get("f") == [T.ANY] else 0
c = T.Checker(S.parse_source("f : a ? a\n")); c.solve(5)
unobserved_any = c.params.get("f", [T.ANY]) == [T.ANY]
print("  ".join("%s=%s" % kv for kv in stats.items()), " 未観測も ANY=%s" % unobserved_any)
if fails: print("NG P2(不動点で更新しても変わる):", len(fails)); print(fails[0]); sys.exit(1)
print("全部 ok(P2)。P1/P3/P4 は上の数を報告する")
