"""test_types_pass1a.py — Pass 1a(名前の種類。自己参照・相互参照は Atom に倒す)が、Typing.lean J.2(c) の言う
「名前を読み直す順をどう選んでも、不動点で止まれば答えは同じ」を満たすかを、小さなランダムな相互参照のプログラムで確かめる。
定義を読む順(Checker.order)を入れ替えて、全部の名前の型(show_t)が同じになるかを見る。
  O1 順に依らない : どの順でも全部の名前の型が同じ
  O2 不動点       : 解いたあとの型は、もう 1 回解いても変わらない
生成は 3 種類に分ける。
  (a) アリティの合った関数だけの輪   : O1 と O2 を失敗の条件にする(実装が満たすべき範囲)
  (b) アリティの合わない呼びを含む輪 : 数えて報告する(順に依る。ill-typed なので J.2 の前提の外)
  (c) 値の定義が輪に混ざる         : 数えて報告する(順に依る。値の自己参照・相互参照は Atom に倒す、という約束が順の影響を受ける)"""
import itertools, random, sys
import sign_interp as S
import sign_types as T

random.seed(20261129)


def solved(nodes, order):
    c = T.Checker(nodes)
    if order is not None: c.order = list(order)
    c.solve(5)
    return {n: T.show_t(c.def_type(n)) for n in c.order}, c

def gen_a():
    n = random.randint(2, 4); names = ["n%d" % i for i in range(n)]; ar = {f: random.randint(1, 2) for f in names}
    lines = []
    for f in names:
        ps = ["a", "b"][:ar[f]]; g = random.choice(names)
        lines.append("%s : %s ? %s %s" % (f, " ".join(ps), g, " ".join(random.choice(ps + ["1", "2.5"]) for _ in range(ar[g]))))
    f = random.choice(names); lines.append("%s %s" % (f, " ".join(random.choice(["1", "2.5"]) for _ in range(ar[f]))))
    return "\n".join(lines) + "\n"

def gen_bc(values):
    n = random.randint(2, 4); names = ["n%d" % i for i in range(n)]
    lines = []
    for f in names:
        g = random.choice(names); k = random.random()
        if values and k < 0.5: lines.append("%s : %s" % (f, g) if k < 0.3 else "%s : %s + 1" % (f, g))
        elif k < 0.75: lines.append("%s : a ? %s a" % (f, g))
        else: lines.append("%s : a b ? %s a b" % (f, g))       # アリティの合わない呼びが混ざる
    lines.append("%s 1" % random.choice(names))
    return "\n".join(lines) + "\n"

def run(gen, count):
    st = {"programs": 0, "order_dep": 0, "not_fixed": 0}; ex = None
    for _ in range(count):
        src = gen()
        try: nodes = S.parse_source(src); base, c0 = solved(nodes, None)
        except Exception: continue
        st["programs"] += 1
        perms = list(itertools.permutations(c0.order)); random.shuffle(perms)
        for perm in perms[:6]:
            try: r, _ = solved(nodes, perm)
            except Exception: continue
            if r != base: st["order_dep"] += 1; ex = ex or (src, base, perm, r); break
        c0.solve(5)
        if {n: T.show_t(c0.def_type(n)) for n in c0.order} != base: st["not_fixed"] += 1
    return st, ex

sa, _ = run(gen_a, 300)
sb, _ = run(lambda: gen_bc(False), 300)
sc, _ = run(lambda: gen_bc(True), 300)
print("(a) アリティの合った関数の輪:", sa)
print("(b) アリティの合わない呼びを含む:", sb)
print("(c) 値の定義が輪に混ざる:", sc)
if sa["order_dep"] or sa["not_fixed"] or sb["not_fixed"] or sc["not_fixed"]: print("NG"); sys.exit(1)
print("全部 ok((a) は順に依らない。(b)(c) は報告)")
