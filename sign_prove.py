"""線形整数算術の小さな証明器(Fourier-Motzkin 消去 + 整数の切り上げ)。
制約は {原子: 係数} と定数 c で `Σ 係数·原子 + c ≥ 0` を表す。unsat() が True なら、制約を同時に満たす整数は無い(健全)。
False は『分からない』(満たす解がある、または大きくなりすぎて諦めた)。証明は unsat だけを使う。"""
from math import gcd

class Sys:
    LIMIT = 600
    def __init__(self): self.cs = []
    def add(self, coefs, const):
        """Σ coefs·原子 + const ≥ 0 を足す。"""
        c = {k: v for k, v in coefs.items() if v}
        if not c:
            self.cs.append(({}, const)); return
        g = 0
        for v in c.values(): g = gcd(g, abs(v))
        if g > 1: c = {k: v // g for k, v in c.items()}; const = const // g      # Σ a·x ≥ -const の両辺を g で割ると右辺は切り上げ。const' = floor(const / g)
        self.cs.append((c, const))
    def eq(self, coefs, const):
        self.add(coefs, const); self.add({k: -v for k, v in coefs.items()}, -const)
    def unsat(self):
        cs = [(dict(c), k) for c, k in self.cs]
        while True:
            for c, k in cs:
                if not c and k < 0: return True
            atoms = {a for c, _ in cs for a in c}
            if not atoms: return False
            best, bs = None, None
            for a in atoms:
                p = sum(1 for c, _ in cs if c.get(a, 0) > 0); n = sum(1 for c, _ in cs if c.get(a, 0) < 0)
                sc = p * n - p - n
                if bs is None or sc < bs: best, bs = a, sc
            a = best; pos, neg, rest = [], [], []
            for c, k in cs:
                v = c.get(a, 0)
                (pos if v > 0 else neg if v < 0 else rest).append((c, k))
            new = list(rest)
            for cp, kp in pos:
                for cn, kn in neg:
                    ap, an = cp[a], -cn[a]; g = gcd(ap, an); mp, mn = an // g, ap // g
                    c = {}
                    for x, v in cp.items(): c[x] = c.get(x, 0) + v * mp
                    for x, v in cn.items(): c[x] = c.get(x, 0) + v * mn
                    k = kp * mp + kn * mn
                    c = {x: v for x, v in c.items() if v and x != a}
                    if c:
                        gg = 0
                        for v in c.values(): gg = gcd(gg, abs(v))
                        if gg > 1: c = {x: v // gg for x, v in c.items()}; k = k // gg          # Python の // は切り下げ: floor(k/g) が整数の切り上げ後の定数
                    new.append((c, k))
            # 重複を落とす
            seen = {}
            for c, k in new:
                key = tuple(sorted(c.items()))
                if key not in seen or k < seen[key]: seen[key] = k
            cs = [(dict(key), k) for key, k in seen.items()]
            if len(cs) > self.LIMIT: return False
