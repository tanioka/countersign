#!/usr/bin/env python3
"""symbol_of の単射の試験(評価の指摘: x0 と sn_x0 が同じ sn_x0 になる)。python test_symbol.py"""
import random, sys
import sign_asm as A
bad = 0
def check(name, ok):
    global bad; bad += not ok; print(("ok  " if ok else "NG  ") + name)
check("x0 と sn_x0 は別の綴り", A.symbol_of("x0") != A.symbol_of("sn_x0"))
check("レジスタ名は sn_ を付ける", A.symbol_of("x0") == "sn_x0" and A.symbol_of("sp") == "sn_sp")
check("ふつうの名前はそのまま", A.symbol_of("inc") == "inc" and A.symbol_of("add_1") == "add_1")
check("`_u` で始まる名前と日本語の名前は別", A.symbol_of("_u_3b1_") != A.symbol_of("α"))
check("`__sp` で終わる名前は、投機の複製の印と別", A.symbol_of("a__sp") != A.symbol_of("a") + "__sp")
random.seed(7); seen = {}; clash = 0
for _ in range(5000):
    n = "".join(random.choice("xsn_u0a1pwαβ") for _ in range(random.randint(1, 7)))
    if n[0].isdigit(): continue
    s = A.symbol_of(n)
    if seen.setdefault(s, n) != n: clash += 1
check(f"ランダムな名前 {len(seen)} 件で衝突なし", clash == 0)
print("\n" + ("全部通った" if not bad else f"{bad} 件 食い違い")); sys.exit(1 if bad else 0)
