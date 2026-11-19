#!/usr/bin/env python3
"""ループ不変式(sign_fuse.lazy_invariants)の試験: 処理系 = 移動した asm = 移動しない asm、働いたか(乗算が減るか)、罠の起きる時が変わらないか。"""
import os, sys
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
src_t = open(os.path.join(HERE, "test_asm.py"), encoding="utf-8").read().split("MAX, MIN1 =")[0]
exec(compile(src_t.replace("__file__", repr(os.path.join(HERE, "test_asm.py"))), "test_asm_head", "exec"))
import sign_asm
BIG = 4611686018427387904
L = "lp : i n k acc ?\n\ti >= n : acc\n\t(k * 3) > i : lp (i + 1) n k (acc + 1)\n\tlp (i + 1) n k (acc + 2)\n"
CASES = [
    ("不変な積が条件にある", L + "lp 0 10 2 0\n", True),
    ("積が条件で偽", L + "lp 0 10 1 0\n", True),
    ("0 回で終わる(積は評価されない)", L + "lp 5 5 %d 0\n" % BIG, True),         # i >= n で抜ける。k * 3 は評価されず、罠にならない
    ("積が溢れる(評価される)", L + "lp 0 10 %d 0\n" % BIG, True),                 # 元でも k * 3 で溢れる。同じ結果
    ("割り算が条件にある", "q : i n d ?\n\ti >= n : i\n\t(d / 2) > i : q (i + 1) n d\n\ti\nq 0 9 10\n", True),
    ("足し引きだけ(対象外)", "r : i n k ?\n\ti >= n : i\n\t(k + 3) > i : r (i + 1) n k\n\ti\nr 0 9 6\n", False),
    ("不変でない引数の積(対象外)", "s : i n ?\n\ti >= n : i\n\t(i * 3) > 20 : i\n\ts (i + 1) n\ns 0 20\n", False),
    ("再帰しない(対象外)", "u : a b ?\n\t(a * b) > 3 : 1\n\t0\nu 2 3\n", False),
]
ng = 0
def gen(src, h):
    sign_asm.HOIST[0] = h
    try: return sign_asm.generate(sign_interp.parse_source(src))
    finally: sign_asm.HOIST[0] = True
for name, src, want_h in CASES:
    want = interp(src)
    r = {}
    for h in (True, False):
        try:
            t = gen(src, h); r[h] = (run_asm(t), t.count("ループ不変式"))
        except Exception as e:
            r[h] = (("断り", str(e)[:50]), 0)
    ok = r[True][0] == want and r[False][0] == want and (r[True][1] > 0) == want_h and r[False][1] == 0
    print(("ok  " if ok else "NG  ") + name, "" if ok else "処理系=%s 移動=%s なし=%s" % (want, r[True], r[False]))
    ng += (not ok)
print("全部 ok" if not ng else "NG %d 件" % ng); sys.exit(1 if ng else 0)
