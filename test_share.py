#!/usr/bin/env python3
"""共通部分式(枝をまたぐ式、sign_fuse.share_exprs)の試験。処理系 = 共通化した asm = 共通化しない asm、共通化が働いたか、罠の起きる時が変わらないか。"""
import os, sys
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
src_t = open(os.path.join(HERE, "test_asm.py"), encoding="utf-8").read().split("MAX, MIN1 =")[0]
exec(compile(src_t.replace("__file__", repr(os.path.join(HERE, "test_asm.py"))), "test_asm_head", "exec"))
import sign_asm
G = "g : a b ?\n\ta > b : 0 - 1\n\t((a + b) / 2) > 10 : (a + b) / 2\n\t((a + b) / 2) * 3\n"
H = "h : lo hi n ?\n\tlo > hi : n\n\t((lo + hi) / 2) % 2 = 0 : h (((lo + hi) / 2) + 1) hi (n + 1)\n\th lo (((lo + hi) / 2) - 1) (n + 2)\n"
BIG = 9223372036854775000
CASES = [
    ("先の枝で抜ける", G + "g 3 1\n", True),
    ("式が 10 より大", G + "g 30 40\n", True),
    ("式が 10 以下", G + "g 1 5\n", True),
    ("先の枝で抜ける(a+b が溢れる)", G + "g %d 1\n" % BIG, True),      # a > b で抜けるので、a + b は評価されない。罠にならない
    ("式が溢れる(抜けない)", G + "g 1 %d\n" % BIG, True),            # 元でも (a + b) で溢れる。同じ結果(罠)になる
    ("自己再帰(ループ)", H + "h 0 100 0\n", True),
    ("自己再帰 空", H + "h 5 1 7\n", True),
    ("共有する式が無い", "k : a b ?\n\ta > b : 0\n\t(a + b) / 2\n", False),
    ("1 回しか出ない", "k : a b ?\n\ta > b : (a + b) / 2\n\t0\nk 1 2\n", False),
]
ng = 0
def gen(src, share):
    sign_asm.SHARE[0] = share
    try: return sign_asm.generate(sign_interp.parse_source(src))
    finally: sign_asm.SHARE[0] = True
for name, src, want_share in CASES:
    if not src.rstrip().splitlines()[-1].startswith(("g ", "h ", "k ")) and name in ("共有する式が無い",): src += "k 1 2\n"
    want = interp(src)
    r = {}
    for sh in (True, False):
        try:
            t = gen(src, sh); r[sh] = (run_asm(t), t.count("sdiv"))
        except Exception as e:
            r[sh] = (("断り", str(e)[:50]), False)
    ok = r[True][0] == want and r[False][0] == want and (r[True][1] < r[False][1]) == want_share     # 働いたかは、除算の命令が減ったかで見る(使われない保存は消される)
    print(("ok  " if ok else "NG  ") + name, "" if ok else "処理系=%s 共通化=%s なし=%s" % (want, r[True], r[False]))
    ng += (not ok)
print("全部 ok" if not ng else "NG %d 件" % ng); sys.exit(1 if ng else 0)
