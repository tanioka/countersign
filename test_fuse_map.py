#!/usr/bin/env python3
"""融合 段 2(`[op] (map $g xs)` を 1 つの輪にする)の試験。
各例で (1) 処理系の答え = 融合した asm の答え、(2) 融合の有無で asm の答えが同じ、(3) 融合したか(補助 `_fmS_` が出る/出ない)を見る。"""
import os, sys
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
src_t = open(os.path.join(HERE, "test_asm.py"), encoding="utf-8").read().split("MAX, MIN1 =")[0]
exec(compile(src_t.replace("__file__", repr(os.path.join(HERE, "test_asm.py"))), "test_asm_head", "exec"))
import sign_asm
M = "map : f [h ~t] ? (@f h) (map f t)~\n"
CASES = [
    ("名前の関数で足す", M + "sq : x ? x * x\n[+] (map $sq (1 2 3))\n", True),
    ("掛ける畳み", M + "inc : x ? x + 1\n[*] (map $inc (1 2 3))\n", True),
    ("引く畳み", M + "sq : x ? x * x\n[-] (map $sq (5 2 1))\n", True),
    ("節 $[* 2]", M + "[+] (map $[* 2] (1 2 3 4))\n", True),
    ("節 $[- 1]", M + "[+] (map $[- 1] (1 2 3 4))\n", True),
    ("無名の関数", M + "[+] (map $[x ? x * 3 + 1] (1 2 3))\n", True),
    ("仮引数のリスト", M + "sq : x ? x * x\ns : xs ? [+] (map $sq xs)\ns (1 2 3 4)\n", True),
    ("範囲を渡す", M + "sq : x ? x * x\n[+] (map $sq [1 ~ 5])\n", True),
    ("2 か所", M + "sq : x ? x * x\n([+] (map $sq (1 2))) + ([*] (map $sq (3 4)))\n", True),
    ("別名の map", "m : f [h ~t] ? (@f h) (m f t)~\nsq : x ? x * x\n[+] (m $sq (1 2 3))\n", True),
    # 融合しない(今までの道のまま)
    ("割り算を含む g", M + "h : x ? 12 / x\n[+] (map $h (1 2 3))\n", False),
    ("恒等の g", M + "w : x ? x\n[+] (map $w (1 2 3))\n", True),
    ("g が別の関数を呼ぶ", M + "a : x ? x + 1\nb : x ? a x\n[+] (map $b (1 2 3))\n", False),
    ("map が別の形", "map : f [h ~t] ? (@f h) (map f t)~ 7\nsq : x ? x * x\n[+] (map $sq (1 2 3))\n", False),
    ("比較の畳み", M + "sq : x ? x * x\n[<] (map $sq (1 2 3))\n", False),
]
ng = 0
def gen(src, fuse):
    sign_asm.FUSE[0] = fuse
    try: return sign_asm.generate(sign_interp.parse_source(src))
    finally: sign_asm.FUSE[0] = True
for name, src, want_fuse in CASES:
    want = interp(src)
    try:
        t1 = gen(src, True); a1 = run_asm(t1)
    except Exception as e:
        t1 = ""; a1 = ("断り", str(e)[:50])
    try:
        t0 = gen(src, False); a0 = run_asm(t0)
    except Exception as e:
        t0 = ""; a0 = ("断り", str(e)[:50])
    fused = "_fmS_" in t1
    ok = (a1 == want or a1[0] == "断り") and (a0 == a1 or a0[0] == "断り") and fused == want_fuse
    if a1[0] == "断り" and want_fuse: ok = False
    print(("ok  " if ok else "NG  ") + name, "処理系=%s 融合=%s 融合なし=%s 融合した=%s" % (want, a1, a0, fused) if not ok else "")
    ng += (not ok)
print("全部 ok" if not ng else "NG %d 件" % ng); sys.exit(1 if ng else 0)
