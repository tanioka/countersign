#!/usr/bin/env python3
"""レコードの分解(sign_fuse.scalarize_records)の試験。処理系 = 分解した asm = 分解しない asm、器の置き場(返値スロット)が減ったか。"""
import os, sys
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
src_t = open(os.path.join(HERE, "test_asm.py"), encoding="utf-8").read().split("MAX, MIN1 =")[0]
exec(compile(src_t.replace("__file__", repr(os.path.join(HERE, "test_asm.py"))), "test_asm_head", "exec"))
import sign_asm
CHAIN = """mv2 : a b c ? [a (b + 1) c]
mv : [a b c] ? mv2 a b c
fe : [a b c] ? [a b (c + 2)]
mk : x ? [x (x + 1) (x + 2)]
t : x ? fe (mv (mk x))
g : x ? (t x) ' 2
"""
CASES = [
    ("字面を直に渡す", "mv2 : a b c ? [a (b + 1) c]\nmv : [a b c] ? mv2 a b c\ng : x ? (mv [x (x + 1) 3]) ' 1\ng 5\n", True),
    ("添字だけで使う仮引数", "p : i v ? (v ' 0) + (v ' 2) + i\ng : x ? p x [x (x + 1) 3]\ng 5\n", True),
    ("3 段の連なり", CHAIN + "g 5\n", True),
    ("連なりをループで", CHAIN + "lp : i n acc ?\n\ti >= n : acc\n\tlp (i + 1) n (acc + (g i))\nlp 0 50 0\n", True),
    ("返す側が cases(字面と末尾呼び)", "z : [a b] ? [a (b + 1)]\nw : x ?\n\tx > 10 : [x 1]\n\tx > 5 : [x 2]\n\tw (x + 4)\nh : x ? (z (w x)) ' 1\nh 1\n", True),
    ("他の引数がある受け手", "q : k [a b] ? (a * k) + b\nm : x ? [x (x + 1)]\nr : x ? q 3 (m x)\nr 4\n", True),
    ("要素が決まらない(割り算)", "mv : [a b] ? a + b\ng : x ? mv [x (10 / x)]\ng 2\n", False),
    ("長さが合わない", "mv : [a b c] ? a + b + c\ng : x ? mv [x x]\ng 2\n", False),
    ("受け手が器を別の使い方もする", "u : v ? (v ' 0) + ||v||\ng : x ? u [x x x]\ng 2\n", False),
    ("要素が読み(@)", "mv : [a b] ? a + b\ng : x ? mv [(@(x + 0)) 3]\ng 0\n", None),     # 読みは全域: 分解してよい。メモリの中身で結果が変わるので、処理系との一致だけ見る
]
ng = 0
def gen(src, sc):
    sign_asm.SCALAR[0] = sc
    try: return sign_asm.generate(sign_interp.parse_source(src))
    finally: sign_asm.SCALAR[0] = True
for name, src, want_cut in CASES:
    try: want = interp(src)
    except Exception as e: want = ("処理系の例外", str(e)[:30])
    r = {}
    for sc in (True, False):
        try:
            t = gen(src, sc); r[sc] = (run_asm(t), t.count("返値スロット"))
        except Exception as e:
            r[sc] = (("断り", str(e)[:40]), 99)
    same = r[True][0] == r[False][0] or r[False][0][0] == "断り"
    ok = same and (r[True][0] == want or want[0] == "処理系の例外" or r[False][0] == r[True][0] and name.startswith("要素が読み"))
    if want_cut is not None: ok = ok and ((r[True][1] < r[False][1]) == want_cut)
    print(("ok  " if ok else "NG  ") + name, "" if ok else "処理系=%s 分解=%s なし=%s" % (want, r[True], r[False]))
    ng += (not ok)
# 仮引数が定義と同じ名前(仮引数が勝つ): 処理系と答えが同じ(分解の有無によらない)
SH = [("先頭に来る", "x1 : 7\nmv : [a b] ? a + b\ng : x1 ? mv [x1 3]\ng 4\n"),
      ("器の先頭", "x1 : 7\ng : x1 ? [x1 3]\n(g 4) ' 0\n"),
      ("普通の使い方", "x1 : 7\ng : x1 ? x1 + 1\ng 4\n"),
      ("入れ子の関数が同じ名前の仮引数", "x1 : 7\nap : f v ? @f v\ng : x1 ? ap $[x1 ? x1 + 100] x1\ng 4\n"),
      ("括りの仮引数と同じ名前", "x1 : 7\nmv : [x1 b] ? x1 + b\nmv [4 3]\n"),
      ("定義の方を使う別の関数は変わらない", "x1 : 7\ng : x1 ? [x1 3]\nh : y ? [x1 y]\n((g 4) ' 0) + ((h 1) ' 0)\n")]
for nm_, src in SH:
    want = interp(src)
    for sc in (True, False):
        try: got = run_asm(gen(src, sc))
        except Exception as e: got = ("断り", str(e)[:40])
        good = got == want
        print(("ok  " if good else "NG  ") + "仮引数が定義と同じ名前: %s(分解=%s)" % (nm_, sc), "" if good else "処理系=%s asm=%s" % (want, got)); ng += (not good)
print("全部 ok" if not ng else "NG %d 件" % ng); sys.exit(1 if ng else 0)
