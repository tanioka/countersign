#!/usr/bin/env python3
"""整数の速い道と自己末尾再帰の輪(sign_interp の FAST)の試験: 切った時(SIGN_NO_FAST=1 と同じ)と値・警告・エラーが同じこと。
  python test_fast.py"""
import os, sys, time
sys.setrecursionlimit(30000)
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sign_interp as S

def snap(src, strict, fast):
    S.STRICT_GATES, S.OVERRIDES, S.OPT = strict, False, False
    S.FAST[0] = fast
    S.MEMORY.clear(); S.WARNINGS.clear(); S.LEFTOVERS[0] = 0; S.POS.clear(); S.LOOP_PLANS.clear(); S.LIST_PLANS.clear(); S.DESTR_PLANS.clear()
    try: return ("val", [S.show(r) for r in S.run(src)]), dict(S.MEMORY), [w[0] for w in S.WARNINGS]
    except (S.SignError, SyntaxError, NotImplementedError, RecursionError) as e:
        return ("err", type(e).__name__, str(e).split(":")[0]), dict(S.MEMORY), [w[0] for w in S.WARNINGS]

CASES = [
 ("和の輪", "c : n a ?\n\t\tn <= 0 : a\n\t\tc (n - 1) (a + n)\nc 1000 0"),
 ("階乗の輪", "c : n a ?\n\t\tn <= 1 : a\n\t\tc (n - 1) (a * n)\nc 20 1"),
 ("引数が1つ", "c : n ?\n\t\tn <= 0 : 7\n\t\tc (n - 1)\nc 50"),
 ("行が複数", "c : n a ?\n\t\tn <= 0 : a\n\t\tn = 5 : c (n - 1) (a + 100)\n\t\tc (n - 1) (a + n)\nc 10 0"),
 ("小数が混ざる", "c : n a ?\n\t\tn <= 0 : a\n\t\tc (n - 1) (a + 0.5)\nc 4 0"),
 ("初めの引数が小数", "c : n a ?\n\t\tn <= 0 : a\n\t\tc (n - 1) (a + n)\nc 2.5 0"),
 ("単位", "c : n a ?\n\t\tn <= 0 : a\n\t\tc (n - 1) (a + n)\nc __ 0"),
 ("文字列", "c : n a ?\n\t\tn <= 0 : a\n\t\tc (n - 1) (a + n)\nc 3 `x`"),
 ("0x の顔", "c : n a ?\n\t\tn <= 0 : a\n\t\tc (n - 1) (a + 0x2)\nc 3 0x1"),
 ("0x の名前", "k : 0x4\nc : n a ?\n\t\tn <= 0 : a\n\t\tc (n - 1) (a + k)\nc 3 0x1"),
 ("外の整数", "k : 4\nc : n a ?\n\t\tn <= 0 : a\n\t\tc (n - 1) (a + k)\nc 3 1"),
 ("比べが決まらない(終わる)", "c : n a ?\n\t\tn <= `a` : 9\n\t\tn <= 0 : a\n\t\tc (n - 1) (a + n)\nc 3 0"),
 ("輪の途中で整数でなくなる", "c : n a ?\n\t\tn <= 0 : a\n\t\tn = 2 : c (n - 1) 1.5\n\t\tc (n - 1) (a + n)\nc 4 0"),
 ("部分適用", "c : n a ?\n\t\tn <= 0 : a\n\t\tc (n - 1) (a + n)\n(c 3) 10"),
 ("負の数", "c : n a ?\n\t\tn >= 0 : a\n\t\tc (n + 1) (a - n)\nc (0 - 5) 0"),
 ("大きな数", "c : n a ?\n\t\tn <= 0 : a\n\t\tc (n - 1) (a * 3000000000)\nc 5 1"),
 ("比べの値(0と1)", "f : n m ? n < m\nf 0 5 + f 1 5"),
 ("比べの値(それ以外)", "f : n m ? n < m\nf 7 9"),
 ("等しくない", "f : n m ?\n\t\tn != m : n\n\t\tm\nf 3 4 + f 5 5"),
 ("上書き", "[+] : a b ? a * b\nc : n a ?\n\t\tn <= 0 : a\n\t\tc (n - 1) (a + n)\nc 4 1"),
 ("仮引数が名前を隠す", "n : 5\nc : n a ?\n\t\tn <= 0 : a\n\t\tc (n - 1) (a + n)\nc 3 0"),
 ("別の関数への末尾呼び出し", "d : n a ? a + n\nc : n a ?\n\t\tn <= 0 : a\n\t\td (n - 1) a\nc 3 0"),
 ("非末尾", "s : n ?\n\t\tn <= 0 : 0\n\t\tn + (s (n - 1))\ns 50"),
 ("累積(~で足す)", "bd : n acc ?\n\t\tn = 0 : acc\n\t\tbd (n - 1) (acc~ n)\nbd 5 [0]"),
 ("累積: 足さずに終わる", "bd : n acc ?\n\t\tn = 0 : acc\n\t\tbd (n - 1) (acc~ n)\nbd 0 [0]"),
 ("累積: 初めが器", "bd : n acc ?\n\t\tn = 0 : acc\n\t\tbd (n - 1) (acc~ n)\nbd 4 [7 8 9]"),
 ("累積: 空の器", "bd : n acc ?\n\t\tn = 0 : acc\n\t\tbd (n - 1) (acc~ n)\nbd 3 []"),
 ("累積: 呼び側の器は変わらない", "bd : n acc ?\n\t\tn = 0 : acc\n\t\tbd (n - 1) (acc~ n)\nxs : [1 2]\nbd 3 xs\nxs"),
 ("累積: 複数の項", "bm : n acc ?\n\t\tn <= 0 : acc\n\t\tbm (n - 1) (acc~ n (n * 2))\nbm 3 [0]"),
 ("累積: 小数が混ざる", "bf : n acc ?\n\t\tn = 0 : acc\n\t\tbf (n - 1) (acc~ 1.5)\nbf 3 [1]"),
 ("累積: 途中の答え", "bz : n acc ?\n\t\tn = 3 : 77\n\t\tn = 0 : acc\n\t\tbz (n - 1) (acc~ n)\nbz 5 [0]"),
 ("累積: 入れ子の器", "bd : n acc ?\n\t\tn = 0 : acc\n\t\tbd (n - 1) (acc~ n)\nbd 3 [[1] [2]]"),
 ("累積: 外の整数", "N : 100\nbx : n acc ?\n\t\tn = 0 : acc\n\t\tbx (n - 1) (acc~ (n + N))\nbx 3 [0]"),
 ("累積: 条件で acc を読む", "br : n acc ?\n\t\t||acc|| > 4 : acc\n\t\tbr (n - 1) (acc~ n)\nbr 9 [0]"),
 ("累積: 答えに足す", "bs : n acc ?\n\t\tn = 0 : acc~ 99\n\t\tbs (n - 1) (acc~ n)\nbs 3 [0]"),
 ("累積: 答えが別の器", "bd : n acc ?\n\t\tn = 0 : acc\n\t\tbd (n - 1) (acc~ n)\nbd 6 [1 2] , 9"),
 ("残り: 和", "sx : [x ~xs] acc ?\n\t\t||xs|| = 0 : acc + x\n\t\tsx xs (acc + x)\nsx [1 2 3 4] 0"),
 ("残り: 1 つだけ", "sx : [x ~xs] acc ?\n\t\t||xs|| = 0 : acc + x\n\t\tsx xs (acc + x)\nsx [7] 0"),
 ("残り: 器でない", "sx : [x ~xs] acc ?\n\t\t||xs|| = 0 : acc + x\n\t\tsx xs (acc + x)\nsx 5 0"),
 ("残り: 空の器", "sx : [x ~xs] acc ?\n\t\t||xs|| = 0 : acc + x\n\t\tsx xs (acc + x)\nsx [] 0"),
 ("残り: 小数・文字が混ざる", "sx : [x ~xs] acc ?\n\t\t||xs|| = 0 : acc + x\n\t\tsx xs (acc + x)\nsx [1 2.5 3] 0"),
 ("残り: 文字", "sx : [x ~xs] acc ?\n\t\t||xs|| = 0 : acc + x\n\t\tsx xs (acc + x)\nsx [1 `a` 3] 0"),
 ("残り: 入れ子", "sx : [x ~xs] acc ?\n\t\t||xs|| = 0 : acc + x\n\t\tsx xs (acc + x)\nsx [[1 2] [3]] 0"),
 ("残り: 呼び側の器は変わらない", "sx : [x ~xs] acc ?\n\t\t||xs|| = 0 : acc + x\n\t\tsx xs (acc + x)\nys : [4 5 6]\nsx ys 0\nys"),
 ("残り: 2 つずつ", "s2 : [x y ~r] acc ?\n\t\t||r|| = 0 : acc + x + y\n\t\ts2 r (acc + (x * y))\ns2 [1 2 3 4 5 6] 0"),
 ("残り: 2 つずつ(余る)", "s2 : [x y ~r] acc ?\n\t\t||r|| = 0 : acc + x + y\n\t\ts2 r (acc + (x * y))\ns2 [1 2 3 4 5] 0"),
 ("残り: 底が無い", "nb : [x ~xs] acc ?\n\t\tx > 100 : acc\n\t\tnb xs (acc + x)\nnb [1 2 3] 0"),
 ("残り: 途中で止まる", "nb : [x ~xs] acc ?\n\t\tx > 100 : acc\n\t\tnb xs (acc + x)\nnb [1 200 3] 0"),
 ("残り: 残りの長さで止まる", "cn : [x ~xs] n ?\n\t\t||xs|| < 3 : n\n\t\tcn xs (n + 1)\ncn [1 2 3 4 5 6] 0"),
 ("残り: 部分適用", "sx : [x ~xs] acc ?\n\t\t||xs|| = 0 : acc + x\n\t\tsx xs (acc + x)\n(sx [1 2 3]) 10"),
 ("相互再帰", "ev : n ?\n\t\tn = 0 : 1\n\t\tod (n - 1)\nod : n ?\n\t\tn = 0 : 0\n\t\tev (n - 1)\nev 11"),
]

def main():
    bad = 0
    for name, src in CASES:
        for strict in (False, True):
            a, b = snap(src, strict, False), snap(src, strict, True)
            if a != b:
                bad += 1; print(f"NG  {'strict ' if strict else 'default'} {name}\n    切った: {a}\n    速い道: {b}")
    S.FAST[0] = True
    t0 = time.time(); S.FAST[0] = True; S.STRICT_GATES = False; S.LIST_PLANS.clear()
    v = S.show(S.run("bd : n acc ?\n\t\tn = 0 : acc\n\t\tbd (n - 1) (acc~ n)\n(bd 30000 [0]) ' 30000")[-1]); ok = v == "1" and time.time() - t0 < 3
    if not ok: bad += 1
    print(("ok  " if ok else "NG  ") + f"累積の速さ(30000 項) {time.time() - t0:.2f}s")
    t0 = time.time(); S.FAST[0] = True; S.STRICT_GATES = False; S.LIST_PLANS.clear(); S.DESTR_PLANS.clear()
    v = S.show(S.run("bd : n acc ?\n\t\tn = 0 : acc\n\t\tbd (n - 1) (acc~ n)\nsx : [x ~xs] acc ?\n\t\t||xs|| = 0 : acc + x\n\t\tsx xs (acc + x)\nsx (bd 30000 [0]) 0")[-1]); ok = v == "450015000" and time.time() - t0 < 3
    if not ok: bad += 1
    print(("ok  " if ok else "NG  ") + f"残りの輪の速さ(30000 項) {time.time() - t0:.2f}s")
    src = "c : n a ?\n\t\tn <= 0 : a\n\t\tc (n - 1) (a + n)\nc 200000 0"
    for strict in (False, True):
        S.STRICT_GATES = strict; S.LOOP_PLANS.clear(); t = time.time(); v = S.show(S.run(src)[-1])
        ok = v == "20000100000" and time.time() - t < 3
        if not ok: bad += 1
        print(("ok  " if ok else "NG  ") + f"輪の速さ({'strict' if strict else 'default'}) {time.time() - t:.2f}s")
    print(f"\n全部通った ({len(CASES) * 2 + 4})" if not bad else f"\n{bad} 件が食い違い")
    return bad

if __name__ == "__main__": sys.exit(1 if main() else 0)
