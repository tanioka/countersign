#!/usr/bin/env python3
"""部分計算・一般部分計算(sign_pe.py)の試験: 最適化の有る無しで、値・メモリ・警告・エラーが同じであること。

  python test_pe.py        # 既定と --strict の両方で回す
各行は (名前, ソース, 期待する最適化の回数(STATS の鍵 → 1以上), 期待しない鍵)。回数は「効いたこと」の確認で、
意味の同値は常に見る。"""
import os, sys
sys.setrecursionlimit(20000)
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sign_interp as S, sign_pe as P

def snap(src, strict, opt):
    S.STRICT_GATES, S.OPT, S.OVERRIDES = strict, opt, False
    S.MEMORY.clear(); S.WARNINGS.clear(); S.LEFTOVERS[0] = 0; S.POS.clear()
    try:
        res = S.run(src)
        out = ("val", [S.show(r) for r in res])
    except (S.SignError, SyntaxError, NotImplementedError) as e:
        out = ("err", type(e).__name__, str(e).split(":")[0])
    return out, dict(S.MEMORY), list(S.WARNINGS), dict(P.STATS)

CASES = [
 ("定数伝播", "K : 8\nf : n ? n + K\nf 2", {"const": 1}),
 ("定数の連鎖", "A : 3\nB : A * 4\nf : n ? n + B\nf 1", {"const": 1}),
 ("畳み込み", "x : 2 + 3 * 4\ny : x - (1 + 1)\ny", {"fold": 1}),
 ("比較の畳み込み", "a : (3 < 5)\nb : (5 < 3)\nc : (3 < 5) & (7 > 2)\nb", {"fold": 1}),
 ("行の畳み込み", "K : 0\nf : n ?\n\t\tK : 99\n\t\tn > 5 : n\n\t\t0\nf 9", {}),
 ("静的な呼び出し", "sq : n ? n * n\nsq 12 + 1", {"static-call": 1}),
 ("静的な末尾再帰", "sum : n a ?\n\t\tn <= 0 : a\n\t\tsum (n - 1) (a + n)\nsum 100 0", {"static-call": 1}),
 ("単位を渡す", "sq : n ? n * n\nsq __", {}),
 ("GPC &: 真", "f : n ?\n\t\tn > 10 : (n > 5) & 100\n\t\t0\n0x1000 # 11\nf (@0x1000)", {"gpc": 1}),
 ("GPC &: 偽", "f : n ?\n\t\tn > 10 : (n < 5) & 100\n\t\t0\n0x1000 # 11\nf (@0x1000)", {"gpc": 1}),
 ("GPC |: 真", "f : n ?\n\t\tn > 10 : (n > 5) | 100\n\t\t0\n0x1000 # 11\nf (@0x1000)", {"gpc": 1}),
 ("GPC |: 偽", "f : n ?\n\t\tn > 10 : (n < 5) | 100\n\t\t0\n0x1000 # 11\nf (@0x1000)", {"gpc": 1}),
 ("GPC 区間の境界(開)", "f : n ?\n\t\tn > 10 : (n >= 11) & 100\n\t\t0\n0x1000 # 11\nf (@0x1000)", {}),
 ("GPC 小数", "f : n ?\n\t\tn > 2 : (n >= 3) & 1\n\t\t0\n0x1000 # 2.5\nf (@0x1000)", {}),
 ("GPC 数でない値(未書き込み)", "f : n ?\n\t\tn > 10 : (n > 5) & 100\n\t\t7\nf (@0x2000)", {"gpc": 1}),
 ("GPC リスト", "f : n ?\n\t\tn < 3 : (n < 4) & 100\n\t\t7\n0x1000 # [1 2]\nf (@0x1000)", {}),
 ("GPC 連鎖", "f : n ?\n\t\t0 < n < 10 : (n > 0) & (n < 10) & 100\n\t\t7\n0x1000 # 5\nf (@0x1000)", {"gpc": 2}),
 ("GPC 影になる仮引数", "f : n ?\n\t\tn > 10 : (g (n - 20)) + ((n > 5) & 1)\n\t\t7\ng : n ? (n > 5) & 1\n0x1000 # 11\nf (@0x1000)", {"gpc": 1}),
 ("GPC 再帰", "f : n a ?\n\t\tn > 0 : f (n - 1) (a + ((n > 0) & 1))\n\t\ta\n0x1000 # 6\nf (@0x1000) 0", {"gpc": 1}),
 ("GPC 番地を取られた仮引数", "f : n ?\n\t\tn > 10 : (n > 5) & 100\n\t\t0\n0x1000 # 11\nz : $n\nf (@0x1000)", {}),
 ("入れ子 GPC: 真", "f : n ?\n\t\tn > 10 :\n\t\t\t\tn > 5 : 100\n\t\t\t\t200\n\t\t0\n0x1000 # 11\nf (@0x1000)", {"row-true": 1}),
 ("入れ子 GPC: 偽", "f : n ?\n\t\tn > 10 :\n\t\t\t\tn < 5 : 100\n\t\t\t\t200\n\t\t0\n0x1000 # 11\nf (@0x1000)", {"row-dead": 1}),
 ("入れ子 GPC: 負の事実", "f : n ?\n\t\tn > 0 :\n\t\t\t\tn <= 0 : 1\n\t\t\t\tn > 0 : 2\n\t\t\t\t3\n\t\t4\n0x1000 # 5\nf (@0x1000)", {"row-dead": 1}),
 ("入れ子: 値の行は List", "f : n ?\n\t\tn > 0 :\n\t\t\t\t1 2\n\t\t\t\t3 4\n\t\t0\nf 5", {}),
 ("影", "K : 5\nf : K ? K + 1\nf 2", {}),
 ("$ で番地", "K : 5\nz : $K\nK + 1", {}),
 ("再定義", "K : 5\nK : 6\nK + 1", {}),
 ("メモリ", "w : n ? 0x1000 # n\nw 7\n@0x1000", {}),
 ("不純な関数は呼ばない", "w : n ? 0x1000 # n\nw 7\nw 8\n@0x1000", {}),
 ("演算子の上書き", "[+] : a b ? a * b\nK : 3\nK + 4", {}),
 ("0 で割る", "f : n ? 10 / n\nf 0", {}),
 ("文字列", "K : 2\n`ab` * K", {}),
 ("ベクトル", "v : [1.0 2.0 3.0 4.0]\nv + v", {}),
 ("既定引数", "f : n m:5 ? n + m\nf 1", {}),
 ("括り仮引数", "f : [a b] ? a + b\nf [1 2]", {}),
 ("map", "inc : x ? x + 1\nmap inc [1 2 3]", {}),
 ("高階", "ap : g x ? g x\ninc : x ? x + 1\nap inc 4", {}),
 ("条件の連鎖", "f : n ?\n\t\t0 < n < 10 : 1\n\t\t0\nf 5 + f 20", {}),
 ("TCO の深い輪", "c : n a ?\n\t\tn <= 0 : a\n\t\tc (n - 1) (a + 1)\nc 50000 0", {}),
 ("アキュムレータ: 和", "sm : n ?\n\t\tn <= 0 : 0\n\t\tn + (sm (n - 1))\nsm 10", {"accum": 1}),
 ("アキュムレータ: 階乗", "ft : n ?\n\t\tn <= 1 : 1\n\t\t(ft (n - 1)) * n\nft 10", {"accum": 1}),
 ("アキュムレータ: 末尾の行も混ざる", "g9 : n ?\n\t\tn <= 0 : 0\n\t\tn = 5 : g9 (n - 1)\n\t\t2 * n + (g9 (n - 1))\ng9 10", {"accum": 1}),
 ("アキュムレータ: 実引数が2つ", "h9 : n m ?\n\t\tn <= 0 : m\n\t\tn + (h9 (n - 1) (m + 1))\nh9 6 100", {"accum": 1}),
 ("アキュムレータ: 小数は元の本体", "sm : n ?\n\t\tn <= 0 : 0\n\t\tn + (sm (n - 1))\nsm 2.5", {"accum": 1}),
 ("アキュムレータ: 文字列は元の本体", "sm : n ?\n\t\tn <= 0 : 0\n\t\tn + (sm (n - 1))\nsm `ab`", {"accum": 1}),
 ("アキュムレータ: 単位は元の本体", "sm : n ?\n\t\tn <= 0 : 0\n\t\tn + (sm (n - 1))\nsm __", {"accum": 1}),
 ("アキュムレータ: 引数が足りない部分適用", "h9 : n m ?\n\t\tn <= 0 : m\n\t\tn + (h9 (n - 1) (m + 1))\n(h9 3) 10", {"accum": 1}),
 ("アキュムレータ: 負の数", "sm : n ?\n\t\tn <= 0 : 0\n\t\tn + (sm (n - 1))\nsm (0 - 3)", {"accum": 1}),
 ("アキュムレータ: 引き算は対象外", "sb : n ?\n\t\tn <= 0 : 0\n\t\tn - (sb (n - 1))\nsb 7", {}),
 ("アキュムレータ: + と * が混ざると対象外", "mx : n ?\n\t\tn <= 0 : 1\n\t\tn = 3 : n * (mx (n - 1))\n\t\tn + (mx (n - 1))\nmx 6", {}),
 ("アキュムレータ: 既定の行が無いと対象外", "nd : n ?\n\t\tn <= 0 : 0\n\t\tn > 0 : n + (nd (n - 1))\nnd 5", {}),
 ("アキュムレータ: 再帰が2か所は対象外", "fb : n ?\n\t\tn < 2 : n\n\t\t(fb (n - 1)) + (fb (n - 2))\nfb 10", {}),
 ("インライン: 引数が仮引数", "sq : x ? x * x\nad : a b ? a + b + 1\nf : n ? (sq n) + (ad n 3)\nf 5", {"inline": 2}),
 ("インライン: 引数が字面", "sq : x ? x * x\nf : n ? (sq 4) + n\nf 5", {"static-call": 1}),
 ("インライン: 単位は展開しない", "sq : x ? x * x\nf : n ? (sq __) + n\nf 5", {}),
 ("インライン: 仮引数が単位", "sq : x ? x * x\nf : n ? (sq n) + 1\nf __", {}),
 ("インライン: 0x の字面", "sq : x ? x * x\nf : n ? (sq 0x4) + n\nf 5", {}),
 ("インライン: 0x の名前を渡す", "k : 0x4\nsq : x ? x * x\nf : n ? (sq k) + n\nf 5", {}),
 ("インライン: 引数が式", "sq : x ? x * x\nf : n ? (sq (n + 1)) + 2\nf 5", {}),
 ("インライン: 名前が隠れる", "sq : x ? x * x\nf : sq ? sq + 1\nf 5", {}),
 ("インライン: 小数", "sq : x ? x * x\nf : n ? (sq n) + 1\nf 2.5", {"inline": 1}),
 ("インライン: 文字列は対象外", "sq : x ? x * x\nf : n ? (sq n)\nf `ab`", {"inline": 1}),
 ("インライン: 本体が大きい関数は対象外", "bg : x ? x + x * x - x + x * x - x + x * x - x + x * x\nf : n ? bg n\nf 3", {}),
 ("インライン: 番地を取られた関数", "sq : x ? x * x\nz : $sq\nf : n ? (sq n) + 1\nf 4", {}),
 ("共通部分式: 重複した呼び出し", "sl : n ?\n\t\tn <= 0 : 0\n\t\tn + (sl (n - 1))\nh : n ? (sl n) + (sl n)\nh 10", {"cse": 1}),
 ("共通部分式: 割り算を含む関数は対象外", "dv : n ? 100 / n\nh : n ? (dv n) + (dv n)\nh 0", {}),
 ("共通部分式: 引数が違えば別", "sl : n ?\n\t\tn <= 0 : 0\n\t\tn + (sl (n - 1))\nh : n ? (sl n) + (sl 3)\nh 10", {}),
 ("使われない局所の定義", "w : n ?\n\t\tk : 5\n\t\tn + 1\nw 3", {"dead-local": 1}),
 ("使われる局所の定義は残す", "w : n ?\n\t\tk : 5\n\t\tn + k\nw 3", {}),
 ("局所の定義: 式は残す(効果があるかもしれない)", "w : n ?\n\t\tk : n + 1\n\t\tn\nw 3", {}),
]

def deep_case():
    """アキュムレータ導入: 非末尾の深い再帰が、呼びの積み上がり無しで走る(元は RecursionError)。"""
    src = "sm : n ?\n\t\tn <= 0 : 0\n\t\tn + (sm (n - 1))\nsm 30000"
    S.STRICT_GATES, S.OVERRIDES, S.OPT = False, False, True
    try: v = S.show(S.run(src)[-1])
    except RecursionError: v = "RecursionError"
    finally: S.OPT = False
    ok = v == str(30000 * 30001 // 2)
    print(("ok  " if ok else "NG  ") + "アキュムレータ: 深い非末尾再帰")
    return 0 if ok else 1

def fuel_case():
    """止まらない呼び出しは、燃料が尽きて元のまま残る(走らせはしない)。"""
    S.STRICT_GATES, S.OVERRIDES = False, False
    nodes = S.parse_source("loop : n ? loop (n + 1)\nloop 0")
    out = P.optimize(S, nodes)
    ok = out[1] == nodes[1] and P.STATS.get("static-call", 0) == 0 and S.FUEL[0] is None
    print(("ok  " if ok else "NG  ") + "燃料切れは元のまま残す")
    return 0 if ok else 1

def main():
    bad = fuel_case() + deep_case()
    for name, src, want in CASES:
        for strict in (False, True):
            u = snap(src, strict, False)
            o = snap(src, strict, True)
            same = u[:3] == o[:3]
            miss = [k for k, v in want.items() if o[3].get(k, 0) < v]
            tag = "strict " if strict else "default"
            if not same or (miss and not strict):
                bad += 1
                print(f"NG  {tag} {name}\n    元:   {u[:3]}\n    最適化: {o[:3]}  効いた: {o[3]}  足りない: {miss}")
            elif "-v" in sys.argv:
                print(f"ok  {tag} {name}  {o[3]}")
    print(f"\n全部通った ({len(CASES) * 2 + 1})" if not bad else f"\n{bad} 件が食い違い")
    return bad

if __name__ == "__main__": sys.exit(1 if main() else 0)
