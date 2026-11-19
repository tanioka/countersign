"""sign_fuse.py(融合変換 段 0: 純と終わるの判定)の試験。"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sign_interp, sign_fuse

def an(src):
    return sign_fuse.Analysis(sign_interp.parse_source(src, "t.sn"))

CASES = [
 # (名前, 本体, 調べる定義, 純, 終わる)
 ("四則だけ", "sq : x ? x * x\n", "sq", True, True),
 ("比べと枝", "f : x ?\n\tx > 3 : x\n\t0\n", "f", True, True),
 ("書き込み", "w : p v ? p # v\n", "w", False, True),
 ("メモリの読み", "r : p ? @p\n", "r", False, True),
 ("定義の見えない名前", "g : x ? foo x\n", "g", False, True),
 ("純な関数を呼ぶ", "sq : x ? x * x\nc : x ? (sq x) + 1\n", "c", True, True),
 ("書き込みの関数を呼ぶ", "w : p v ? p # v\nc : p ? w p 1\n", "c", False, True),
 ("引数の関数の呼び出しは不明", "ap : f x ? @f x\n", "ap", False, True),
 ("数の再帰(守りが <=)", "g : n ?\n\tn <= 0 : 0\n\tg (n - 1)\n", "g", True, True),
 ("数の再帰(守りが =)は終わると言えない", "f : n ?\n\tn = 0 : 1\n\tn * (f (n - 1))\n", "f", True, False),
 ("数の再帰(別の仮引数と比べる)", "sum : i n acc ?\n\ti >= n : acc\n\tsum (i + 1) n (acc + i)\n", "sum", True, True),
 ("数の再帰(相手を変える)は言えない", "sum : i n acc ?\n\ti >= n : acc\n\tsum (i + 1) (n + 1) (acc + i)\n", "sum", True, False),
 ("数の再帰(進む向きが逆)は言えない", "sum : i n acc ?\n\ti >= n : acc\n\tsum (i - 1) n (acc + i)\n", "sum", True, False),
 ("数の再帰(進み方が字面でない)は言えない", "g : n k ?\n\tn <= 0 : 0\n\tg (n - k) k\n", "g", True, False),
 ("守りの前に再帰がある", "g : n ?\n\tn > 5 : g (n - 1)\n\tn <= 0 : 0\n\t1\n", "g", True, False),
 ("構造再帰", "len : [h ~t] n ?\n\t!t : n + 1\n\tlen t (n + 1)\n", "len", True, True),
 ("構造再帰(残りを別の位置に渡す)は言えない", "f : [h ~t] [a ~b] ?\n\t!t : 0\n\tf b t\n", "f", True, False),
 ("相互再帰は言えない", "ev : n ?\n\tn = 0 : 1\n\tod (n - 1)\nod : n ?\n\tn = 0 : 0\n\tev (n - 1)\n", "ev", True, False),
 ("自分を値として渡す", "f : n ? $f\n", "f", True, False),
 ("終わらない再帰", "loop : n ? loop n\n", "loop", True, False),
 ("純でない関数を経由すると純でない", "w : p ? p # 1\nl : p ?\n\tp <= 0 : 0\n\t(w p) : l (p - 1)\n\t1\n", "l", False, True),
 ("二重定義", "a : 1\na : 2\nb : x ? a\n", "b", False, True),
 ("定数の参照", "K : 10\nf : x ? x + K\n", "f", True, True),
]

def run():
    bad = 0
    for nm, src, d, pure, term in CASES:
        try:
            a = an(src); i = a.info[d]
            ok = (i.pure, i.terminates) == (pure, term)
        except Exception as e:
            ok = False; i = repr(e)
        print(("ok  " if ok else "NG  ") + nm + ("" if ok else "  → %r" % (i,)))
        bad += (not ok)
    # 式の判定
    a = an("sq : x ? x * x\nw : p v ? p # v\n")
    for nm, node_src, pure in [("式: 純な呼び出し", "sq 3\n", True), ("式: 書き込みの呼び出し", "w 1 2\n", False)]:
        node = sign_interp.parse_source("sq : x ? x * x\nw : p v ? p # v\n" + node_src, "t.sn")[-1]
        i = a.expr(node)
        ok = i.pure == pure
        print(("ok  " if ok else "NG  ") + nm + ("" if ok else "  → %r" % (i,)))
        bad += (not ok)
    # std.sn の取り込みを通す: println は書き込みに行き着く
    import sign_asm
    src = "`std.sn`@~\nsq : x ? x * x\nsq 3\n"
    nodes = sign_interp.parse_source(src, os.path.join(os.path.dirname(os.path.abspath(__file__)), "t.sn"))
    sign_asm.IMPORT_DIR[0] = os.path.dirname(os.path.abspath(__file__))
    nodes = sign_asm.expand_imports(nodes)
    a = sign_fuse.Analysis(nodes)
    for nm, d, pure in [("std: println は純でない", "println", False), ("std: 自分の sq は純", "sq", True), ("std: rand_int は純でない", "rand_int", False)]:
        if d not in a.info: print("NG  " + nm + "  → 定義が見つからない"); bad += 1; continue
        ok = a.info[d].pure == pure
        print(("ok  " if ok else "NG  ") + nm + ("" if ok else "  → %r" % (a.info[d],)))
        bad += (not ok)
    print("\n" + ("全部 ok" if not bad else "%d 件 NG" % bad))
    return 1 if bad else 0

if __name__ == "__main__":
    sys.exit(run())
