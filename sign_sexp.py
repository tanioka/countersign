#!/usr/bin/env python3
"""sign_sexp.py — Sign の構文木を S 式(Lisp の読みの形)で書き出す【拡張】。構文だけで、意味(`_` の吸収・比べが左の値を返す・0 で割れば `_` など)は写さない。

使い方:  python3 sign_sexp.py a.sn        (標準入力なら  python3 sign_sexp.py -)
          python3 sign.py --sexp a.sn      と同じ

読みの決め(設計者の GitHub Discussions #40 の例と確認された木に合わせた):
  * 演算子が先頭、被演算子は書いた順のまま(入れ替えない)。結合の向きは入れ子の形だけを決める
    (`a : b : c` は右、`a - b - c` は左)。operator_table.md の右結合は `: ? # , ^ @`(中置)の 6 つ。
  * `f : x y ? x + y`  →  (setq f (lambda (x y) (+ x y)))        (設計者の投稿の例と同じ)
  * Lisp の記号に使えない演算子(`| ; , ' # @ ~` など)は operator_table.js の名前にする。
  * 空白(余積)は書いた並びのまま (coproduct a b c)。適用か構築かは意味の段が決めるので、ここでは決めない。
  * 括り (block …) は残す(`[x]` ≅ `x` の読みは意味の段の話)。知らない種類の節は (種類 …) とそのまま出す(落ちない)。
"""
import os, re, sys

# 演算子 → S 式の先頭の記号
OPNAME = {
    "+": "+", "-": "-", "*": "*", "/": "/", "%": "mod", "^": "expt",
    "<": "<", "<=": "<=", ">": ">", ">=": ">=", "=": "=", "==": "equal", "!=": "/=", "!==": "xnot-equal",
    "&": "and", "|": "or", ";": "xor", "&&": "bit-and", "||": "bit-or", ";;": "bit-xor",
    "<<": "shift-left", ">>": "shift-right",
    "#": "output", "'": "get-prop", "@": "get-at", "~": "range",
    "~+": "range-arithmetic", "~-": "range-arithmetic-rev", "~*": "range-geometric", "~/": "range-geometric-rev", "~^": "range-power",
    ",": "product",
}
PREFIX = {"not": "not", "neg": "-", "bnot": "bit-not", "addr": "address", "input": "input", "lift": "continuous",
          "abs": "abs", "norm": "norm"}


def sym(name):
    """名前を S 式の記号に。Lisp で読める形はそのまま、そうでなければ |…| で囲む。"""
    s = str(name)
    if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_\-]*", s) and s != "nil" and s != "t": return s
    return "|" + s.replace("\\", "\\\\").replace("|", "\\|") + "|"


def lit(v, tag=None):
    if isinstance(v, bool): return "t" if v else "nil"
    if isinstance(v, int):
        return {"Address": "(address %d)", "UInt": "(uint %d)"}.get(tag, "%d") % v
    if isinstance(v, float): return repr(v)
    if isinstance(v, list): return "(list%s)" % "".join(" " + lit(x) for x in v)
    return '"' + str(v).replace("\\", "\\\\").replace('"', '\\"').replace("\n", "\\n") + '"'


def param(p):
    if isinstance(p, tuple) and p and p[0] == "name":
        return sym(p[1]) if len(p) < 3 or p[2] is None else "(%s %s)" % (sym(p[1]), conv(p[2]))
    if isinstance(p, tuple) and p and p[0] == "destr":
        names = [sym(x) if isinstance(x, str) else conv(x) for x in p[1]]
        rest = [("~" + sym(p[2]))] if len(p) > 2 and isinstance(p[2], str) and p[2] else []
        return "(destructure %s)" % " ".join(names + rest)
    return conv(p)


def conv(n):
    """構文木の節 → S 式の文字列。どんな節でも落ちない。"""
    try:
        return _conv(n)
    except Exception:                                   # 形が想定外でも、読める形で出す
        return generic(n)


def generic(n):
    if isinstance(n, tuple) and n and isinstance(n[0], str):
        return "(%s%s)" % (sym(n[0]), "".join(" " + generic(c) for c in n[1:]))
    if isinstance(n, (list, tuple)): return "(list%s)" % "".join(" " + generic(c) for c in n)
    if isinstance(n, dict): return "(table%s)" % "".join(" (%s %s)" % (sym(k), generic(v)) for k, v in n.items())
    if n is None: return "nil"
    return lit(n) if isinstance(n, (int, float, str)) else sym(n)


def _conv(n):
    k = n[0]
    if k == "id": return sym(n[1])
    if k == "lit": return lit(n[1], n[2] if len(n) > 2 else None)
    if k == "hole": return "unit"
    if k == "def": return "(setq %s %s)" % (sym(n[1]) if isinstance(n[1], str) else conv(n[1]), conv(n[2]))
    if k == "lam": return "(lambda (%s) %s)" % (" ".join(param(p) for p in n[1]), conv(n[2]))
    if k == "cases":
        rows = []
        for c, e in n[1]: rows.append("(%s %s)" % ("t" if c is None else conv(c), conv(e)))
        return "(cond %s)" % " ".join(rows)
    if k == "bin": return "(%s %s %s)" % (OPNAME.get(n[1], sym(n[1])), conv(n[2]), conv(n[3]))
    if k == "cmp":
        ops = n[2]
        if len(set(ops)) == 1: return "(%s %s)" % (OPNAME.get(ops[0], sym(ops[0])), " ".join(conv(x) for x in n[1]))
        return "(compare-chain %s)" % " ".join(
            conv(n[1][0]) + "".join(" %s %s" % (OPNAME.get(o, sym(o)), conv(x)) for o, x in zip(ops, n[1][1:])))
    if k == "prod": return "(product %s)" % " ".join(conv(x) for x in n[1])
    if k == "seq": return "(coproduct %s)" % " ".join(conv(x) for x in n[1])
    if k == "block": return "(block %s)" % conv(n[1])
    if k in PREFIX: return "(%s %s)" % (PREFIX[k], conv(n[1]))
    if k == "post":
        return "(%s %s)" % ({"!": "factorial", "~": "expand", "@": "import"}.get(n[1], sym(n[1])), conv(n[2]))
    if k == "importspread": return "(import-spread %s)" % conv(n[1])
    if k == "sec":                                      # 点なし: [+] の畳み、[+ 1] の部分
        if n[1] == "fold" and isinstance(n[2], str) and n[3] is None: return "(fold %s)" % OPNAME.get(n[2], sym(n[2]))
        return "(section %s)" % " ".join(generic(x) for x in n[1:])
    return generic(n)


def to_sexp(src):
    import sign_interp
    tree = sign_interp.parse_source(src)
    return "\n".join(conv(n) for n in tree)


def main(argv):
    if not argv:
        print("使い方: python3 sign_sexp.py ファイル.sn   (標準入力は -)"); return 2
    path = argv[0]
    try:
        src = sys.stdin.read() if path == "-" else open(path, encoding="utf-8").read()
        print(to_sexp(src))
    except OSError as e:
        print("エラー: %s" % e); return 1
    except Exception as e:                              # 読めないプログラムは、断りを出して普通に終わる
        print("エラー: %s" % e); return 1
    return 0


if __name__ == "__main__":
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    sys.exit(main(sys.argv[1:]))
