#!/usr/bin/env python3
"""sign_forth.py — Sign の構文木を後置(Forth の読みの形)で書き出す【拡張】。構文だけで、意味は写さない(実行できる Forth ではない)。

使い方:  python3 sign_forth.py a.sn   (標準入力なら  -)      python3 sign.py --forth a.sn  と同じ

読みの決め(設計者の GitHub Discussions #40 の後置の例に合わせた。`f : x y ? x + y` → `f [x y] [x y +] ? :`):
  * 被演算子は書いた順、演算子はその後ろ(後置)。結合の向きは並べ方だけを決める(`a - b - c` は `a b - c -`、`a ^ b ^ c` は `a b c ^ ^`)。
  * 記号は書いたまま(`:` `;` `?` などは Forth では別の語の綴りだが、設計者の例も同じ綴りを使う)。
  * 括り・関数の仮引数と本体は `[ … ]`(語ごとに空白で区切る)。定義は `名前 値 :`、関数は `[ 仮引数 ] [ 本体 ] ?`。
  * 枝は `{ 条件 値 : … 既定の値 }`、比べの連鎖は `a b c < < chain`、空白(余積)と n 個の積は `… n coproduct`。前置・後置の印は語(not neg …)にした。
"""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from sign_sexp import PREFIX as _PX, lit as _lit
PREFIX = dict(_PX, neg="neg")                         # 前置の符号反転は語 neg(`-` のままだと中置の引き算と区別できない)

def lit(v, tag=None):
    if isinstance(v, list): return "[ " + " ".join(lit(x) for x in v) + " ]" if v else "[ ]"
    return _lit(v, tag).replace("(address ", "").replace("(uint ", "").rstrip(")") if tag in ("Address", "UInt") and isinstance(v, int) else _lit(v, tag)

def param(p):
    if isinstance(p, tuple) and p and p[0] == "name":
        return p[1] if len(p) < 3 or p[2] is None else "%s %s :" % (p[1], conv(p[2]))
    if isinstance(p, tuple) and p and p[0] == "destr":
        return "[ " + " ".join([x if isinstance(x, str) else conv(x) for x in p[1]] + (["~" + p[2]] if len(p) > 2 and isinstance(p[2], str) and p[2] else [])) + " ]"
    return conv(p)

def generic(n):
    if isinstance(n, tuple) and n and isinstance(n[0], str):
        return " ".join([generic(c) for c in n[1:]] + [n[0]])
    if isinstance(n, (list, tuple)): return "[ " + " ".join(generic(c) for c in n) + " ]"
    if isinstance(n, dict): return "{ " + " ".join("%s %s" % (k, generic(v)) for k, v in n.items()) + " }"
    if n is None: return "nil"
    return lit(n) if isinstance(n, (int, float, str)) else str(n)

def conv(n):
    try: return _conv(n)
    except Exception: return generic(n)

def _conv(n):
    k = n[0]
    if k == "id": return n[1]
    if k == "lit": return lit(n[1], n[2] if len(n) > 2 else None)
    if k == "hole": return "unit"
    if k == "def": return "%s %s :" % (n[1] if isinstance(n[1], str) else conv(n[1]), conv(n[2]))
    if k == "lam": return "[ %s ] [ %s ] ?" % (" ".join(param(p) for p in n[1]), conv(n[2]))
    if k == "cases":
        rows = ["%s %s :" % (conv(c), conv(e)) if c is not None else conv(e) for c, e in n[1]]
        return "{ " + " ".join(rows) + " }"
    if k == "bin": return "%s %s %s" % (conv(n[2]), conv(n[3]), n[1])
    if k == "cmp":
        ops = n[2]
        if len(ops) == 1: return "%s %s %s" % (conv(n[1][0]), conv(n[1][1]), ops[0])
        return "%s %s chain" % (" ".join(conv(x) for x in n[1]), " ".join(ops))
    if k == "prod": return "%s %s" % (" ".join(conv(x) for x in n[1]), " ".join([","] * (len(n[1]) - 1)))     # 右結合: x1 x2 x3 , ,
    if k == "seq": return "%s %d coproduct" % (" ".join(conv(x) for x in n[1]), len(n[1]))
    if k == "block": return "[ %s ]" % conv(n[1])
    if k in PREFIX: return "%s %s" % (conv(n[1]), PREFIX[k])
    if k == "post": return "%s %s" % (conv(n[2]), {"!": "factorial", "~": "expand", "@": "import"}.get(n[1], n[1]))
    if k == "importspread": return "%s import-spread" % conv(n[1])
    if k == "sec":
        if n[1] == "fold" and isinstance(n[2], str) and n[3] is None: return "[ %s ] fold" % n[2]
        return generic(n)
    return generic(n)

def to_forth(src):
    import sign_interp
    return "\n".join(conv(n) for n in sign_interp.parse_source(src))

def main(argv):
    if not argv:
        print("使い方: python3 sign_forth.py ファイル.sn   (標準入力は -)"); return 2
    try:
        src = sys.stdin.read() if argv[0] == "-" else open(argv[0], encoding="utf-8").read()
        print(to_forth(src))
    except OSError as e:
        print("エラー: %s" % e); return 1
    except Exception as e:
        print("エラー: %s" % e); return 1
    return 0

if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
