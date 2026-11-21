#!/usr/bin/env python3
"""Sign の整合性の静的検査(実行せずに、構文と型の整合を調べて知らせる)

番地の境界(静的): `--bounds` / `--region=名前:[始まり:]大きさ`(option.ms の `region.名前 : [始まり:]大きさ` も同じ) / `--band=始まり:大きさ[:名前]` / `--display=…` / `--ram=始まり:大きさ` / `--guard=N` のどれかを付けると、
  `a # v` と `@a` で、番地が字面・最上位の定数の名前・その `+ - *` で決まる物が装置の帯からはみ出していれば error [bounds-static]。
  決まらない番地は通す(見逃しはあるが誤検出は無い)。実行時の検査は `--check-bounds`。
使い方:  python sign.py --check file.sn [--json]  (python sign_interp.py --check … ・ python sign_check.py file.sn も同じ)
         file.sn [--json] [--werror] [--no-hint] [--unused] [--strict] [--layer N] [--alpha]
  終了コード 0: 断りなし / 1: 断りがある(--werror なら警告も) / 2: 読めない・構文の誤り

報告の種類(重さ):
  error  仕様の断り。sign_types.py の Pass 3b の帳簿のうち、コンパイルエラーになる物(ERROR_KINDS)。
         ただし STRICT_ONLY の種類(局所の名前の輪・G7 などの先の分からない @・G16 の裸の関数・関数を $ なしで返す・連番スロットの実行時添字・$ を渡す再帰の深さ)は、--strict を付けたときだけ error にし、付けなければ note(根拠は STRICT_ONLY の注)
  note   sign_types.py の帳簿のうち、断りではない物(未定義の識別子が __ に収束する・括りの余りなど。unit.md §0.1)
  hint   参考(この検査器が足した物で、仕様の断りではない): 重複した定義。`--unused` を付けると、どこからも使われない定義も出す
         (ライブラリや、実行環境が名前で呼ぶ入口(init など)は使われていないように見えるので、既定では出さない)
`--no-hint` で hint を出さない。
`--strict` を付けると、`--strict` の断り(G の規則)のうち実行せずに決まる物も error で出す(kind は strict-G4 など。範囲は _strict_reports の説明を見る)。場所は 行:桁(定義の場所は構文木から、識別子は定義の本文の中から探した行)。
"""
import json, os, re, sys

os.environ.setdefault("SIGN_NO_CACHE", "1")          # 構文木の場所の表(POS)を確実に作る
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sign_interp as S
import sign_types as T

# 型の静的パスの error のうち、既定の道では error にしない物(--strict を付けたときだけ error)。値は根拠:
#   (G7 の先の分からない `[@p,]` は、呼び出しが p に関数でない字面(数・文字列)だけを渡すなら unknown-input-called(note。--strict でも断らない)。呼び出しが無い・関数や名前を渡す呼び出しがあれば unknown-input(--strict で error))
#   "run-strict"  既定の道では動き、--strict の実行では本物が断る(実行で確かめた): name-cycle(R80)・unknown-input(G19・G7 のどちらも、既定では動き --strict の実行で断られる例を作って確かめた)
#   "static-only" 既定の道でも --strict でも本物は断らない(実行で確かめた: suika.sn・小さな例)が、型の静的パスは断る(コンパイル側の判定):
#                 bare-function-return(G16)・function-return-without-address(execution_model.md §4)・struct-runtime-index・instance-nest-limit
# いつも error の物: range-no-progress(既定の道の実行でも断る)・float-literal-layer(--layer / option.ms で層を指した時だけ出る。指したのだから断りにする。本物の実行は層を見ない)
STRICT_ONLY = {"name-cycle": "run-strict", "unknown-input": "run-strict",
               "bare-function-return": "static-only", "function-return-without-address": "static-only", "struct-runtime-index": "static-only", "instance-nest-limit": "static-only"}

def _walk(n, f):
    if isinstance(n, tuple):
        f(n)
        for x in n: _walk(x, f)
    elif isinstance(n, list):
        for x in n: _walk(x, f)

def _defs(tree):
    """(名前, def の節, 公開か) の並び(先頭の層だけ)"""
    out = []
    for n in tree:
        pub = False
        if isinstance(n, tuple) and n and n[0] == "export": pub = True; n = n[1]
        if isinstance(n, tuple) and n and n[0] == "def": out.append((n[1], n, pub))
    return out

def _param_names(params):
    names = []
    for sp in params:
        names += [sp[1]] if sp[0] == "name" else list(sp[1]) + list(sp[4] if len(sp) > 4 else []) + ([sp[2]] if sp[2] else [])
    return names

def _strict_reports(src, tree, defs, pos, span):
    """`--strict` の断り(G の規則)のうち、実行せずに決まる物だけ。
      1. 構文を読む段で働く門(G7 の中置の穴・G22 の既定値の綴りなど): 本物の読み取りを --strict で通して、断られた最初の 1 件を出す(読み取りはそこで止まる)
      2. name-shadow(R133: 断りでなく知らせ。severity note): 最上位の関数の定義の仮引数が、最上位の関数の名前(自分の名前も)と同じ(定義の順は問わない。取り込んだ物・入れ子の関数の仮引数は見ない)
         (G4 は --strict では前置 ~ が単一の対象に係る読み(R79)になり、`~1 2 3` は `(~1) 2 3` になるので、断りは起きない)
          3. G19: 口が 3 つ以上と分かる最上位の関数に撒いた並びを最後に当てる形(`add3 xs~`)。実行で空になる撒きは断られないが、静的には分からないので出る
    値の種類や関数の口の数が実行で決まる門(G1 G2 G3 G5 G6 G9 G10 G12 G13 G15 G20 G21 など)は対象外 — `--strict` で実行して確かめる。"""
    out = []
    old = S.STRICT_GATES
    S.STRICT_GATES = True
    try:
        try: S.parse_source(src)
        except (S.SignError, SyntaxError) as e:
            loc = getattr(e, "loc", None)
            ln = loc[1] if loc else getattr(e, "lineno", None)
            m = str(e)
            mg = re.search(r"\bG\d+\b|name-[a-z]+", m)
            out.append({"severity": "error", "kind": "strict-" + (mg.group(0) if mg else "parse"), "where": "<parse>", "line": ln, "col": loc[2] if loc else None, "message": m})
    finally: S.STRICT_GATES = old
    if not out:                                   # 3. name-duplicate(R133・P2): 同じ関数の仮引数どうしの同名は、--strict の実行がファイルごと断る。仮引数の並びだけで決まるので、実行せずに出せる
        old = S.STRICT_GATES; S.STRICT_GATES = True
        try: S.static_param_dup(tree)
        except (S.SignError, SyntaxError) as e:
            loc = getattr(e, "loc", None)
            out.append({"severity": "error", "kind": "strict-name-duplicate", "where": "<parse>", "line": loc[1] if loc else None, "col": loc[2] if loc else None, "message": str(e)})
        finally: S.STRICT_GATES = old
    funs = set()                                  # 最上位の関数の定義の名前(定義の順は関係ない: 実行は先に全部の名前を置く)
    for nm, nd, _ in defs:
        v = nd[2]
        while isinstance(v, tuple) and v and v[0] == "block" and not isinstance(v[1], list): v = v[1]
        if isinstance(v, tuple) and v and v[0] == "lam": funs.add(nm)
    for nm, nd, _ in defs:
        v = nd[2]
        while isinstance(v, tuple) and v and v[0] == "block" and not isinstance(v[1], list): v = v[1]
        if isinstance(v, tuple) and v and v[0] == "lam":
            for pn in _param_names(v[1]):
                if pn in funs:
                    p = pos(nd)
                    out.append({"severity": "note", "kind": "name-shadow", "where": nm, "line": p[1], "col": p[2],
                                "message": f"name-shadow: 仮引数 `{pn}` はファイルの定義 `{pn}` を隠します。この関数の中の `{pn}` は仮引数です(内側が勝つ。§4 R133)"})
    # G19: 口が 3 つ以上と分かる最上位の関数に、撒いた並び `x~` を最後に当てる形(`add3 xs~`・`add4 1 xs~`)。
    #   最上位の定義の口の数が分かる所(名前だけの仮引数で既定値なし、定義が 1 回だけ)に限る。仮引数や局所の定義が同じ名前を隠す所は見ない。
    #   実行時は stream_feed が、残りの口が 1 つでも 2 つでもなければ断る。ただし撒く物が空(`[]~`)なら断られない(実行で確かめた)。書いた `[]~` は除くが、実行で空になる変数の撒きは静的には分からないので出てしまう。書いてあれば出す(実行されなくても)。
    arity = {}; dup = set()
    for nm, nd, _ in defs:
        v = nd[2]
        while isinstance(v, tuple) and v and v[0] == "block" and not isinstance(v[1], list): v = v[1]
        if nm in arity or nm in dup: dup.add(nm); arity.pop(nm, None); continue
        if isinstance(v, tuple) and v and v[0] == "lam" and all(sp[0] == "name" and sp[2] is None for sp in v[1]): arity[nm] = len(v[1])
    def g19(n, who, hidden):
        if isinstance(n, list):
            for x in n: g19(x, who, hidden)
            return
        if not isinstance(n, tuple) or not n: return
        if n[0] == "lam":
            h2 = hidden | set(_param_names(n[1]))
            g19(n[2], who, h2); return
        if n[0] == "cases":
            h2 = hidden                                                              # R128: 本体の `名前 : 値` の行は枝で、局所の定義は無い(名前を隠さない)
            for c, v in n[1]:
                if c is not None: g19(c, who, h2)
                g19(v, who, h2)
            return
        if n[0] == "seq" and isinstance(n[1], list) and len(n[1]) >= 2:
            it = n[1]; h = it[0]
            if h[0] == "id" and h[1] in arity and h[1] not in hidden:
                last = it[-1]; given = len(it) - 2
                if last[0] == "post" and last[1] == "~" and len(last) == 3 and last[2] != ("lit", []) and all(not (x[0] == "post" and x[1] == "~") for x in it[1:-1]):
                    left = arity[h[1]] - given
                    if left >= 3:
                        p = pos(n); r = span(who) if who else None
                        out.append({"severity": "error", "kind": "strict-G19", "where": who or "<top>", "line": p[1] or (r[0] if r else None), "col": p[2],
                                    "message": f"G19: 撒いた並び x~ を受ける関数 {h[1]} の口が残り {left} 個で、1つか2つに決まりません。要素を書き並べるか、括りの関数の最後の口で受けます"})
        for x in n[1:]: g19(x, who, hidden)
    for nm, nd, _ in defs: g19(nd[2], nm, set())
    for n in tree:
        if isinstance(n, tuple) and n and n[0] not in ("def", "export"): g19(n, None, set())
    return out

def _bounds_reports(tree, defs, pos, span, spec):
    """番地の境界の静的検査(実行時の --check-bounds と同じ規則を、字面と定数の算術で決まる番地にだけ当てる)。
    spec = {"bands": [(base, size, 名前)], "guard": 見張る幅, "rams": [(始まり, 大きさ)]}。
    `a # v` の書き込みと `@a` の読み込みで、a が `0x…`・整数の字面・最上位の定数の名前・その `+ - *` の算術で決まる物だけを調べる。
    決まらない番地(引数・読んだ値・関数の戻り)は黙って通す(見逃しはあるが、誤検出は出ない)。局所の名前(仮引数・局所の定義)が最上位の定数を隠す所は決めない。"""
    consts = {}                                       # 最上位の `名前 : 式` の式(定数の候補)
    for nm, nd, _ in defs:
        body = nd[2]
        if isinstance(body, tuple) and body and body[0] != "lam": consts.setdefault(nm, body)
    S.DEVICES.clear()
    for base, size, name in spec["bands"]:
        S.DEVICES.append(type(name, (), {"base": base, "size": size})())
    S.BOUNDS[0] = True; S.BOUNDS[1] = spec["guard"]; S.BOUNDS[2][:] = list(spec["rams"])
    memo = {}
    regions = spec.get("regions", {})                  # 名前 → (始まり or None, 大きさ)。名前は最上位の定数の名前(`fb : 0x9100000`)
    def fold(n, hidden, stack=()):
        """(領域の名前 or None, 値) か None。領域の名前は、最上位の定数 fb が宣言した領域の始まりを指すとき、fb + 定数 の形に付く(意図した参照先)"""
        if not isinstance(n, tuple) or not n: return None
        k = n[0]
        if k == "lit": return (None, n[1]) if type(n[1]) is int else None
        if k == "block": return None if isinstance(n[1], list) else fold(n[1], hidden, stack)
        if k == "seq" and isinstance(n[1], list) and len(n[1]) == 1: return fold(n[1][0], hidden, stack)
        if k == "id":
            nm = n[1]
            if nm in hidden or nm in stack: return None
            if nm not in memo:
                v = fold(consts[nm], set(), stack + (nm,)) if nm in consts else None
                if v is None and nm in regions and regions[nm][0] is not None: v = (None, regions[nm][0])
                if v is not None and nm in regions and v[0] is None: v = (nm, v[1])      # 領域の始まりそのもの
                memo[nm] = v
            return memo[nm]
        if k == "neg":
            v = fold(n[1], hidden, stack); return None if v is None or v[0] else (None, -v[1])
        if k == "bin" and len(n) == 4 and n[1] in ("+", "-", "*"):
            a = fold(n[2], hidden, stack); b = fold(n[3], hidden, stack)
            if a is None or b is None: return None
            if n[1] == "*": return None if a[0] or b[0] else (None, a[1] * b[1])
            if n[1] == "+":
                if a[0] and b[0]: return None
                return (a[0] or b[0], a[1] + b[1])
            if b[0]: return (None, a[1] - b[1]) if a[0] == b[0] else None      # 同じ領域どうしの差は数
            return (a[0], a[1] - b[1])
        return None
    out = []
    def report(n, who, kind, msg):
        p_ = pos(n); r = span(who) if who and who != "<top>" else None
        out.append({"severity": "error", "kind": kind, "where": who or "<top>", "line": p_[1] or (r[0] if r else None), "col": p_[2], "message": msg})
    def in_region(reg, v):
        """領域 reg の中の値 v か。外なら文面を返す"""
        base = memo.get(reg) and memo[reg][1]
        size = regions[reg][1]
        if base is None or base <= v < base + size: return None
        return f"領域 {reg} [0x{base:x}, 0x{base + size:x}) の外です(始まりから {v - base:+d})"
    def visit(n, who, hidden):
        if not isinstance(n, tuple) or not n: return
        if n[0] == "lam":
            visit(n[2], who, hidden | set(_param_names(n[1]))); return
        if n[0] == "cases":
            h2 = hidden | {c[1] for c, _ in n[1] if c is not None and c[0] == "id"}
            for c, v in n[1]:
                if c is not None: visit(c, who, h2)
                visit(v, who, h2)
            return
        a = op = None
        if n[0] == "bin" and len(n) == 4 and n[1] == "#": a, op = fold(n[2], hidden), "書き込み"
        elif n[0] == "input": a, op = fold(n[1], hidden), "読み込み"
        if a is not None:
            reg, v = a
            m = None
            if reg: m = in_region(reg, v)
            if m: m = f"境界: {op}の番地 0x{v:x} は{m}"
            elif v >= 0: m = S.bounds_error(v, op)
            else: m = f"境界: {op}の番地 {v} は負です"
            if m is not None: report(n, who, "bounds-region" if reg else "bounds-static", m)
        elif n[0] == "bin" and len(n) == 4 and n[1] == "~":                 # 範囲 [始め ~ 終わり] と刻み付き [始め ~+ 刻み ~ 終わり](Iterator・スライス)
            X = n[2]
            while isinstance(X, tuple) and X and X[0] == "block" and not isinstance(X[1], list): X = X[1]
            if isinstance(X, tuple) and X[0] == "bin" and len(X) == 4 and X[1] in ("~+", "~-"):
                st, sp_, en = fold(X[2], hidden), fold(X[3], hidden), fold(n[3], hidden); sgn = 1 if X[1] == "~+" else -1
                ok = st and sp_ and en and not sp_[0] and sp_[1] * sgn != 0
                step = sp_[1] * sgn if ok else 0
            else:
                st, en = fold(X, hidden), fold(n[3], hidden); ok = st and en; step = (1 if ok and st[1] <= en[1] else -1)
            if ok and (st[0] or en[0]) and (st[0] == en[0] or not st[0] or not en[0]):
                reg = st[0] or en[0]; lo, hi = st[1], en[1]
                if (step > 0) == (hi >= lo):                                      # 刻みが終わりへ向かうときだけ要素がある
                    last = lo + ((hi - lo) // step) * step
                    for label, v in (("始め", lo), ("最後の要素", last)):
                        m = in_region(reg, v)
                        if m: report(n, who, "bounds-region", f"境界: 範囲の{label} 0x{v:x} は{m}"); break
        for x in n[1:]:
            if isinstance(x, list):
                for y in x: visit(y, who, hidden)
            else: visit(x, who, hidden)
    for nm_ in regions: fold(("id", nm_), set())                                   # 領域の始まりを先に決めておく
    for nm, nd, _ in defs: visit(nd[2], nm, set())
    for n in tree:
        if isinstance(n, tuple) and n and n[0] not in ("def", "export"): visit(n, None, set())
    have = {(r_["line"], r_["col"], r_["message"]) for r_ in out}
    out += [r_ for r_ in _bounds_sim(tree, defs, consts, fold, in_region, pos, span, regions) if (r_["line"], r_["col"], r_["message"]) not in have]      # 字面で決まる番地は上の走査と重ねて出さない
    S.BOUNDS[0] = False; S.BOUNDS[2][:] = []; S.DEVICES.clear()
    return out

def _bounds_sim(tree, defs, consts, fold, in_region, pos, span, regions, fuel=300000):
    """引数や輪の回数で決まる番地の検査。最上位の式・定義を上から順に、整数の部分だけを実際に辿る(定数の実引数で関数を呼び、行の条件を決め、末尾呼びを輪として回す)。
    辿れるのは、整数の算術 `+ - *`・比べ・`a # v`・`@a`・最上位の関数の呼び(口の数が合う物)・行の条件が決まる `cases` だけ。条件が決まらない・知らない形に当たったらその道はそこで止める。
    辿った道で実際に起きるアクセスだけを調べるので、確実に起きるはみ出しだけが error(誤検出は無い)。書く値が分からない(単位かもしれない)書き込みを通った後の報告は、note(kind bounds-path。値が単位なら実行されない)。"""
    funcs = {nm: nd[2] for nm, nd, _ in defs if isinstance(nd[2], tuple) and nd[2] and nd[2][0] == "lam"}
    found = []; seen = {}; st = {"fuel": fuel, "certain": True}
    class Stop(Exception): pass
    def arith(op, a, b):
        if a is None or b is None: return None
        if op == "*": return None if a[0] or b[0] else (None, a[1] * b[1])
        if op == "+": return None if (a[0] and b[0]) else (a[0] or b[0], a[1] + b[1])
        if b[0]: return (None, a[1] - b[1]) if a[0] == b[0] else None
        return (a[0], a[1] - b[1])
    def access(n, who, val, op):
        if val is None: return
        reg, v = val
        m = in_region(reg, v) if reg else None
        if m: m = f"境界: {op}の番地 0x{v:x} は{m}"
        elif v >= 0: m = S.bounds_error(v, op)
        else: m = f"境界: {op}の番地 {v} は負です"
        if m is None: return
        p_ = pos(n); r_ = span(who) if who and who != "<top>" else None
        line = p_[1] or (r_[0] if r_ else None)
        key = (line, p_[2], st["certain"])
        if key in seen:
            seen[key]["_n"] += 1; return
        seen[key] = None
        found.append({"severity": "error" if st["certain"] else "note", "kind": ("bounds-region" if reg else "bounds-static") if st["certain"] else "bounds-path", "where": who or "<top>", "line": line, "col": p_[2],
                      "message": m + ("" if st["certain"] else "(書く値が単位でなければ起きます)"), "_n": 1})
        seen[key] = found[-1]
    def strip(n):
        while isinstance(n, tuple) and n and n[0] == "block" and not isinstance(n[1], list): n = n[1]
        return n
    def ev(n, env, who, depth):
        st["fuel"] -= 1
        if st["fuel"] <= 0: raise Stop()
        n = strip(n)
        if not isinstance(n, tuple) or not n: return None
        k = n[0]
        if k == "lit": return (None, n[1]) if type(n[1]) is int else None
        if k == "id":
            if n[1] in env: return env[n[1]]
            return fold(n, set(env)) if n[1] in consts or n[1] in regions else None
        if k == "neg":
            v = ev(n[1], env, who, depth); return None if v is None or v[0] else (None, -v[1])
        if k == "bin" and len(n) == 4 and n[1] in ("+", "-", "*"): return arith(n[1], ev(n[2], env, who, depth), ev(n[3], env, who, depth))
        if k == "bin" and len(n) == 4 and n[1] == "#":
            a = ev(n[2], env, who, depth); d = ev(n[3], env, who, depth)
            if a is None: raise Stop()
            if d is None: st["certain"] = False
            access(n, who, a, "書き込み"); return a
        if k == "input":
            a = ev(n[1], env, who, depth)
            if a is not None: access(n, who, a, "読み込み")
            return None
        if k == "seq" and isinstance(n[1], list) and n[1]:
            items = n[1]; h = items[0]
            if h[0] == "id" and h[1] in funcs and h[1] not in env and len(items) - 1 == len(funcs[h[1]][1]) and all(sp[0] == "name" and sp[2] is None for sp in funcs[h[1]][1]):
                args = [ev(x, env, who, depth) for x in items[1:]]
                return call(h[1], args, depth + 1)
            for x in items[1:]: ev(x, env, who, depth)          # 関数の呼びの実引数は先に評価される(副作用は起きる)
            return None
        return None
    def cond(c, env, who, depth):
        c = strip(c)
        if not isinstance(c, tuple) or not c: return None
        if c[0] == "cmp" and len(c[1]) == 2 and len(c[2]) == 1 and c[2][0] in ("=", "==", "!=", "<", "<=", ">", ">="):
            a = ev(c[1][0], env, who, depth); b = ev(c[1][1], env, who, depth)
            if a is None or b is None: return None
            x, y, o = a[1], b[1], c[2][0]
            return x == y if o in ("=", "==") else x != y if o == "!=" else x < y if o == "<" else x <= y if o == "<=" else x > y if o == ">" else x >= y
        if c[0] == "bin" and len(c) == 4 and c[1] == "#":
            a = ev(c, env, who, depth); return True if a is not None else None
        return None
    def call(name, args, depth):
        if depth > 150 or any(a is None for a in args): raise Stop()
        while True:
            lam = funcs[name]; env = {sp[1]: a for sp, a in zip(lam[1], args)}; body = strip(lam[2])
            rows = body[1] if isinstance(body, tuple) and body[0] == "cases" else [(None, body)]
            localdefs = len(rows) > 1 and rows[-1][0] is None and all(c is not None and strip(c)[0] == "id" for c, _ in rows[:-1])
            for c, v in rows:
                if c is not None and localdefs:
                    cn = strip(c)[1]
                    if cn in env or cn in funcs: raise Stop()
                    r = ev(v, env, name, depth); 
                    if r is None: raise Stop()
                    env[cn] = r; continue
                t = True if c is None else cond(c, env, name, depth)
                if t is None: raise Stop()
                if not t: continue
                v = strip(v)
                if isinstance(v, tuple) and v[0] == "seq" and isinstance(v[1], list) and v[1] and v[1][0][0] == "id" and v[1][0][1] in funcs and v[1][0][1] not in env and len(v[1]) - 1 == len(funcs[v[1][0][1]][1]) and all(sp[0] == "name" and sp[2] is None for sp in funcs[v[1][0][1]][1]):
                    args = [ev(x, env, name, depth) for x in v[1][1:]]           # 末尾呼び: 輪として回す
                    if any(a is None for a in args): raise Stop()
                    name = v[1][0][1]; break
                return ev(v, env, name, depth)
            else: raise Stop()
    for n in tree:
        try:
            if isinstance(n, tuple) and n and n[0] == "def" and not (isinstance(n[2], tuple) and n[2] and n[2][0] == "lam"): ev(n[2], {}, n[1], 0)
            elif isinstance(n, tuple) and n and n[0] not in ("def", "export"): ev(n, {}, None, 0)
        except Stop: pass
        except RecursionError: pass
        st["certain"] = True
        if st["fuel"] <= 0: break
    for r_ in found:
        n_ = r_.pop("_n")
        if n_ > 1: r_["message"] += f"(この行で同じはみ出しがほかに {n_ - 1} 回起きます。最初の1回を示しています)"
    return found

def check(src, base_dir=".", layer=None, alpha=False, hints=True, unused=False, strict=False, bounds=None):
    """報告の list: {"severity", "kind", "where", "line", "col", "message"}。構文の誤りは例外 S.SignError"""
    S.POS.clear()
    tree = S.parse_source(src)
    pos = lambda node: (S.POS.get(id(node)) or (None, None, None))
    defs = _defs(tree)
    lines = src.split("\n")
    starts = sorted((pos(nd)[1], nm) for nm, nd, _ in defs if pos(nd)[1])
    def span(name):                                   # 定義の本文の行の範囲 [始まり, 次の定義の手前]
        for i, (ln, nm) in enumerate(starts):
            if nm == name: return ln, (starts[i + 1][0] - 1 if i + 1 < len(starts) else len(lines))
        return None
    def find_line(where, word):                       # 識別子が出る最初の行(定義の中、なければ全体)
        r = span(where) if where != "<top>" else None
        lo, hi = r if r else (1, len(lines))
        rx = re.compile(r"(?<![\w'])" + re.escape(word) + r"(?![\w])")
        for ln in range(lo, hi + 1):
            if rx.search(lines[ln - 1]): return ln
        return None
    out = []
    chk = T.infer(src, base_dir, layer, alpha)
    for kind, where, detail in chk.diags:
        sev = "error" if kind in T.ERROR_KINDS else "note"
        only = kind in STRICT_ONLY
        if only and not strict: sev = "note"                       # 既定の道では通る形: --strict のときだけ断りにする
        ln = None; col = None
        m = re.match(r"^\S+$", detail)
        if kind == "undefined-identifier" and m: ln = find_line(where, detail)
        if ln is None and where != "<top>":
            r = span(where); ln = r[0] if r else None
        out.append({"severity": sev, "kind": kind, "where": where, "line": ln, "col": col, "message": detail + (" (--strict なら断り)" if only and not strict else ""), **({"strict_only": True, "basis": STRICT_ONLY[kind]} if only else {})})
    if strict: out += _strict_reports(src, tree, defs, pos, span)
    if bounds is not None: out += _bounds_reports(tree, defs, pos, span, bounds)
    if hints:
        seen = {}
        for nm, nd, pub in defs:
            if nm in seen:
                p = pos(nd)
                out.append({"severity": "hint", "kind": "duplicate-definition", "where": nm, "line": p[1], "col": p[2],
                            "message": f"{nm} は {seen[nm]} 行目にも定義があります(後の定義が前を隠します)"})
            else: seen[nm] = pos(nd)[1]
        refs = {}                                     # 名前 → その名前を『自分以外の定義・式』が使う回数
        for nm, nd, pub in defs:
            def cnt(n, nm=nm, who=nm):
                if n and n[0] == "id" and len(n) > 1: refs.setdefault(n[1], set()).add(who)
            _walk(nd[2], cnt)
        for n in tree:                                # 定義でない式(根の式)も使い手
            if isinstance(n, tuple) and n and n[0] not in ("def", "export"):
                def cnt2(m_):
                    if m_ and m_[0] == "id" and len(m_) > 1: refs.setdefault(m_[1], set()).add("<top>")
                _walk(n, cnt2)
        for nm, nd, pub in (defs if unused else []):
            if pub: continue
            if not (refs.get(nm, set()) - {nm}):
                p = pos(nd)
                out.append({"severity": "hint", "kind": "unused-definition", "where": nm, "line": p[1], "col": p[2],
                            "message": f"{nm} はどこからも使われていません(公開 # でもありません)"})
    out.sort(key=lambda d: (d["line"] or 10**9, {"error": 0, "note": 1, "hint": 2}[d["severity"]]))
    return out

def main(argv):
    if not [a for a in argv if not a.startswith("--")]: print(__doc__); return 2
    layer = None
    if "--layer" in argv:
        i = argv.index("--layer"); layer = int(argv[i + 1]); del argv[i:i + 2]
    bounds = None
    bands = []; rams = []; guard = 0x100
    regions = {}
    for a in [a for a in argv if a.startswith("--region=")]:                       # --region=名前:大きさ か 名前:始まり:大きさ(名前は最上位の定数の名前)
        argv.remove(a); f = a[9:].split(":"); regions[f[0]] = (int(f[1], 0), int(f[2], 0)) if len(f) == 3 else (None, int(f[1], 0)); bounds = bounds or {}
    for a in [a for a in argv if a.startswith("--band=") or a.startswith("--display") or a.startswith("--ram=") or a.startswith("--guard=") or a == "--bounds"]:
        argv.remove(a)
        if a == "--bounds": bounds = bounds or {}
        elif a.startswith("--band="):                  # --band=始まり:大きさ[:名前]
            f = a[7:].split(":"); bands.append((int(f[0], 0), int(f[1], 0), f[2] if len(f) > 2 else "Band")); bounds = bounds or {}
        elif a.startswith("--display"):                # --display=… : 帯だけを使う(画面の大きさ WxH があれば帯の大きさに反映。無ければ既定)
            import sign_gfx
            m = re.search(r"(\d+)x(\d+)", a); d = sign_gfx.Display(int(m.group(1)), int(m.group(2)), "null") if m else sign_gfx.parse_spec("null")
            bands.append((d.base, d.size, "Display")); bounds = bounds or {}
        elif a.startswith("--ram="): s_, z_ = a[6:].split(":"); rams.append((int(s_, 0), int(z_, 0))); bounds = bounds or {}
        elif a.startswith("--guard="): guard = int(a[8:], 0); bounds = bounds or {}
    path = [a for a in argv if not a.startswith("--")][0]
    for k_, v_ in T.read_option(os.path.dirname(os.path.abspath(path))).items():        # option.ms の `region.名前 : 始まり:大きさ`(始まりは省ける)
        if k_.startswith("region."):
            f = v_.split(":"); regions.setdefault(k_[7:], (int(f[0], 0), int(f[1], 0)) if len(f) == 2 else (None, int(f[0], 0))); bounds = bounds or {}
    if bounds is not None: bounds = {"bands": bands, "guard": guard, "rams": rams, "regions": regions}
    try: src = open(path, encoding="utf-8").read()
    except OSError as e: print(f"読めません: {e}", file=sys.stderr); return 2
    base = os.path.dirname(os.path.abspath(path))
    if layer is None: layer = T.read_layer(base)
    try: rep = check(src, base, layer, "--alpha" in argv, "--no-hint" not in argv, "--unused" in argv, "--strict" in argv, bounds)
    except (S.SignError, SyntaxError) as e:
        loc = getattr(e, "loc", None)
        ln = loc[1] if loc else getattr(e, "lineno", None); co = loc[2] if loc else getattr(e, "offset", None)
        msg = {"severity": "error", "kind": "syntax", "where": "<file>", "line": ln, "col": co, "message": getattr(e, "msg", None) or str(e)}
        if "--json" in argv: print(json.dumps({"file": path, "ok": False, "reports": [msg]}, ensure_ascii=False, indent=1))
        else: print(f"{path}:{msg['line'] or '?'}: error [syntax] {msg['message']}")
        return 2
    nerr = sum(r["severity"] == "error" for r in rep); nwarn = sum(r["severity"] == "note" for r in rep); nhint = sum(r["severity"] == "hint" for r in rep)
    bad = nerr > 0 or ("--werror" in argv and nwarn > 0)
    if "--json" in argv:
        print(json.dumps({"file": path, "ok": not bad, "errors": nerr, "notes": nwarn, "hints": nhint, "reports": rep}, ensure_ascii=False, indent=1))
    else:
        for r in rep:
            where = f"{path}:{r['line'] or '?'}" + (f":{r['col']}" if r["col"] else "")
            print(f"{where}: {r['severity']} [{r['kind']}] {r['where']}: {r['message']}")
        print(f"\n{path}: 断り {nerr} 件 / 注意 {nwarn} 件 / 参考 {nhint} 件" + ("  → 整合しています" if not bad and not rep else ""))
    return 1 if bad else 0

if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
