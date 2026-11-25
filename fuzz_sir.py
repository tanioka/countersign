"""乱数で整数の式・関数を作り、strict の評価器と SIR の評価を照合する(前段)。
使い方: python3 fuzz_sir.py [件数=2000] [種=1]     終了コード: 食い違いがあれば 1"""
import sys, os, io, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__))); sys.setrecursionlimit(20000)
import sign_interp as S, sign_sir as R
from fixblank import fix

LIST_RATE = [0.0]
DEF_RATE = [0.0]
PARTIAL = [False]
STRINGS = [False]                  # --strings: 文字列・文字の定数(S1。SIR_VALUES.md)
FLOATS = [False]                   # --floats: Float の字面と算術(S4)
STRUCTS = [False]                  # --structs: 欄ブロック・欄引き・コンストラクタ(S3・S5)
NAMES = [False]                    # --names: 定義の無い名前 zz を式に混ぜる(R21 で `!_`)
FLOW_RATE = [0.0]
NOVOID = [False]
def num(r):
    return str(r.choice([0, 1, 2, 3, 5, 7, 10, 100, 9223372036854775807]))
def atom(r, ps):
    c = r.random()
    if ps and c < .4: return r.choice(ps)
    if NAMES[0] and c < .15: return "zz"
    if c < .5 and not NOVOID[0]: return "__"
    return num(r)
def expr(r, ps, d):
    if d <= 0 or r.random() < .25: return atom(r, ps)
    c = r.random(); a = expr(r, ps, d-1); b = expr(r, ps, d-1)
    if c < .55: return f"({a} {r.choice('+-*/%')} {b})"
    if c < .75: return f"({a} {r.choice(['<','>','<=','>=','==','!=','='])} {b})"
    if c < .83: return f"({a} {r.choice('&|')} {b})"
    if c < .88: return f"(0 - {a})" if r.random() < .6 else f"|{a}|"
    if c < .94:
        o = r.choice(["<", "<="]); return f"({a} {o} {b} {o} {expr(r, ps, d-1)})"
    if c < .97:
        op = r.choice(["<", ">", "<=", ">=", "==", "="])
        xs = [atom(r, ps) if r.random() < .7 else "(" + expr(r, ps, d-1) + ")" for _ in range(r.randint(1, 4))]
        return f"([{op}] {' '.join(xs)})"
    return f"({a} = {b} = {expr(r, ps, d-1)})"
FLOW_G = "g : x ? x + 1\nk : x y ? x + y\nm : a b c ? a + b + c\np : x ? g (x > 5)\nsb : a b ? a - b\ndv : a b ? a / b\nh3 : a b c ? a * b - c\n"
def vexp(r, ps):
    return r.choice(["__", "__", "(x > 5)", "(3 > 5)", "(7 > 5)"]) if ps else r.choice(["__", "(3 > 5)", "(7 > 5)", "4"])
def fitem(r, ps):
    c = r.random()
    if c < .35: return atom(r, ps) if ps and r.random() < .3 else str(r.choice([1, 2, 5, 7, 8, 100]))
    if c < .55: return f"(g {vexp(r, ps)})"
    if c < .72: return f"(k {r.choice(['4', vexp(r, ps)])} {vexp(r, ps)})"
    if c < .85: return f"(m {vexp(r, ps)} {r.choice(['1', vexp(r, ps)])} {r.choice(['2', vexp(r, ps)])})"
    if c < .88: return f"(m {vexp(r, ps)})"
    if c < .91: return f"(sb {r.choice(['10', '3', vexp(r, ps)])} {vexp(r, ps)})"                # 順序で答えが変わる関数(合成の向きの確かめ)
    if c < .94: return f"(dv {r.choice(['100', '7', vexp(r, ps)])} {r.choice(['0', '3', vexp(r, ps)])})"
    if c < .96: return f"(h3 {r.choice(['4', vexp(r, ps)])} {vexp(r, ps)})"
    return f"(p {r.choice(ps) if ps else '3'})"
def flow_program(r):
    n = r.randint(1, 6)
    top = " ".join(fitem(r, []) for _ in range(n))
    if r.random() < .5:
        body = " ".join(fitem(r, ["x"]) for _ in range(r.randint(1, 6)))
        return FLOW_G + f"f : x ? {body}\n" + (f"f {r.choice([3, 9])}\n" if r.random() < .8 else top + "\n")
    return FLOW_G + top + "\n"
def lst(r):
    return " ".join(r.choice(["0","1","-5","7","100","9223372036854775807","-9223372036854775807"]) for _ in range(r.randint(2, 5)))
def lexpr(r, names, d):
    """リストを使う式(関数の外の式だけ。関数の中の添字は SIR が断る)。"""
    c = r.random()
    if c < .12: return f"({r.choice(names)} ' {r.choice(names)})"                   # 鍵が名前: 欄の名前なので void(R64)
    if c < .45: return f"({r.choice(names)} ' {expr(r, [], 1)})"
    if c < .6: return f"||{r.choice(names)}||"
    if d <= 0: return num(r)
    a, b = lexpr(r, names, d-1), lexpr(r, names, d-1)
    return f"({a} {r.choice(['+','-','*','/','%','|','&','<','=='])} {b})"
def list_program(r):
    names = ["la", "lb"][:r.randint(1, 2)]
    defs = "\n".join(f"{n} : {lst(r)}" for n in names) + "\n"
    if r.random() < .4:                                                    # リストを受ける関数。鍵が仮引数の名前なら欄の名前で void(R64)
        k = r.choice(["0", "1", "2", "-1", "i", "9"])
        body = r.choice([f"(xs ' {k}) + ||xs||", f"xs ' {k}", f"||xs|| * (xs ' {k})", f"(xs ' {k}) | (xs ' 0)", f"((xs ' {k}) < 100) + 1"])
        defs += f"gf : xs i ? {body}\n"
        return defs + f"gf {r.choice(names)} {r.choice(['2', '1', '(1 < 0)', num(r)])}\n"
    if r.random() < .35:                                                   # 器の算術(`List * n` は n 回コピー、`+ - %` は `!_`)
        n0 = r.choice(names); k = r.choice(["2", "3", "1", "0", "-1", "__", "(1 < 0)", "1.5", "la", "(la ' 0)"])
        body = r.choice([f"{n0} * {k}", f"{n0} {r.choice('+-%/')} {k}", f"{k} * {n0}", f"||{n0} * {k}||", f"({n0} * {k}) ' {r.choice(['0', '3', '-1', '9'])}", f"({n0} * 2) * 2", f"5 + ({n0} + 1)", f"({n0} + 1) | 7", f"{n0} * 2 + 1"])
        return defs + body + "\n"
    return defs + lexpr(r, names, 3) + "\n"
def defaults_program(r):
    """既定値のある関数(整数の字面の既定値。既定値の無い口が先)と、その呼び。実引数は単位になりうる式も混ぜる。"""
    nreq = r.randint(1, 2); nd = r.randint(1, 2)
    req = ["x", "y"][:nreq]; dfl = [("p", r.choice([0, 1, -3, 7])), ("q", r.choice([2, 5, 100]))][:nd]
    ps = req + [d[0] for d in dfl]
    body = expr(r, ps, 2)
    head = "gd :\n" + "".join(f"\t\t{n}\n" for n in req) + "".join(f"\t\t{n} : {v}\n" for n, v in dfl) + f"\t? {body}\n\n"
    def arg(): return r.choice(["__", "(3 < 2)", num(r), "(" + expr(r, [], 1) + ")"]) if r.random() < .4 else num(r)
    call = "gd " + " ".join(arg() for _ in range(r.randint(nreq, nreq + nd + (1 if r.random() < .2 else 0))))   # 口より 1 つ多い呼びは、余りが流れになる
    if r.random() < .4: call = f"({call}) {r.choice('+-*')} {num(r)}"
    return head + call + "\n"
def partial_program(r):
    """行の値(枝の値・既定の行)が部分適用になりうる関数。実引数が単位になる呼び・足りない呼びを行の値に置く。"""
    vals = ["add (3 < 2)", "add 1", "add 1 2", "x", "7", "(x + 1)", "add __ 4", "k (3 < 2)", "k 2"]
    n = r.randint(1, 3); rows = []
    for i in range(n):
        c = r.choice(["x > 0", "x < 3", "x = 5", "x > 100", "(3 < 2)"])
        rows.append(f"\t{c} : {r.choice(vals)}")
    if r.random() < .8: rows.append(f"\t{r.choice(vals)}")
    head = "add : a b ? a + b\nk : a ? a * 2\nf : x ?\n" + "\n".join(rows) + "\n\n"
    call = f"f {r.choice(['5', '3', '0', '(0 - 4)'])}"
    if r.random() < .3: call = f"({call}) {r.choice('+-*')} {num(r)}"
    if r.random() < .15: call += " " + num(r)
    return head + call + "\n"
def strings_program(r):
    """文字列・文字の名前と、長さ・文字の答え・断る形を混ぜる。使える形は `||s||`(長さ)・文字の名前・答え。ほかは SIR が断るか、断らずに strict と合う"""
    al = "abcdefgh"
    s1 = "".join(r.choice(al) for _ in range(r.randint(1, 6))); s2 = "".join(r.choice(al) for _ in range(r.randint(1, 4)))
    c1 = r.choice(al); c2 = r.choice(al)
    head = f"s : `{s1}`\nt : `{s2}`\nc : \\{c1}\nd : \\{c2}\nk : 1\n"
    n = lambda: r.choice(["||s||", "||t||", "||c||", "||`" + s1 + "`||", num(r), "(||s|| - ||t||)", "(||s|| * 3)", "(||s|| / 2)"])
    pick = r.random()
    if pick < .25: body = f"{n()} {r.choice('+-*/%')} {n()}"
    elif pick < .4: body = f"({n()} {r.choice(['<','>','=','!='])} {n()}) & {n()}"
    elif pick < .5: body = r.choice(["c", "d", "(c | d)", "(5 & c)", "(__ | d)", "(c & d)", "(c = d)", "(c < d)", "(c + 1)", "(c - 1)", "(c + d)", "(c - d)", "(1 + c)", "(c * 3)", "||c * 3||", "(c * 0)", "(c / 2)", "(c + 100)", "(c - 200)", "((c + 1) + 1)", "(0 + c)", "(3 * c)", "(c * d)", "(k - c)", "(c + __)", "(c + k)", "(c - k)", "((c * 3) ' 1)"])
    elif pick < .6: body = r.choice(["s", "t", "(s | t)", "(s = t)", "(s + 1)", "||s + 1||", "(1 + s)", "(s - t)", "(s / 2)", "|s|", "-s", "(s * 2)", "(s * 0)", "(s * -1)", "||s * 3||", "(s * t)", "(2 * s)", "((s * 2) ' 3)", "(s * 2) * 2", "(5 + (s + 1))", "(s == s)", "(s = s)"])
    elif pick < .72: i = r.choice(["0", "1", "2", "-1", "-2", "-3", "5", "9", "-9", "__", "(2 - 5)", "9223372036854775807", "k"]); body = r.choice([f"(s ' {i})", f"(t ' {i})", f"||s ' {i}||", f"((s ' {i}) | 7)", f"(3 & (s ' {i}))", f"((s ' {i}) + 1)"])
    elif pick < .75: head += f"u : s ' {r.choice(['0', '1', '4', '-1'])}\n"; body = r.choice(["u", "(u | 5)", "||u||", "(c | u)"])             # 値が字面でない定義は機械語が断る(定義の本体が文字列の添字)
    elif pick < .8: return head + f"f : x ? x + {n()}\nf {num(r)}\n"
    elif pick < .9: return head + f"f : x ?\n\t{n()} > x : {n()}\n\t{n()}\n\nf {r.choice(['1', '3', '9'])}\n"
    elif pick < .93: return head + f"f : x ? ||x||\nf {r.choice(['s', 'c', '`ab`', '5'])}\n"
    else:                                                                       # S2: 文字列・文字を関数へ渡す・返す
        arg = lambda: r.choice(["s", "t", "c", "d", "`ab`", "\\\\z", "(s ' 1)", "(s ' 9)", "(t ' 0)", "5", "__"])
        body = r.choice(["x", "||x||", "(x ' 0)", "(x ' -1)", "(x ' 5)", "(x + 1)", "||x|| + 1", "(x = x)", "|x|", "(x | 7)", "(3 & x)", "(||x|| > 1)"])
        two = r.random() < .3
        if two: return head + f"f : x y ? {r.choice(['||x|| + ||y||', '(x ' + str(r.choice([0, 1, -1])) + ')', 'y', '(y ' + chr(39) + ' 0)', 'x'])}\nf {arg()} {arg()}\n"
        pre = f"g : x ? {r.choice(['x', '(x ' + chr(39) + ' 1)', '||x||'])}\n" if r.random() < .3 else ""
        call = f"f {arg()}" if not pre else r.choice([f"f (g {arg()})", f"||g {arg()}||", f"g {arg()}"])
        return head + pre + f"f : x ? {body}\n{call}\n"
    return head + body + "\n"
def structs_program(r):
    """S3・S5: 欄ブロック・欄引き `'`・コンストラクタ・入れ子・欄の長さ・関数へ渡す。欄の名前・位置・文字列の鍵・範囲外・単位の欄・値の名前の鍵を混ぜる"""
    v = lambda: r.choice(["1", "2", "7", "-3", "(3 < 2)", "(4 + 5)", "a", "b", "`xy`", "\\\\q", "__"])
    nf = r.randint(1, 4); names = r.sample(["a", "b", "c", "d"], nf)
    lines = []
    for i, nm in enumerate(names):
        vv = r.choice([x for x in ["1", "2", "7", "-3", "(3 < 2)", "(4 + 5)", "`xy`", "\\\\q"] + [m for m in names[:i]] + [m + " + 1" for m in names[:i]]])
        lines.append(f"\t{nm} : {vv}")
    head = "p :\n" + "\n".join(lines) + "\nk : 2\nq : 1\n"
    if r.random() < .25: head += "w :\n\tz : 5\n\tp : " + r.choice(["1", "`s`"]) + "\n"; names2 = names
    key = r.choice(names + ["e", "0", "1", "2", "3", "-1", "-4", "9", "k", "__", "`a`", "`e`", "(1 + 1)", "(2 - 5)", "(3 < 2)"])
    pick = r.random()
    if pick < .2: body = "p"
    elif pick < .55: body = f"p ' {key}"
    elif pick < .65: body = f"||p||"
    elif pick < .72: body = f"(p ' {key}) + 1"
    elif pick < .8: body = f"p + 1"
    elif pick < .86: return head + f"f : s ? s ' {r.choice(names + ['e'])}\nf p\n"
    elif pick < .9: return head + f"f : s x ? (s ' {r.choice(names)}) + x\nf p {r.choice(['1', '(3 < 2)'])}\n"
    elif pick < .95: return "Pt : x y ? [\n\tl : x\n\tm : y\n\tn : x + y\n]\n(Pt " + f"{r.choice(['1','2'])} {r.choice(['3','(3 < 2)'])}) ' {r.choice(['l','m','n','o','0','-1'])}\n"
    else: body = r.choice(["w ' z", "(w ' p)", "||w||", "w"])
    return head + body + "\n"
def floats_program(r):
    """S4: Float の字面・整数との混ぜ算・比べ・符号・関数。`%`・0 割り・溢れ・添字・長さは SIR が断る(仕様が未決)"""
    fl = lambda: r.choice(["1.5", "2.0", "0.5", "-0.5", "3.25", "0.1", "0.0", "100.0", "-2.0"])
    iv = lambda: r.choice(["1", "2", "7", "-3", "0", "9", "(3 < 2)", "__"])
    a = lambda: r.choice([fl(), fl(), iv(), "x"]) if False else r.choice([fl(), iv()])
    pick = r.random()
    if pick < .35: body = f"{a()} {r.choice(['+','-','*','/','/','%'])} {a()}"
    elif pick < .5: body = f"({a()} {r.choice(['<','>','<=','>=','=','!='])} {a()})"
    elif pick < .58: body = f"{a()} {r.choice(['<','>','<='])} {a()} {r.choice(['<','>','<='])} {a()}"
    elif pick < .66: body = r.choice([f"|{fl()}|", f"-({fl()})", f"|{iv()} - {fl()}|"])
    elif pick < .74: body = f"({a()} | {a()})"
    elif pick < .75: body = f"({a()} & {a()})"
    elif pick < .88: return f"f : x ? x {r.choice(['+','*','-','/'])} {a()}\nf {a()}\n"
    elif pick < .94: return f"f : x y ? x {r.choice(['+','*','<','-'])} y\nf {a()} {a()}\n"
    elif pick < .97: body = r.choice([f"[3 4 5] ' {fl()}", f"`abc` ' {fl()}", f"[3 4 5] ' ({a()} + {fl()})", f"[3 4 5] ' ({fl()} - {fl()})", f"[3 4 5] ' ({fl()} * 2)"])
    else: body = r.choice([f"||{fl()}||", f"||{iv()}||", f"||{a()} + {a()}||", f"(||{iv()}|| + 1)", f"||{a()} * 2|| - 3"])
    return body + "\n"
def program(r):
    if FLOATS[0]: return floats_program(r)
    if STRUCTS[0]: return structs_program(r)
    if STRINGS[0]: return strings_program(r)
    if PARTIAL[0]: return partial_program(r)
    if DEF_RATE[0] and r.random() < DEF_RATE[0]: return defaults_program(r)
    if FLOW_RATE[0] and r.random() < FLOW_RATE[0]: return flow_program(r)
    if r.random() < LIST_RATE[0]: return list_program(r)
    out, fs = [], []
    for i in range(r.randint(0, 2)):
        k = r.randint(1, 2); ps = ["x", "y"][:k]
        body = expr(r, ps, 3)
        if r.random() < .3: body = f"{expr(r, ps, 2)} ? {expr(r, ps, 2)} : {expr(r, ps, 2)}"
        if " ? " in body:
            c, v, e = body.split(" ? ")[0], None, None
            c, rest = body.split(" ? ", 1); v, e = rest.split(" : ", 1)
            out.append(f"f{i} : {' '.join(ps)} ?\n\t{c} : {v}\n\t{e}")
        else: out.append(f"f{i} : {' '.join(ps)} ? {body}")
        fs.append((f"f{i}", k))
    t = expr(r, [], 3)
    if r.random() < .15: out.insert(0, "v0 : " + num(r)); t = expr(r, ["v0"], 2)
    if fs and r.random() < .12: t = r.choice([num(r), "v0" if out and out[0].startswith("v0") else num(r)]) + " " + r.choice(fs)[0]
    elif fs and r.random() < .7:
        n, k = r.choice(fs); t = f"{n} " + " ".join(f"({expr(r, [], 2)})" for _ in range(k))
    return "\n".join(out + [t]) + "\n"
def obs_strict(t):
    S.STRICT_GATES = True
    try:
        S.MEMORY.clear(); S.WARNINGS.clear(); old = sys.stdout; sys.stdout = io.StringIO()
        try: r = S.run(t)
        finally: sys.stdout = old
        v = S.show(r[-1]) if r else "!_"
    except BaseException as e: return ("refuse", type(e).__name__)
    finally: S.STRICT_GATES = False
    if v.startswith("[") and v.endswith("]") and ": " in v: return ("rec", v)
    if ("." in v or "e" in v) and v.lstrip("-")[:1].isdigit():
        try: float(v); return ("flt", v)
        except ValueError: pass
    if v.startswith("[") and v.endswith("]"):
        try: return ("flow", tuple(int(x) for x in v[1:-1].split(",")))
        except ValueError: pass
    if len(v) >= 3 and v[0] == v[-1] == "`" and v[1:-1].isascii(): return ("str", v[1:-1])
    if len(v) == 2 and v[0] == "\\" and v[1].isalnum() and v[1].isascii(): return ("chr", ord(v[1]))
    return ("void",) if v == "!_" else (("val", int(v)) if v.lstrip("-").isdigit() else ("other", v[:20]))
def obs_sir(t):
    try:
        f, top = R.lower(S.parse_source(t))
        if top is None: return ("unsup", "なし")
        return R.evaluate(f, top)
    except R.Unsup as e: return ("unsup", str(e))
    except BaseException as e: return ("crash", type(e).__name__ + str(e)[:40])
_ns = {}
def _got(got):
    if got[0] == "trap": return ("trap",)
    if got[0] == "ok": return ("void",) if got[1] == "__" else ("val", got[1])
    if got[0] == "exit":                                                       # linux: 出力の文字
        v = got[1].strip()
        if v == "__": return ("void",)
        if v.lstrip("-").isdigit(): return ("val", int(v))
        if len(v) >= 3 and v[0] == v[-1] == "`": return ("str", v[1:-1])
        if len(v) == 2 and v[0] == "\\" and v[1].isalnum(): return ("chr", ord(v[1]))
        if v.startswith("[") and v.endswith("]"):
            try: return ("flow", tuple(int(x) for x in v[1:-1].split(",")))
            except ValueError: pass
    return ("refuse", str(got)[:30])

def obs_asm(t, linux=False):
    """機械語(strict_rewrite + generate + エミュレータ)の観測。断り・罠は答えを出さない観測。"""
    import sign_asm
    if not _ns:
        here = os.path.dirname(os.path.abspath(__file__))
        src = open(os.path.join(here, "test_asm.py"), encoding="utf-8").read()
        _ns.update({"__file__": os.path.join(here, "test_asm.py"), "__name__": "emu"})
        exec(compile(src[:src.index("# ---------------- 処理系の答え")], "emu", "exec"), _ns)
        sign_asm.STRICT[0] = True
    try:
        tree, rest = sign_asm.strict_rewrite(S.parse_source(t))
        if rest: return ("refuse", "strict_rewrite")
        got = _ns["run_asm"](sign_asm.generate(tree, "linux"), linux=True) if linux else _ns["run_asm"](sign_asm.generate(tree))
    except (sign_asm.AsmError, sign_asm.StrictRefusal) as e: return ("refuse", str(e)[:30])
    except Exception as e: return ("refuse", "例外 " + type(e).__name__)
    return _got(got)

def obs_asm_sir(t, linux=False):
    """SIR を旧 AST に戻し、strict_rewrite を通さずに generate へ。戻せない形は ("unsup",)。"""
    import sign_asm
    obs_asm("0\n")                                                     # エミュレータの準備
    try:
        f, top = R.lower(S.parse_source(t))
        nodes = R.raise_ast(f, top)
    except R.Unsup as e: return ("unsup", str(e)[:30])
    try: got = _ns["run_asm"](sign_asm.generate(nodes, "linux"), linux=True) if linux else _ns["run_asm"](sign_asm.generate(nodes))
    except (sign_asm.AsmError, sign_asm.StrictRefusal) as e: return ("refuse", str(e)[:30])
    except Exception as e: return ("refuse", "例外 " + type(e).__name__)
    return _got(got)

def main():
    av = [x for x in sys.argv[1:] if not x.startswith('--')]
    n = int(av[0]) if av else 2000; r = random.Random(int(av[1]) if len(av) > 1 else 1)
    FLOW_RATE[0] = 1.0 if '--flows' in sys.argv else 0.0
    NOVOID[0] = '--novoid' in sys.argv
    LIST_RATE[0] = 0.5 if '--lists' in sys.argv else 0.0
    DEF_RATE[0] = 1.0 if '--defaults' in sys.argv else 0.0
    NAMES[0] = '--names' in sys.argv
    PARTIAL[0] = '--partial' in sys.argv
    STRINGS[0] = '--strings' in sys.argv
    STRUCTS[0] = '--structs' in sys.argv
    FLOATS[0] = '--floats' in sys.argv
    tally, bad = {}, []
    for _ in range(n):
        t = fix(program(r)); b = obs_sir(t)
        if b[0] == "unsup": tally["未対応"] = tally.get("未対応", 0) + 1; continue
        if b[0] == "crash": bad.append((t, "SIR が落ちた", b)); continue
        a = obs_strict(t)
        if a[0] in ("refuse", "other") or b == ("partial",) or b == ("fuel",): k = "比べない: " + ("評価器が断る" if a[0]=="refuse" else "評価器の値が整数でない" if a[0]=="other" else "部分適用" if b==("partial",) else "燃料"); tally[k] = tally.get(k, 0) + 1; continue
        if a == b: tally["一致"] = tally.get("一致", 0) + 1
        else: bad.append((t, a, b))
        lx = FLOW_RATE[0] > 0 or b[0] == "flow" or PARTIAL[0]      # 余りの実引数がある呼びは、実行時に単位かどうかで値か流れかが変わる。非 linux の観測は流れを読めないので、linux で見る
        if "--asm" in sys.argv:
            lx = lx or "`" in t or "\\" in t                                       # 文字列・文字は実機の印字で見る
            c = obs_asm(t, lx)
            k = "後段 一致" if c == b else ("後段 断り" if c[0] == "refuse" else "後段 罠" if c[0] == "trap" else "後段 誤答")
            tally[k] = tally.get(k, 0) + 1
            if k == "後段 誤答": bad.append((t, "機械語 " + str(c), b))
            d = obs_asm_sir(t, lx)
            k2 = "SIR経由 戻せない" if d[0] == "unsup" else "SIR経由 一致" if d == b else ("SIR経由 断り" if d[0] == "refuse" else "SIR経由 罠" if d[0] == "trap" else "SIR経由 誤答")
            tally[k2] = tally.get(k2, 0) + 1
            if k2 == "SIR経由 誤答": bad.append((t, "SIR経由の機械語 " + str(d), b))
    print("乱数照合:", tally, "食い違い", len(bad))
    for t, a, b in bad[:8]: print("---\n" + t + f"評価器 {a} / SIR {b}")
    return 1 if bad else 0
if __name__ == "__main__": sys.exit(main())
