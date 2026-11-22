"""乱数で整数の式・関数を作り、strict の評価器と SIR の評価を照合する(前段)。
使い方: python3 fuzz_sir.py [件数=2000] [種=1]     終了コード: 食い違いがあれば 1"""
import sys, os, io, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__))); sys.setrecursionlimit(20000)
import sign_interp as S, sign_sir as R
from fixblank import fix

LIST_RATE = [0.0]
def num(r):
    return str(r.choice([0, 1, 2, 3, 5, 7, 10, 100, 9223372036854775807]))
def atom(r, ps):
    c = r.random()
    if ps and c < .4: return r.choice(ps)
    if c < .5: return "__"
    return num(r)
def expr(r, ps, d):
    if d <= 0 or r.random() < .25: return atom(r, ps)
    c = r.random(); a = expr(r, ps, d-1); b = expr(r, ps, d-1)
    if c < .55: return f"({a} {r.choice('+-*/%')} {b})"
    if c < .75: return f"({a} {r.choice(['<','>','<=','>=','==','!=','='])} {b})"
    if c < .83: return f"({a} {r.choice('&|')} {b})"
    if c < .88: return f"(0 - {a})"
    if c < .94:
        o = r.choice(["<", "<="]); return f"({a} {o} {b} {o} {expr(r, ps, d-1)})"
    if c < .97:
        op = r.choice(["<", ">", "<=", ">=", "==", "="])
        xs = [atom(r, ps) if r.random() < .7 else "(" + expr(r, ps, d-1) + ")" for _ in range(r.randint(1, 4))]
        return f"([{op}] {' '.join(xs)})"
    return f"({a} = {b} = {expr(r, ps, d-1)})"
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
    return "\n".join(f"{n} : {lst(r)}" for n in names) + "\n" + lexpr(r, names, 3) + "\n"
def program(r):
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
    return ("void",) if v == "!_" else (("val", int(v)) if v.lstrip("-").isdigit() else ("other", v[:20]))
def obs_sir(t):
    try:
        f, top = R.lower(S.parse_source(t))
        if top is None: return ("unsup", "なし")
        return R.evaluate(f, top)
    except R.Unsup as e: return ("unsup", str(e))
    except BaseException as e: return ("crash", type(e).__name__ + str(e)[:40])
_ns = {}
def obs_asm(t):
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
        got = _ns["run_asm"](sign_asm.generate(tree))
    except sign_asm.AsmError as e: return ("refuse", str(e)[:30])
    except Exception as e: return ("refuse", "例外 " + type(e).__name__)
    if got[0] == "trap": return ("trap",)
    if got[0] != "ok": return ("refuse", str(got)[:30])
    return ("void",) if got[1] == "__" else ("val", got[1])

def main():
    av = [x for x in sys.argv[1:] if not x.startswith('--')]
    n = int(av[0]) if av else 2000; r = random.Random(int(av[1]) if len(av) > 1 else 1)
    LIST_RATE[0] = 0.5 if '--lists' in sys.argv else 0.0
    tally, bad = {}, []
    for _ in range(n):
        t = fix(program(r)); b = obs_sir(t)
        if b[0] == "unsup": tally["未対応"] = tally.get("未対応", 0) + 1; continue
        if b[0] == "crash": bad.append((t, "SIR が落ちた", b)); continue
        a = obs_strict(t)
        if a[0] in ("refuse", "other") or b == ("partial",) or b == ("fuel",): k = "比べない: " + ("評価器が断る" if a[0]=="refuse" else "評価器の値が整数でない" if a[0]=="other" else "部分適用" if b==("partial",) else "燃料"); tally[k] = tally.get(k, 0) + 1; continue
        if a == b: tally["一致"] = tally.get("一致", 0) + 1
        else: bad.append((t, a, b))
        if "--asm" in sys.argv:
            c = obs_asm(t)
            k = "後段 一致" if c == b else ("後段 断り" if c[0] == "refuse" else "後段 罠" if c[0] == "trap" else "後段 誤答")
            tally[k] = tally.get(k, 0) + 1
            if k == "後段 誤答": bad.append((t, "機械語 " + str(c), b))
    print("乱数照合:", tally, "食い違い", len(bad))
    for t, a, b in bad[:8]: print("---\n" + t + f"評価器 {a} / SIR {b}")
    return 1 if bad else 0
if __name__ == "__main__": sys.exit(main())
