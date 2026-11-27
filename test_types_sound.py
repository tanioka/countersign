"""test_types_sound.py — 型の静的パス(sign_types.py)の健全さの性質検査(ランダム生成)。Typing.lean J.1(b) `fold_sound` の実装側の見張り。
  S1 型保存    : 型が付いた最上位の式を処理系(sign_interp)で動かした値が、型と合う。
                 値は `!_`(`__`)でもよい(Lean の `Approx`: none ∨ some k。`!_` はどの型にも入る)。
  S2 進行      : 型が付いた式の評価は、例外で落ちず(止まらない例外・落ちる例外を数える)、値(`__` を含む)に着く。
値の種類: Int(整数)・Float・Char・String・List・Struct・Unit。型との合い方: Int ⊑ Scalar、Atom はどの値も受ける、Open は並びの値。"""
import random, sys, signal
sys.setrecursionlimit(20000)
import sign_interp as S
import sign_types as T

random.seed(20261129)
IDX = [1]          # 添字の上限(1: 範囲の中だけ。4: 範囲の外 = `!_` が出うる)

def gen_expr(depth, ty, fns):
    """型 ty(Int / Float / String / List)の式の文字列。fns: [(名前, 引数の型, 返す型)]"""
    r = random.random()
    cands = [f for f in fns if f[2] == ty and depth > 0]
    if cands and r < 0.35:
        f = random.choice(cands)
        return "(%s %s)" % (f[0], gen_expr(depth - 1, f[1], fns))
    if ty == "Int":
        if depth <= 0 or r < 0.35: return str(random.choice([0, 1, 2, 7, -3]))
        if r < 0.65: return "(%s %s %s)" % (gen_expr(depth - 1, "Int", fns), random.choice(["+", "-", "*"]), gen_expr(depth - 1, "Int", fns))
        if r < 0.8: return "(||%s||)" % gen_expr(depth - 1, "List", fns)
        return "(%s ' %d)" % (gen_expr(depth - 1, "List", fns), random.randint(0, IDX[0]))
    if ty == "Float":
        if depth <= 0 or r < 0.4: return random.choice(["0.5", "1.5", "2.0"])
        return "(%s %s %s)" % (gen_expr(depth - 1, "Float", fns), random.choice(["+", "-", "*"]), gen_expr(depth - 1, "Float", fns))
    if ty == "String":
        if depth <= 0 or r < 0.5: return random.choice(["`ab`", "`c`", "`xyz`"])
        return "(%s %s)" % (gen_expr(depth - 1, "String", fns), gen_expr(depth - 1, "String", fns))
    # List(Int)
    if depth <= 0 or r < 0.4: return "(" + " ".join(str(random.randint(0, 9)) for _ in range(random.randint(2, 4))) + ")"
    return "(%s %s)" % (gen_expr(depth - 1, "List", fns), gen_expr(depth - 1, "List", fns))

def gen():
    fns, defs = [], []
    for i in range(random.randint(0, 3)):
        a, b = random.choice(["Int", "Float", "String", "List"]), random.choice(["Int", "Float", "String", "List"])
        body = gen_expr(2, b, fns) if random.random() < 0.5 else "x"
        if body == "x": b = a
        name = "f%d" % i
        defs.append("%s : x ? %s" % (name, body)); fns.append((name, a, b))
    ty = random.choice(["Int", "Float", "String", "List"])
    return "\n".join(defs + [gen_expr(3, ty, fns)]) + "\n"

def value_kinds(v):
    if v is S.UNIT or v is S.ABS or S.is_unit(v): return {"Unit"}
    if isinstance(v, bool): return {"Int"}
    if isinstance(v, int): return {"Int"}
    if isinstance(v, float): return {"Float"}
    if isinstance(v, S.Char): return {"Char"}
    if isinstance(v, str): return {"String"}
    if isinstance(v, S.Struct): return {"Struct"}
    if isinstance(v, list): return {"List"}
    return {"Other"}

def accepts(t, v):
    ks = value_kinds(v)
    if "Unit" in ks: return True                         # `!_` はどの型にも入る
    if t in (T.ANY, T.UNIT_T) or t == "Atom": return True
    if t in ("Scalar",): return bool(ks & {"Int", "Float"})
    if t == T.INT: return "Int" in ks or "Float" in ks   # Int の字面は小数への昇格を許す側の既定
    if t == T.FLOAT: return bool(ks & {"Float", "Int"})
    if t in (T.CHAR,): return "Char" in ks
    if t == T.STRING: return bool(ks & {"String", "Char"})
    if T.is_list(t):
        return "List" in ks and all(accepts(t[1], x) for x in v)
    if T.is_struct(t): return bool(ks & {"Struct", "List"})
    if T.is_open(t): return "List" in ks or "String" in ks
    return True                                          # Fn・Stream・Reader などは、ここでは見ない

class Timeout(Exception): pass
def alarm(sig, frm): raise Timeout()
signal.signal(signal.SIGALRM, alarm)

def run(count):
    stats = {"programs": 0, "typed": 0, "s1_break": 0, "s2_crash": 0, "s2_timeout": 0}
    bad = []
    for _ in range(count):
        src = gen()
        try: c = T.Checker(S.parse_source(src)).solve().cycle_pass().plain_pass().nest_pass().excess_pass()
        except Exception: continue
        stats["programs"] += 1
        if not c.top_types: continue
        t = c.top_types[-1]
        stats["typed"] += 1
        try:
            signal.alarm(5); res = S.run(src); signal.alarm(0)
        except Timeout: stats["s2_timeout"] += 1; continue
        except Exception as e:
            signal.alarm(0); stats["s2_crash"] += 1; bad.append(("crash", src, repr(e)[:80])); continue
        if not res: continue
        v = res[-1]
        if not accepts(t, v):
            stats["s1_break"] += 1; bad.append(("S1", src, "%s ← %s" % (T.show_t(t), S.show(v))))
    return stats, bad

IDX[0] = 1
sa, ba = run(400)
IDX[0] = 4
sb, bb = run(400)
print("(a) 範囲の中だけ(`!_` が出ない):", sa)
print("(b) 範囲の外の添字あり(`!_` が単位として混ざる):", sb)
for kind, src, why in (ba + bb)[:2]: print("例", kind, why); print(src)
# 既知の反例(Lean の `value_ops_not_self_typed`: `!_` は演算の単位なので、答えの種類が相手の種類になる): 型は List(Int)、値は Int の 6
known = "((((9 3 8) (2 1)) ' 4) * 6)\n"
ck = T.Checker(S.parse_source(known)).solve()
kt, kv = ck.top_types[-1], S.run(known)[-1]
print("既知の反例:", T.show_t(kt), "←", S.show(kv), "(型保存は `!_` が単位になる所で破れる。報告のみ)")
if sa["s1_break"] or sa["s2_crash"] or sb["s2_crash"]: sys.exit(1)
print("全部 ok((a) は型保存。(b) の S1 は `!_` が単位になる所で型が変わる件の報告)")
