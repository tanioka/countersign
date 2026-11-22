"""文字列・リストの表(test_asm.py の STR_CASES)を SIR に下げ、下げられない理由を数える(第二段階の作業リスト)。
使い方: python3 diff_str.py [-v]"""
import sys, os, ast, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__))); sys.setrecursionlimit(20000)
import sign_interp as S, sign_sir as R
from fixblank import fix

def str_cases():
    src = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "test_asm.py"), encoding="utf-8").read()
    out = []
    for n in ast.parse(src).body:
        if isinstance(n, (ast.Assign, ast.AugAssign)):
            tg = n.targets[0] if isinstance(n, ast.Assign) else n.target
            if isinstance(tg, ast.Name) and tg.id == "STR_CASES":
                try: out += ast.literal_eval(n.value)
                except Exception: pass
    return out

def main():
    cs = str_cases(); c = collections.Counter(); ex = {}
    for name, t in cs:
        try:
            f, top = R.lower(S.parse_source(fix(t)))
            if top is None: c["式なし"] += 1; continue
            c["下げられた"] += 1
        except R.Unsup as e:
            k = str(e)[:34]; c[k] += 1; ex.setdefault(k, t)
        except BaseException as e: c["落ちた " + type(e).__name__] += 1
    print("STR_CASES", len(cs), "件")
    for k, n in c.most_common(25):
        print(f"{n:4}  {k}" + (f"    例 {ex[k][:60]!r}" if "-v" in sys.argv and k in ex else ""))
main()
