#!/usr/bin/env python3
"""--sexp(構文木の S 式)の試験。設計者の例(Discussions #40)と同じ形・結合の向き・全見本が落ちずに釣り合う形で出ること。"""
import glob, os, re, subprocess, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sign_sexp as Q
ng = 0
def eq(src, want):
    global ng
    got = Q.to_sexp(src + "\n")
    if got != want: ng += 1; print("NG", repr(src), "\n   得", got, "\n   期", want)
eq("f : x y ? x + y", "(setq f (lambda (x y) (+ x y)))")                      # 設計者の投稿の例
eq("unit : none : []", "(setq unit (setq none (list)))")                        # 確認された入れ子(右結合)
eq("a - b - c", "(- (- a b) c)")                                                 # 左結合
eq("a ^ b ^ c", "(expt a (expt b c))")                                           # 右結合
eq("a # b # c", "(output a (output b c))")                                       # 右結合(仕様)
eq("a , b , c", "(product a b c)")
eq("x : 10", "(setq x 10)")                                                      # 被演算子は書いた順(入れ替えない)
eq("a < b < c", "(< a b c)")
eq("[+] 1 2 3", "(coproduct (fold +) 1 2 3)")
eq("f : n ?\n\tn = 0 : 1\n\tn * (f (n - 1))", "(setq f (lambda (n) (cond ((= n 0) 1) (t (* n (block (coproduct f (block (- n 1)))))))))")
def bal(t):
    t = re.sub(r'"(\\.|[^"\\])*"', "", t); t = re.sub(r"\|(\\.|[^|\\])*\|", "", t)
    return t.count("(") == t.count(")")
here = os.path.dirname(os.path.abspath(__file__))
files = sorted(glob.glob(os.path.join(here, "*.sn")))
for f in files:
    try: out = Q.to_sexp(open(f, encoding="utf-8").read())
    except Exception as e: ng += 1; print("NG 落ちた", f, e); continue
    if not bal(out): ng += 1; print("NG 括弧が釣り合わない", f)
r = subprocess.run([sys.executable, os.path.join(here, "sign.py"), "--sexp", os.path.join(here, "echo.sn")], capture_output=True, text=True)
if r.returncode != 0 or not r.stdout.startswith("("): ng += 1; print("NG --sexp の起動口", r.stdout[:80], r.stderr[:80])
r = subprocess.run([sys.executable, os.path.join(here, "sign.py"), "--sexp", "/no/such/file.sn"], capture_output=True, text=True)
if r.returncode == 0 or "Traceback" in r.stderr: ng += 1; print("NG 無いファイルで落ちた")
print("全部通った (%d 本の見本)" % len(files) if not ng else "%d 件 NG" % ng)
sys.exit(1 if ng else 0)
