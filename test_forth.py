#!/usr/bin/env python3
"""--forth(構文木の後置)の試験。設計者の例(Discussions #40)・結合の向き・全見本が落ちずに出ること。"""
import glob, os, subprocess, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sign_forth as F
ng = 0
def eq(src, want):
    global ng
    got = F.to_forth(src + "\n")
    if got != want: ng += 1; print("NG", repr(src), "\n   得", got, "\n   期", want)
eq("f : x y ? x + y", "f [ x y ] [ x y + ] ? :")          # 設計者の後置の例 `f [x y] [x y +] ? :`
eq("unit : none : []", "unit none [ ] : :")               # 右結合
eq("a - b - c", "a b - c -")                              # 左結合
eq("a ^ b ^ c", "a b c ^ ^")                              # 右結合
eq("a # b # c", "a b c # #")                              # 右結合(仕様)
eq("a , b , c", "a b c , ,")
eq("x : 10", "x 10 :")
eq("-x + !y", "x neg y not +")
eq("a < b < c", "a b c < < chain")
here = os.path.dirname(os.path.abspath(__file__))
files = sorted(glob.glob(os.path.join(here, "*.sn")))
for f in files:
    try: out = F.to_forth(open(f, encoding="utf-8").read())
    except Exception as e: ng += 1; print("NG 落ちた", f, e); continue
    if not out.strip(): ng += 1; print("NG 空", f)
r = subprocess.run([sys.executable, os.path.join(here, "sign.py"), "--forth", os.path.join(here, "echo.sn")], capture_output=True, text=True)
if r.returncode != 0 or not r.stdout.strip(): ng += 1; print("NG --forth の起動口", r.stderr[:80])
r = subprocess.run([sys.executable, os.path.join(here, "sign.py"), "--forth", "/no/such/file.sn"], capture_output=True, text=True)
if r.returncode == 0 or "Traceback" in r.stderr: ng += 1; print("NG 無いファイルで落ちた")
print("全部通った (%d 本の見本)" % len(files) if not ng else "%d 件 NG" % ng)
sys.exit(1 if ng else 0)
