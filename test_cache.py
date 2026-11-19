#!/usr/bin/env python3
"""構文木のキャッシュ(sign_interp.parse_source)の試験: 手元の .sn すべてで、キャッシュから読んだ木が、解析し直した木と型まで同じ。
キャッシュを切る・壊れたキャッシュ・別の置き場・--strict で今までどおり動くこと。python test_cache.py"""
import os, subprocess, sys, tempfile, glob, shutil
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
bad = 0
def check(name, got, want):
    global bad
    ok = got == want; bad += not ok
    print(("ok  " if ok else "NG  ") + name + ("" if ok else f"\n    得た: {got!r}\n    期待: {want!r}"))
CD = tempfile.mkdtemp(); os.environ["SIGN_CACHE_DIR"] = CD
import sign_interp as S
def deep(a, b):
    if type(a) is not type(b): return False
    if isinstance(a, (tuple, list)): return len(a) == len(b) and all(deep(x, y) for x, y in zip(a, b))
    if isinstance(a, dict): return a.keys() == b.keys() and all(deep(a[k], b[k]) for k in a)
    return a == b
files = sorted(glob.glob(os.path.join(HERE, "*.sn")))
n_cached = 0
S._CACHE_MIN_SECONDS = 0.0          # 『重い』の境目(解析 15 ms)に時間の揺れで当たらないよう、この繰り返しの間は全部置く
for f in files:
    src = open(f, encoding="utf-8").read()
    S.CACHE_ON[0] = False; fresh = S.parse_source(src)
    S.CACHE_ON[0] = True
    before = len(os.listdir(CD)); first = S.parse_source(src); second = S.parse_source(src)
    n_cached += len(os.listdir(CD)) > before
    check(f"{os.path.basename(f)}: 1 回目・2 回目とも同じ木", deep(fresh, first) and deep(fresh, second), True)
check("重い .sn はキャッシュに置かれた", n_cached >= 3, True)
S._CACHE_MIN_SECONDS = 0.015
# 壊れたキャッシュは黙って捨てて解析し直す
big = open(os.path.join(HERE, "suika.sn"), encoding="utf-8").read()
S.parse_source(big)
for p in glob.glob(os.path.join(CD, "*.pkl")): open(p, "wb").write(b"not a pickle")
S.CACHE_ON[0] = False; fresh = S.parse_source(big); S.CACHE_ON[0] = True
check("壊れたキャッシュから回復する", deep(S.parse_source(big), fresh), True)
check("別の原文は別の鍵(書き換えた Suika は書き換えが反映される)", deep(S.parse_source(big + "\nzz : 12345\n"), fresh), False)
# 実行: キャッシュあり・なし・--strict で出力が同じ
def run(args, env_extra):
    env = dict(os.environ); env.update(env_extra)
    r = subprocess.run([sys.executable, os.path.join(HERE, "sign_interp.py"), *args], capture_output=True, text=True, timeout=120, env=env, cwd=HERE, stdin=subprocess.DEVNULL)
    return r.returncode, r.stdout, r.stderr
for prog in ("fib_bench.sn", "std_demo.sn"):
    a = run([prog], {"SIGN_CACHE_DIR": CD}); b = run([prog], {"SIGN_CACHE_DIR": CD}); c = run([prog], {"SIGN_NO_CACHE": "1"})
    check(f"{prog}: キャッシュ 1 回目・2 回目・なしで同じ", a == b == c, True)
a = run(["--strict", "fib_bench.sn"], {"SIGN_CACHE_DIR": CD}); b = run(["--strict", "fib_bench.sn"], {"SIGN_NO_CACHE": "1"})
check("--strict は今までどおり(キャッシュを使わない)", a == b, True)
# 構文エラーはキャッシュされず、行・桁つきで出る
open(os.path.join(CD, "bad.sn"), "w").write("f : x ?\n" + "\tx + 1\n" * 3 + "( 1 2\n" + "# padding\n" * 60)
a = run([os.path.join(CD, "bad.sn")], {"SIGN_CACHE_DIR": CD}); b = run([os.path.join(CD, "bad.sn")], {"SIGN_CACHE_DIR": CD})
check("構文エラーは毎回同じ", a == b and a[0] == 1, True)
# sign.py(翻訳済みの本体を読むだけの起動口)は sign_interp.py と同じ出力
for args in (["fib_bench.sn"], ["std_demo.sn"], ["sprite_demo.sn", "--display=ascii", "--timer=virtual", "--input=1:close"], ["--strict", "fib_bench.sn"], ["no_such_file.sn"]):
    a = run(args, {"SIGN_NO_CACHE": "1"})
    r = subprocess.run([sys.executable, os.path.join(HERE, "sign.py"), *args], capture_output=True, text=True, timeout=120, env=dict(os.environ, SIGN_NO_CACHE="1"), cwd=HERE, stdin=subprocess.DEVNULL)
    check(f"sign.py {' '.join(args)}: sign_interp.py と同じ", (r.returncode, r.stdout, r.stderr) == a, True)
# 別の起動口(sign.py)が作ったキャッシュを sign_interp.py が読んでも、文字(Char)の型が食い違わない(逆も)
import tempfile as _tf
CD2 = _tf.mkdtemp(); db = _tf.mkdtemp()
def runp(prog, script, extra, cache):
    env = dict(os.environ); env.pop("SIGN_NO_CACHE", None); env["SIGN_CACHE_DIR"] = cache
    r = subprocess.run([sys.executable, os.path.join(HERE, script), os.path.join(HERE, prog), *extra], capture_output=True, text=True, timeout=120, env=env, cwd=HERE, stdin=subprocess.DEVNULL)
    return r.returncode, r.stdout, r.stderr
ref = runp("sqlite_demo.sn", "sign_interp.py", ["--db=" + db], os.path.join(CD2, "none"))
a = runp("sqlite_demo.sn", "sign.py", ["--db=" + db], CD2); b = runp("sqlite_demo.sn", "sign_interp.py", ["--db=" + db], CD2); c = runp("sqlite_demo.sn", "sign.py", ["--db=" + db], CD2)
check("sign.py が作ったキャッシュを sign_interp.py が読む(Char の型)", a == b == c == ref, True)
shutil.rmtree(CD2, ignore_errors=True); shutil.rmtree(db, ignore_errors=True)
shutil.rmtree(CD, ignore_errors=True)
print("\n全部 ok" if not bad else f"\n{bad} 件 NG"); sys.exit(1 if bad else 0)
