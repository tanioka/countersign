"""(--strict は最後の行の値を出さない(V9)ので、strict では知らせの有無だけを見る。)
最後でない枝の中の再帰は末尾でない(value_spec V9・V10)。--strict では深さを数え、上限で resource-depth を出す。
最後の行(既定の行)で呼ぶ形は末尾で、同じ段数でも知らせが出ない。"""
import subprocess, sys, tempfile, os
HERE = os.path.dirname(os.path.abspath(__file__))
def run(src, *opts):
    with tempfile.TemporaryDirectory() as d:
        open(os.path.join(d, "a.sn"), "w").write(src)
        r = subprocess.run([sys.executable, os.path.join(HERE, "sign.py"), *opts, os.path.join(d, "a.sn")], capture_output=True, text=True, cwd=HERE)
        return r.stdout + r.stderr
BRANCH = "`std.sn`@~\nlp : n acc ?\n\tn > 0 : lp (n - 1) (acc + n)\n\tacc\n\nprintln_int (lp %d 0)\n"
TAIL = "`std.sn`@~\nlp : n acc ?\n\tn = 0 : acc\n\tlp (n - 1) (acc + n)\n\nprintln_int (lp %d 0)\n"
bad = 0
def check(name, cond):
    global bad
    print(("ok  " if cond else "NG  ") + name); bad += (not cond)
o = run(BRANCH % 100000, "--strict"); check("最後でない枝の再帰 100000 段(strict)は resource-depth", "resource-depth" in o)
o = run(BRANCH % 1000, "--strict"); check("同 1000 段は resource-depth なし", "resource-depth" not in o and "エラー" not in o)
o = run(TAIL % 100000, "--strict"); check("既定の行で呼ぶ形は 100000 段でも深さを使わない", "resource-depth" not in o and "エラー" not in o)
o = run(TAIL % 100000); check("既定のモード: 末尾の形は 100000 段で答える", "5000050000" in o)
o = run(BRANCH % 10000); check("既定のモードは従来どおり(10000 段で答える)", "50005000" in o)
print("全部通った" if not bad else f"{bad} 件失敗"); sys.exit(1 if bad else 0)
