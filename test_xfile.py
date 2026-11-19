"""枚を跨ぐ同じ名前(compiler_pipeline.md §4・coproduct_spec P2): --strict は name-duplicate で断る。公開(`#`)でない名前は引く側に入らないので、ぶつからない。"""
import os, subprocess, sys, tempfile
HERE = os.path.dirname(os.path.abspath(__file__))
FILES = {"lib.sn": "#k : x ? w x\nw : x ? x + 1\n", "pub.sn": "#w : x ? x + 1\n", "pub2.sn": "#w : x ? x + 100\n"}
CASES = [   # (名前, 本文, strict で断るか)
    ("公開の k だけを引く", "`lib.sn`@~\nk 5\n", False),
    ("lib の private な w と自分の w は別", "`lib.sn`@~\nw : x ? x * 10\nk 5\n", False),
    ("private な w は引く側から見えない(未定義の名前)", "`lib.sn`@~\nw 5\n", False),
    ("公開の w が 2 枚", "`pub.sn`@~\n`pub2.sn`@~\nw 1\n", True),
    ("公開の w と自分の w(自分が後)", "`pub.sn`@~\nw : x ? x * 10\nw 5\n", True),
    ("自分の w(先)と公開の w", "w : x ? x * 10\n`pub.sn`@~\nw 5\n", True),
    ("同じ枚を 2 回引く", "`pub.sn`@~\n`pub.sn`@~\nw 5\n", True),   # 同じ公開が2回: 名前が重なる(撒く取り込みの重なり)
]
bad = 0
d = tempfile.mkdtemp()
for n, t in FILES.items(): open(os.path.join(d, n), "w", encoding="utf-8").write(t)
for name, body, refuse in CASES:
    f = os.path.join(d, "m.sn"); open(f, "w", encoding="utf-8").write(body)
    r = subprocess.run([sys.executable, os.path.join(HERE, "sign.py"), "--strict", f], capture_output=True, text=True, cwd=d)
    got = "name-duplicate" in r.stderr + r.stdout
    if got != refuse: bad += 1; print("NG", name, "断りが出た" if got else "断りが出ない", "のはず:", "断る" if refuse else "通る", r.stderr[:120])
print("全部 ok" if not bad else "NG %d 件" % bad); sys.exit(1 if bad else 0)
