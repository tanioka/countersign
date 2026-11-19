"""test_asm_dev.py — 実プログラムを、処理系と asm 版(エミュレータ+同じ仮想装置)で走らせて、標準出力と描画装置の PNG を突き合わせる。
装置はソフトの模擬(emu_dev.py)で、実機の代わりではない。実機では未実行。"""
import os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import emu_dev, sign_asm, sign_interp, random, tempfile
os.environ.setdefault("EMU_LIMIT", "2000000000")      # suika_flat は命令数が多い

fails = 0
def check(name, want, got):
    global fails
    if want == got: print("ok ", name)
    else: fails += 1; print("NG ", name, "\n    want", repr(want)[:200], "\n    got ", repr(got)[:200])

CASES = [
    ("echo.sn", [], b"hello\n"),
    ("i2c_scan.sn", ["i2c=fake:0x48,0x50"], b""), ("i2c_scan.sn", ["i2c=fake"], b""),
    ("spi_loopback.sn", ["spi=fake"], b""),
    ("aht25_demo.sn", ["i2c=aht25:23.5,61", "timer"], b""),
    ("sys_demo.sn", ["sys", "timer"], b""),
    ("sqlite_demo.sn", ["db"], b""),
    ("animate.sn", ["timer"], b""),
    ("keys.sn", ["timer", "input=0:kd:29,50:kd:29,120:kd:28,200:kd:113"], b""), ("keys.sn", ["timer", "input=10:close"], b""),
    ("draw_gfx.sn", ["display=png:o.png:64x32"], b""),
    ("turtle_square.sn", ["display=png:sq.png:300x300", "timer"], b""),
    ("turtle_sierpinski.sn", ["display=png:sp.png:300x300", "timer"], b""),
    ("font_demo.sn", ["display=png:f.png:128x64", "timer"], b""),
    ("sound_demo.sn", ["sound"], b""),
]
def suika_script(seed, drops):
    """乱数で作ったキー台本(左右に動かして落とす)。seed が同じなら同じ台本。"""
    rnd = random.Random(seed); ev = []; t = 200
    for _ in range(drops):
        for _ in range(rnd.randint(0, 12)): ev.append("%d:kd:%d" % (t, rnd.choice([28, 29]))); t += 16
        ev.append("%d:kd:32" % t); t += 40; ev.append("%d:ku:32" % t); t += rnd.randint(300, 900)
    ev.append("%d:close" % (t + 800))
    return ["display=png:s_{n}.png:80x104", "timer", "input=" + ",".join(ev)]
_CSV = "alice,30,82\nbob,x,75\ncarol,,90\ndave,41\neve,28,9z\nfrank,35,100\n".encode()
CASES += [("std_demo.sn", ["charset=utf32"], "5\n3\n8\nabc\n 10 \n-2\n".encode()), ("std_demo.sn", ["charset=utf32"], b""),
          ("robust_csv.sn", ["charset=utf32"], b""), ("robust_csv_stdin.sn", ["charset=utf32"], _CSV), ("robust_csv_stdin.sn", ["charset=utf32"], _CSV[:25])]
CASES += [("suika_flat.sn", suika_script(1, 4), b""), ("suika_flat.sn", suika_script(2, 10), b"")]
for prog, specs, stdin in CASES:
    try:
        want, got = emu_dev.compare(prog, specs, stdin)
    except sign_asm.AsmError as e:
        check("%s %s" % (prog, specs), "compiled", "refused: %s" % e); continue
    check("%s %s: 標準出力と PNG が処理系と一致" % (prog, " ".join(specs)[:70]), want, got)
    if prog == "suika_flat.sn": check("  比べた画面の枚数が 20 枚以上(毎こま)", want.count(".png:") >= 20, True)

# suika_flat.sn は suika.sn(果物の並びを番地 1 つに置く作り)を要素ごとの番地へ展開した版。処理系で同じ出力・同じ画面になること
for _seed, _n in [(1, 4), (2, 10), (3, 14)]:
    _sp = suika_script(_seed, _n); _r = []
    for _p in ("suika.sn", "suika_flat.sn"):
        _d = tempfile.mkdtemp(); _o = emu_dev.run_interp(os.path.join(HERE, _p), _sp, b"", _d); _r.append((_o, emu_dev.png_digest(_d)))
    check("suika.sn と suika_flat.sn が処理系で同じ出力・同じ全こまの画面(台本 %d, %d 回落とす)" % (_seed, _n), _r[0], _r[1])

print("\n全部 ok" if not fails else "\n失敗 %d 件" % fails)
sys.exit(1 if fails else 0)
