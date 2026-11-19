"""test_scratch.py — sign_scratch.html(Scratch 風のブロック)の試験。
  1. コード生成(ページの GEN の部分を node で走らせ、できた Sign を本物の処理系・ゲーム機で動かして値を確かめる)
  2. 画面の操作(Playwright と Chromium があれば。ブロックを棚から落とす・穴に入れる・変数をつくる・プレビュー・自動反映)
"""
import io, json, os, re, shutil, subprocess, sys, tempfile, time
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import sign_interp as si, sign_console as sc

bad = 0
def check(name, got, want):
    global bad
    ok = got == want
    if not ok: bad += 1
    print(("ok  " if ok else "NG  ") + name + ("" if ok else f"\n    得た: {got!r}\n    期待: {want!r}"))

NODE = shutil.which("node")
HTML = open(os.path.join(HERE, "sign_scratch.html"), encoding="utf-8").read()
GENJS = re.search(r'<script id="gen">([\s\S]*?)</script>', HTML).group(1)
RUNNER = GENJS + "\nlet s='';process.stdin.on('data',d=>s+=d).on('end',()=>process.stdout.write(GEN.generate(JSON.parse(s))));"

def gen(proj):
    with tempfile.NamedTemporaryFile("w", suffix=".js", delete=False, encoding="utf-8") as f: f.write(RUNNER); n = f.name
    try: return subprocess.run([NODE, n], input=json.dumps(proj), capture_output=True, text=True, timeout=30, check=True).stdout
    finally: os.unlink(n)

N = lambda v: {"t": "n", "v": str(v)}
V = lambda n: {"t": "v", "v": n}
OP = lambda o, a, b: {"t": "op", "o": o, "a": a, "b": b}
CMP = lambda o, a, b: {"t": "cmp", "o": o, "a": a, "b": b}
SET = lambda v, e: {"t": "set", "v": v, "e": e}
def proj(vars_, init=(), tick=(), ):
    return {"vars": list(vars_), "scripts": [{"id": 1, "x": 0, "y": 0, "hat": "init", "body": list(init)}, {"id": 2, "x": 0, "y": 100, "hat": "tick", "body": list(tick)}]}

def play(p, frames=1, script="", read=()):
    """生成して動かし、変数の値(vars の並び順)を返す。"""
    src = gen(p)
    d = tempfile.mkdtemp(); path = os.path.join(d, "g.sn")
    open(path, "w", encoding="utf-8").write(src)
    disp, timer, inp = sc.setup("null:96x96", True, script)
    out = io.StringIO(); con = sc.Console(path, 60, False, out); con.display, con.timer = disp, timer
    for _ in range(frames):
        if not con.frame(): break
        timer.write(4, 16)                                   # 仮想の時計を 1 こま分進める
    vals = [si.MEMORY.get(0x200000 + 4 * i) for i in range(len(p["vars"]))]
    return vals, out.getvalue(), con, src

def main():
    # --- 式 ---
    vals, err, con, src = play(proj(["a", "b", "c", "d", "e", "f", "g", "h"], init=[
        SET("a", OP("*", OP("+", N(7), N(3)), N(2))),            # 20
        SET("b", OP("/", N(7), N(0))),                            # 0 で割ると 0
        SET("c", OP("%", N(17), N(5))),                           # 2
        SET("d", OP("min", N(4), N(-3))),                         # -3
        SET("e", OP("max", N(4), N(-3))),                         # 4
        SET("f", {"t": "abs", "a": N(-9)}),                       # 9
        SET("g", OP("-", N(0), N(5))),                            # -5
        SET("h", OP("%", N(3), N(0))),                            # 0
    ]))
    check("式: 四則・割り算の 0・あまり・大小・絶対値・負の数", vals, [20, 0, 2, -3, 4, 9, -5, 0])
    check("式: 生成が ok(エラーなし)", err, "")
    # --- 条件 ---
    def branch(cond, then=1, els=2):
        return play(proj(["r"], tick=[{"t": "if", "c": cond, "then": [SET("r", N(then))], "else": [SET("r", N(els))]}]))[0][0]
    check("もし: 真", branch(CMP("<", N(1), N(2))), 1)
    check("もし: 偽 → でなければ", branch(CMP(">", N(1), N(2))), 2)
    check("もし: = が等しい", branch(CMP("=", N(3), N(3))), 1)
    check("もし: ≠ が違う", branch(CMP("!=", N(3), N(4))), 1)
    check("もし: ≠ が等しい", branch(CMP("!=", N(3), N(3))), 2)
    check("もし: ≦ ≧", (branch(CMP("<=", N(3), N(3))), branch(CMP(">=", N(2), N(3)))), (1, 2))
    check("もし: かつ", (branch({"t": "and", "a": CMP("<", N(1), N(2)), "b": CMP("<", N(2), N(3))}), branch({"t": "and", "a": CMP("<", N(1), N(2)), "b": CMP(">", N(2), N(3))})), (1, 2))
    check("もし: または", (branch({"t": "or", "a": CMP(">", N(1), N(2)), "b": CMP("<", N(2), N(3))}), branch({"t": "or", "a": CMP(">", N(1), N(2)), "b": CMP(">", N(2), N(3))})), (1, 2))
    check("もし: でない(比較・かつ・または・二重)",
          (branch({"t": "not", "a": CMP("<", N(1), N(2))}), branch({"t": "not", "a": {"t": "and", "a": CMP("<", N(1), N(2)), "b": CMP("<", N(2), N(3))}}),
           branch({"t": "not", "a": {"t": "or", "a": CMP(">", N(1), N(2)), "b": CMP(">", N(2), N(3))}}), branch({"t": "not", "a": {"t": "not", "a": CMP("<", N(1), N(2))}}),
           branch({"t": "not", "a": CMP("=", N(3), N(3))})), (2, 2, 1, 1, 2))
    check("もし: 空の条件は偽", branch(None), 2)
    check("もし: 空の枝", play(proj(["r"], tick=[{"t": "if", "c": CMP("<", N(1), N(2)), "then": [], "else": []}, SET("r", N(7))]))[0], [7])
    # --- 入れ子の もし ---
    inner = {"t": "if", "c": CMP(">", V("r"), N(5)), "then": [SET("r", N(100))], "else": [SET("r", N(-100))]}
    check("入れ子の もし", play(proj(["r"], init=[SET("r", N(9))], tick=[{"t": "if", "c": CMP("<", N(1), N(2)), "then": [inner], "else": []}]))[0], [100])
    # --- くりかえし ---
    check("くりかえし: 0 から n 未満", play(proj(["i", "s"], init=[SET("s", N(0))], tick=[SET("s", N(0)), {"t": "for", "v": "i", "n": N(5), "body": [{"t": "change", "v": "s", "e": V("i")}]}]))[0], [4, 10])
    check("くりかえし: 0 回", play(proj(["i", "s"], tick=[SET("s", N(3)), {"t": "for", "v": "i", "n": N(0), "body": [SET("s", N(99))]}]))[0][1], 3)
    check("くりかえし: 入れ子(3×4=12 回)", play(proj(["i", "j", "s"], tick=[SET("s", N(0)), {"t": "for", "v": "i", "n": N(3), "body": [{"t": "for", "v": "j", "n": N(4), "body": [{"t": "change", "v": "s", "e": N(1)}]}]}]))[0][2], 12)
    check("くりかえし: 長い(300 回)", play(proj(["i", "s"], tick=[SET("s", N(0)), {"t": "for", "v": "i", "n": N(300), "body": [{"t": "change", "v": "s", "e": N(1)}]}]))[0][1], 300)
    # --- 並びが長い(seq の入れ子) ---
    check("文が 25 個", play(proj(["a"], init=[SET("a", N(0))], tick=[{"t": "change", "v": "a", "e": N(1)}] * 25))[0], [25])
    # --- 描く(画面の画素) ---
    p = proj(["x"], tick=[{"t": "clear", "c": {"t": "c", "v": "#000000"}}, {"t": "rect", "x": N(3), "y": N(4), "w": N(2), "h": N(2), "c": {"t": "c", "v": "#ff0000"}},
                          {"t": "line", "x": N(0), "y": N(0), "x2": N(9), "y2": N(0), "c": {"t": "c", "v": "#00ff00"}}, {"t": "num", "e": N(1234), "x": N(20), "y": N(20), "c": {"t": "c", "v": "#ffffff"}}])
    vals, err, con, src = play(p)
    d = con.display
    W = d.w
    check("描く: 四角・線・画面の色", (d.pix[4 * W + 3], d.pix[5 * W + 4], d.pix[0 * W + 5], d.pix[50 * W + 50]), (0xFF0000, 0xFF0000, 0x00FF00, 0))
    check("描く: 数字(1234 の 1 の縦棒)", d.pix[20 * W + 22] in (0xFFFFFF, 0), True)
    # --- 文字(5×7 のフォント) ---
    COL = lambda v: {"t": "c", "v": v}
    FA = [".###.", "#...#", "#...#", "#####", "#...#", "#...#", "#...#"]
    FB = ["####.", "#...#", "#...#", "####.", "#...#", "#...#", "####."]
    p = proj(["x"], tick=[{"t": "clear", "c": COL("#000000")}, {"t": "text", "txt": "AB a", "x": N(3), "y": N(4), "k": N(1), "c": COL("#ffff00")},
                          {"t": "text", "txt": "A", "x": N(3), "y": N(20), "k": N(2), "c": COL("#00ffff")}, {"t": "rect", "x": N(60), "y": N(60), "w": N(2), "h": N(2), "c": COL("#ff0000")}])
    vals, err, con, src = play(p)
    d = con.display; W = d.w
    cell = lambda x0, y0, w, h, c: ["".join("#" if d.pix[(y0 + j) * W + x0 + i] == c else "." for i in range(w)) for j in range(h)]
    check("文字: 生成が ok(エラーなし)", err, "")
    check("文字: 'A' の形(倍率 1)", cell(3, 4, 5, 7, 0xFFFF00), FA)
    check("文字: 次の字は 6 画素右('B')", cell(9, 4, 5, 7, 0xFFFF00), FB)
    check("文字: 空白をはさんで 'a' は 18 画素右(a の形の一部がある)", sum(r.count("#") for r in cell(21, 4, 5, 7, 0xFFFF00)) > 5, True)
    check("文字: 倍率 2(A の 1 行目が 2×2、2 行目 #...# は ##......##)", (cell(3, 20, 10, 2, 0x00FFFF), cell(3, 22, 10, 1, 0x00FFFF)), (["..######..", "..######.."], ["##......##"]))
    check("文字: 後の命令(四角)も効く・SCALE は元に戻る", (d.pix[60 * W + 60], d.reg.get(0x30)), (0xFF0000, 1))
    check("文字: 使った字の形だけを出力に入れる(A・B・a。全部は入れない)", (src.count("\tc = ") , "fglyph" in src), (3, True))
    src0 = gen(proj(["x"], tick=[{"t": "clear", "c": COL("#000000")}]))
    check("文字: 使わなければフォントを出力しない", ("fglyph" in src0, "fch" in src0), (False, False))
    check("文字: 文字が空・範囲外だけなら何も描かない(エラーなし)", play(proj(["x"], tick=[{"t": "text", "txt": "日本", "x": N(3), "y": N(4), "k": N(1), "c": COL("#ffffff")}]))[1], "")
    check("毎こまの終わりに画面が出る(present)", d.reg[0x24], 1)
    # --- 乱数・キー・おわる ---
    vals, err, con, src = play(proj(["r"], tick=[SET("r", {"t": "rand", "a": N(10)})]), frames=50)
    check("乱数: 0〜9 の範囲", 0 <= vals[0] < 10, True)
    seen = set()
    for k in range(30):
        v, *_ = play(proj(["r"], init=[], tick=[SET("r", {"t": "rand", "a": N(10)})]), frames=k + 1); seen.add(v[0])
    check("乱数: 値がばらつく", len(seen) >= 5, True)
    check("乱数: 0 未満の幅は 0", play(proj(["r"], tick=[SET("r", {"t": "rand", "a": N(0)})]), frames=3)[0], [0])
    keyp = lambda k: {"t": "key", "k": k}
    kp = proj(["r"], tick=[{"t": "if", "c": keyp("left"), "then": [SET("r", N(1))], "else": [SET("r", N(2))]}])
    check("キー: 押されていない", play(kp)[0], [2])
    check("キー: 押されている(台本)", play(kp, frames=3, script="0:kd:28")[0], [1])
    check("キー: 文字キー a", play(proj(["r"], tick=[{"t": "if", "c": keyp("a"), "then": [SET("r", N(1))], "else": [SET("r", N(2))]}]), frames=3, script="0:kd:a")[0], [1])
    check("キー: でない", play(proj(["r"], tick=[{"t": "if", "c": {"t": "not", "a": keyp("left")}, "then": [SET("r", N(1))], "else": [SET("r", N(2))]}]))[0], [1])
    vals, err, con, src = play(proj(["r"], tick=[{"t": "change", "v": "r", "e": N(1)}, {"t": "if", "c": CMP(">", V("r"), N(2)), "then": [{"t": "stop"}], "else": []}]), frames=50)
    check("ゲームをおわる: tick が -1 を返して止まる", (vals, con.frames), ([3], 3))
    # --- 変数の自動追加(棚に無い名前でも動く) ---
    check("棚に無い変数名でも動く", play({"vars": [], "scripts": [{"id": 1, "x": 0, "y": 0, "hat": "tick", "body": [SET("ふしぎ", N(5))]}]})[0] == [], True)
    # --- 帽子が無い積み重ねは動かない・複数の帽子は上から順 ---
    p2 = {"vars": ["a"], "scripts": [{"id": 1, "x": 0, "y": 50, "hat": "tick", "body": [SET("a", N(2))]}, {"id": 2, "x": 0, "y": 10, "hat": "tick", "body": [SET("a", N(1))]},
                                        {"id": 3, "x": 0, "y": 200, "hat": None, "body": [SET("a", N(99))]}]}
    check("帽子の無い積み重ねは動かない・上の帽子から順", play(p2)[0], [2])
    # --- イベントの帽子 ---
    def hat(h, body, k=None, y=0):
        d = {"id": 9, "x": 0, "y": y, "hat": h, "body": body}
        if k: d["k"] = k
        return d
    ev = lambda scripts, vars_=("r", "s"): {"vars": list(vars_), "scripts": [hat("tick", [])] + scripts}
    check("イベント: キーが押されたとき(1 回ずつ。押しっぱなしの繰り返しは数えない)",
          play(ev([hat("key", [{"t": "change", "v": "r", "e": N(1)}], "left")]), frames=40, script="100:kd:28,110:kd:28,120:kd:28,130:ku:28,300:kd:28")[0][0], 2)
    check("イベント: 違うキーは呼ばない", play(ev([hat("key", [SET("r", N(5))], "left")]), frames=20, script="100:kd:29")[0][0], 0)
    check("イベント: キーごとに別の帽子", play(ev([hat("key", [SET("r", N(1))], "left"), hat("key", [SET("s", N(2))], "a")]), frames=30, script="100:kd:a,200:kd:28")[0], [1, 2])
    check("イベント: 同じキーの帽子は上から順に続く", play(ev([hat("key", [SET("r", N(2))], "a", y=50), hat("key", [SET("r", N(1))], "a", y=10)]), frames=20, script="100:kd:a")[0][0], 2)
    check("イベント: キーが離されたとき", play(ev([hat("keyup", [SET("r", N(7))], "a")]), frames=30, script="100:kd:a,200:ku:a")[0][0], 7)
    vals, err, con, src = play(ev([hat("click", [SET("r", {"t": "mx"}), SET("s", {"t": "my"})])]), frames=30, script="100:md:1:33:44")
    check("イベント: クリックされたとき(マウスの x y)", vals, [33, 44])
    check("イベント: クリックのボタン", play(ev([hat("click", [SET("r", {"t": "mb"})])]), frames=30, script="100:md:3:5:6")[0][0], 3)
    check("イベント: マウスが動いたとき", play(ev([hat("mouse", [SET("r", {"t": "mx"}), SET("s", {"t": "my"})])]), frames=30, script="100:mm:12:34")[0], [12, 34])
    check("イベント: マウスの位置は毎こまの帽子からも読める", play({"vars": ["r"], "scripts": [hat("tick", [SET("r", {"t": "my"})]), hat("mouse", [])]}, frames=30, script="100:mm:12:34")[0][0], 34)
    vals, err, con, src = play(ev([hat("key", [{"t": "stop"}], "q")]), frames=50, script="100:kd:q")
    check("イベント: 「ゲームをおわる」で終わる", con.frames < 50, True)
    vals, err, con, src = play(ev([hat("key", [SET("r", N(1))], "a")]), frames=50, script="100:close")
    check("イベント: 帽子があれば閉じるで終わる", con.frames < 50, True)
    check("イベント: 帽子の中の もし・くりかえしも動く", play(ev([hat("key", [{"t": "for", "v": "s", "n": N(4), "body": [{"t": "change", "v": "r", "e": N(1)}]}], "a")]), frames=30, script="100:kd:a")[0][0], 4)
    check("イベント: 帽子が無ければ従来どおり(q で終わる)", play(proj(["r"], tick=[]), frames=50, script="100:kd:q")[2].frames < 50, True)
    # --- スプライト(絵を番地に置き、装置の BLIT で描く) ---
    YEL, RED, BLU = 0xF5D90A, 0xE0453A, 0x2AA8E0
    SPR = lambda name, rows, *more, w=None: {"name": name, "w": w or len(rows[0]), "h": len(rows), "costumes": [rows, *more]}
    SD = lambda n: {"t": "spdraw", "s": n}
    SS = lambda n, x, y: {"t": "spset", "s": n, "x": N(x), "y": N(y)}
    def shot(p, frames=2):
        vals, err, con, src = play(p, frames=frames)
        d = con.display; return (lambda x, y: d.pix[y * d.w + x]), vals, err, src
    def sprj(sprites, init=(), tick=(), vars_=()):
        q = proj(list(vars_), init=list(init), tick=list(tick)); q["sprites"] = sprites; return q
    BG = {"t": "clear", "c": {"t": "c", "v": "#000000"}}
    two = SPR("a", ["e.", ".c"])
    px, vals, err, src = shot(sprj([two], init=[SS("a", 10, 20)], tick=[BG, SD("a")]))
    check("スプライト: 描く(位置と色。透明は描かない)", (px(10, 20), px(11, 20), px(10, 21), px(11, 21), err), (YEL, 0, 0, RED, ""))
    px, *_ = shot(sprj([two], init=[SS("a", 10, 20), {"t": "spscale", "s": "a", "e": N(3)}], tick=[BG, SD("a")]))
    check("スプライト: 大きさ 3 倍", (px(10, 20), px(12, 22), px(13, 20), px(13, 23), px(15, 25), px(16, 25)), (YEL, YEL, 0, RED, RED, 0))
    px, *_ = shot(sprj([two], init=[SS("a", 10, 20), {"t": "spflip", "s": "a", "f": "1"}], tick=[BG, SD("a")]))
    check("スプライト: 左右反転", (px(10, 20), px(11, 20), px(10, 21), px(11, 21)), (0, YEL, RED, 0))
    px, *_ = shot(sprj([two], init=[SS("a", 10, 20), {"t": "spflip", "s": "a", "f": "2"}], tick=[BG, SD("a")]))
    check("スプライト: 上下反転", (px(10, 20), px(11, 20), px(10, 21), px(11, 21)), (0, RED, YEL, 0))
    two2 = SPR("a", ["e.", ".c"], ["h.", ".h"], ["cc", "cc"])
    px, *_ = shot(sprj([two2], init=[SS("a", 5, 5), {"t": "spcost", "s": "a", "e": N(2)}], tick=[BG, SD("a")]))
    check("スプライト: 見た目を 2 番にする", (px(5, 5), px(6, 6), px(6, 5)), (BLU, BLU, 0))
    px, *_ = shot(sprj([two2], init=[SS("a", 5, 5)], tick=[BG, SD("a"), {"t": "spnext", "s": "a"}]), frames=3)
    check("スプライト: 見た目を次にする(毎こま 1 → 2 → 3 番)", (px(6, 5), px(5, 5)), (RED, RED))
    px, *_ = shot(sprj([two2], init=[SS("a", 5, 5)], tick=[BG, SD("a"), {"t": "spnext", "s": "a"}]), frames=4)
    check("スプライト: 見た目は 1 周して戻る", (px(5, 5), px(6, 5)), (YEL, 0))
    px, *_ = shot(sprj([two2], init=[SS("a", 5, 5), {"t": "spshow", "s": "a", "show": "0"}], tick=[BG, SD("a")]))
    check("スプライト: かくすと描かない", px(5, 5), 0)
    px, *_ = shot(sprj([two], init=[SS("a", 10, 20)], tick=[BG, SD("a"), {"t": "spmove", "s": "a", "x": N(2), "y": N(-1)}]), frames=3)
    check("スプライト: ずつ動かす(毎こま x+2 y-1。3 こまめは (14,18))", (px(14, 18), px(10, 20), px(12, 19)), (YEL, 0, 0))
    px, *_ = shot(sprj([two], init=[SS("a", -1, -1)], tick=[BG, SD("a")]))
    check("スプライト: 画面の外へはみ出しても落ちない", px(0, 0), RED)
    ref = lambda p_, k: {"t": "sp", "s": "a", "p": p_}
    vals, err, con, src = play(sprj([SPR("a", ["ee", "ee", "ee"]), ], init=[SS("a", 7, 9), {"t": "spscale", "s": "a", "e": N(4)}, {"t": "spcost", "s": "a", "e": N(1)},
                                      SET("p", ref("x", 0)), SET("q", ref("y", 0)), SET("r", ref("scale", 0)), SET("s", ref("w", 0)), SET("t", ref("h", 0)), SET("u", ref("costume", 0))],
                                tick=[], vars_=list("pqrstu")), frames=1)
    check("スプライト: x y 大きさ 幅 高さ 見た目の番号を読める", vals, [7, 9, 4, 8, 12, 1])
    two_sp = [SPR("a", ["ee", "ee"]), SPR("b", ["cc", "cc"])]
    TOUCH = {"t": "touch", "a": "a", "b": "b"}
    def touching(ax, ay, bx, by, extra=(), neg=False):
        c = {"t": "not", "a": TOUCH} if neg else TOUCH
        return play(sprj(two_sp, init=[SS("a", ax, ay), SS("b", bx, by), *extra], tick=[{"t": "if", "c": c, "then": [SET("r", N(1))], "else": []}], vars_=["r"]), frames=2)[0][0]
    check("スプライト: 触れた(重なる)", touching(10, 10, 11, 11), 1)
    check("スプライト: 触れた(同じ位置)", touching(10, 10, 10, 10), 1)
    check("スプライト: 触れない(辺が接するだけ・離れている)", (touching(10, 10, 12, 10), touching(10, 10, 30, 40)), (0, 0))
    check("スプライト: 大きさを掛けて触れる", touching(10, 10, 15, 10, extra=[{"t": "spscale", "s": "a", "e": N(4)}]), 1)
    check("スプライト: でない(触れていなければ 1)", (touching(10, 10, 30, 30, neg=True), touching(10, 10, 10, 10, neg=True)), (1, 0))
    check("スプライト: かくした物には触れない", touching(10, 10, 10, 10, extra=[{"t": "spshow", "s": "b", "show": "0"}]), 0)
    check("スプライト: 触れた(上下の離れ)", touching(10, 10, 11, 12), 0)
    vals, err, con, src = play(sprj([], init=[{"t": "spset", "s": "x", "x": N(1), "y": N(2)}], tick=[{"t": "spdraw", "s": "x"}, SET("r", {"t": "sp", "s": "x", "p": "x"})], vars_=["r"]), frames=2)
    check("スプライト: 1 つも無いときブロックは何もしない(落ちない)", (vals, err), ([0], ""))
    # 絵を直して保存 → 続きから動いたまま絵が変わる(init は走らない)
    d = tempfile.mkdtemp(); path = os.path.join(d, "g.sn")
    base = sprj([SPR("a", ["e"])], init=[SS("a", 3, 3), SET("r", N(0))], tick=[BG, SD("a"), {"t": "change", "v": "r", "e": N(1)}], vars_=["r"])
    open(path, "w", encoding="utf-8").write(gen(base))
    disp, timer, inp = sc.setup("null:96x96", True, ""); out = io.StringIO()
    con = sc.Console(path, 60, False, out); con.display, con.timer = disp, timer
    for _ in range(3): con.frame(); timer.write(4, 16)
    before = disp.pix[3 * 96 + 3]
    base["sprites"] = [SPR("a", ["h"])]
    open(path, "w", encoding="utf-8").write(gen(base)); os.utime(path, (time.time() + 5, time.time() + 5))
    for _ in range(3): con.frame(); timer.write(4, 16)
    check("スプライト: 絵を直すと続きから変わる(変数 r は 0 に戻らない)", (before, disp.pix[3 * 96 + 3], si.MEMORY.get(0x200000), out.getvalue().count("エラー")), (YEL, BLU, 6, 0))
    big = SPR("a", ["e" * 16] * 16)
    px, *_ = shot(sprj([big], init=[SS("a", 0, 0)], tick=[BG, SD("a")]))
    check("スプライト: 16×16 まで", (px(0, 0), px(15, 15), px(16, 16)), (YEL, YEL, 0))
    px, *_ = shot(sprj([SPR("a", ["eXe", "e.."])], init=[SS("a", 0, 0)], tick=[BG, SD("a")]))
    check("スプライト: 知らない文字は透明", (px(0, 0), px(1, 0), px(2, 0)), (YEL, 0, YEL))
    sp_src = gen(sprj(two_sp, init=[SS("a", 1, 1)], tick=[SD("a"), {"t": "if", "c": TOUCH, "then": [{"t": "spnext", "s": "b"}], "else": []}]))
    d = tempfile.mkdtemp(); path = os.path.join(d, "g.sn"); open(path, "w", encoding="utf-8").write(sp_src)
    r = subprocess.run([sys.executable, os.path.join(HERE, "sign.py"), "--strict", path], capture_output=True, text=True, timeout=60)
    check("スプライト: 生成した Sign は --strict でもエラーなし", ("エラー" in r.stderr, r.returncode), (False, 0))
    # --- 時計のアラーム(n ミリ秒ごと・はじまって n ミリ秒後) ---
    TH = lambda kind, ms, body, y=0: {"id": 9 + y, "x": 0, "y": y, "hat": kind, "ms": N(ms), "body": body}
    def tm(hats, frames=40, vars_=("r", "s")):
        q = {"vars": list(vars_), "scripts": [{"id": 1, "x": 0, "y": 0, "hat": "tick", "body": []}, *hats]}
        return play(q, frames=frames)
    inc = lambda v: [{"t": "change", "v": v, "e": N(1)}]
    check("時計: 100 ミリ秒ごと(640 ミリ秒で 6 回)", tm([TH("every", 100, inc("r"))])[0][0], 6)
    check("時計: はじまって 200 ミリ秒後に 1 回だけ", tm([TH("after", 200, inc("r"))])[0][0], 1)
    check("時計: 帽子ごとに別の周期", tm([TH("every", 100, inc("r"), 0), TH("every", 320, inc("s"), 50)])[0], [6, 1])
    check("時計: 0 や負の周期でも固まらない(毎こま)", tm([TH("every", 0, inc("r"))], frames=10)[0][0] >= 8, True)
    check("時計: 帽子の中の もし・おわる", tm([TH("every", 50, [{"t": "stop"}])], frames=40)[2].frames < 40, True)
    vals, err, con, src = tm([TH("every", 100, inc("r"))])
    check("時計: エラーなし", err, "")
    # 周期を直して保存 → 付け直される(変数は続きから)
    d = tempfile.mkdtemp(); path = os.path.join(d, "g.sn")
    q = {"vars": ["r"], "scripts": [{"id": 1, "x": 0, "y": 0, "hat": "tick", "body": []}, TH("every", 100, inc("r"))]}
    open(path, "w", encoding="utf-8").write(gen(q))
    disp, timer, inp = sc.setup("null:96x96", True, ""); out = io.StringIO()
    con = sc.Console(path, 60, False, out); con.display, con.timer = disp, timer
    for _ in range(20): con.frame(); timer.write(4, 16)
    r1 = si.MEMORY.get(0x200000)
    q["scripts"][1] = TH("every", 20, inc("r")); open(path, "w", encoding="utf-8").write(gen(q)); os.utime(path, (time.time() + 5, time.time() + 5))
    for _ in range(20): con.frame(); timer.write(4, 16)
    r2 = si.MEMORY.get(0x200000)
    check("時計: 周期を直して保存すると付け直される(r は戻らない)", (r1, r2 - r1 >= 14, out.getvalue().count("エラー")), (3, True, 0))
    tsrc = gen(q); open(path, "w", encoding="utf-8").write(tsrc)
    r = subprocess.run([sys.executable, os.path.join(HERE, "sign.py"), "--strict", path], capture_output=True, text=True, timeout=60)
    check("時計: 生成した Sign は --strict でもエラーなし", "エラー" in r.stderr, False)
    # --- メッセージ(送る → 待ち行列 → 次のこまの頭に受け取る帽子) ---
    MH = lambda m, body, me="", y=0: {"id": 20 + y, "x": 0, "y": y, "hat": "onmsg", "m": m, "me": me, "body": body}
    SEND = lambda m, to="": {"t": "send", "m": m, "to": to}
    def msgp(msgs, init=(), tick=(), hats=(), vars_=("r", "s", "t"), sprites=()):
        q = proj(list(vars_), init=list(init), tick=list(tick)); q["msgs"] = list(msgs); q["scripts"] += list(hats)
        if sprites: q["sprites"] = list(sprites)
        return q
    chg = lambda v: {"t": "change", "v": v, "e": N(1)}
    check("メッセージ: 送ると次のこまの頭に受け取る(1 回だけ)", (play(msgp(["go"], init=[SEND("go")], hats=[MH("go", [chg("r")])]), frames=1)[0][0], play(msgp(["go"], init=[SEND("go")], hats=[MH("go", [chg("r")])]), frames=6)[0][0]), (1, 1))
    check("メッセージ: 同じ名前の帽子は全部走る", play(msgp(["go"], init=[SEND("go")], hats=[MH("go", [chg("r")]), MH("go", [chg("s")], y=50)]), frames=3)[0][:2], [1, 1])
    check("メッセージ: 違う名前は走らない", play(msgp(["a", "b"], init=[SEND("a")], hats=[MH("b", [chg("r")])]), frames=4)[0][0], 0)
    chain = msgp(["a", "b"], init=[SEND("a")], hats=[MH("a", [SEND("b")]), MH("b", [chg("s")], y=50)])
    check("メッセージ: 受け取った帽子がまた送れる(1 こまに 1 段ずつ)", (play(chain, frames=1)[0][1], play(chain, frames=2)[0][1]), (0, 1))
    check("メッセージ: 毎こま送ると毎こま受け取る(10 こまで 9 回)", play(msgp(["p"], tick=[SEND("p")], hats=[MH("p", [chg("r")])]), frames=10)[0][0], 9)
    check("メッセージ: 待ち行列は 64 個まで", play(msgp(["p"], init=[{"t": "for", "v": "s", "n": N(100), "body": [SEND("p")]}], hats=[MH("p", [chg("r")])]), frames=3)[0][0], 64)
    sp2 = [SPR("a", ["e"]), SPR("b", ["c"])]
    hats3 = [MH("hit", [chg("r")], me="a", y=0), MH("hit", [chg("s")], me="b", y=40), MH("hit", [chg("t")], me="", y=80)]
    check("メッセージ: スプライト宛て(宛先の帽子と宛先を決めない帽子だけが走る)", play(msgp(["hit"], init=[SEND("hit", "a")], hats=hats3, sprites=sp2), frames=3)[0], [1, 0, 1])
    check("メッセージ: みんな宛てなら全部走る", play(msgp(["hit"], init=[SEND("hit", "")], hats=hats3, sprites=sp2), frames=3)[0], [1, 1, 1])
    check("メッセージ: 触れたら送る", play(msgp(["bump"], init=[SS("a", 5, 5), SS("b", 5, 5)], tick=[{"t": "if", "c": {"t": "touch", "a": "a", "b": "b"}, "then": [SEND("bump", "b")], "else": []}],
                                              hats=[MH("bump", [chg("s")], me="b")], sprites=sp2), frames=3)[0][1], 2)
    check("メッセージ: 受け取る帽子の中で「ゲームをおわる」", play(msgp(["q"], init=[SEND("q")], hats=[MH("q", [{"t": "stop"}])]), frames=20)[2].frames < 20, True)
    check("メッセージ: エラーなし", play(msgp(["go"], init=[SEND("go")], hats=[MH("go", [chg("r")])]), frames=3)[1], "")
    d = tempfile.mkdtemp(); path = os.path.join(d, "g.sn"); open(path, "w", encoding="utf-8").write(gen(hats3 and msgp(["hit"], init=[SEND("hit", "a")], hats=hats3, sprites=sp2)))
    r = subprocess.run([sys.executable, os.path.join(HERE, "sign.py"), "--strict", path], capture_output=True, text=True, timeout=60)
    check("メッセージ: 生成した Sign は --strict でもエラーなし", "エラー" in r.stderr, False)
    # --- クローン ---
    CM = lambda sp, x, y: {"t": "clmake", "s": sp, "x": N(x), "y": N(y)}
    CF = lambda sp, body: {"t": "clfor", "s": sp, "body": list(body)}
    CLP = lambda p_: {"t": "cl", "p": p_}
    CNT = lambda sp: {"t": "clcount", "s": sp}
    def clp(init=(), tick=(), hats=(), sprites=None, vars_=("r", "s", "t")):
        q = proj(list(vars_), init=list(init), tick=list(tick)); q["scripts"] += list(hats)
        q["sprites"] = sprites or [SPR("a", ["ee", "ee"]), SPR("b", ["cc", "cc"])]; return q
    check("クローン: 作ると数が増える", play(clp(init=[CM("a", 1, 1), CM("a", 5, 5), SET("r", CNT("a"))]), frames=1)[0][0], 2)
    check("クローン: 1 つのスプライトにつき 16 個まで", play(clp(init=[{"t": "for", "v": "s", "n": N(30), "body": [CM("a", 0, 0)]}, SET("r", CNT("a"))]), frames=1)[0][0], 16)
    check("クローン: 別のスプライトの数は別", play(clp(init=[CM("a", 1, 1), CM("b", 1, 1), CM("b", 2, 2), SET("r", CNT("a")), SET("s", CNT("b"))]), frames=1)[0][:2], [1, 2])
    mv = clp(init=[CM("a", 10, 20)], tick=[CF("a", [{"t": "clmove", "x": N(2), "y": N(1)}, SET("r", CLP("x")), SET("s", CLP("y"))])])
    check("クローン: 各クローンについて動かす(3 こまで x+6 y+3)", play(mv, frames=3)[0][:2], [16, 23])
    px, *_ = shot(clp(init=[CM("a", 10, 20), CM("a", 40, 50)], tick=[BG, CF("a", [{"t": "cldraw"}])]))
    check("クローン: 描く(2 つとも。元のスプライトは描かない)", (px(10, 20), px(11, 21), px(40, 50), px(0, 0)), (YEL, YEL, YEL, 0))
    px, *_ = shot(clp(init=[SS("a", 70, 70), {"t": "spscale", "s": "a", "e": N(3)}, CM("a", 10, 10)], tick=[BG, CF("a", [{"t": "cldraw"}])]))
    check("クローン: 元の大きさ・向き・見た目を受け継ぐ(3 倍)", (px(10, 10), px(15, 15), px(16, 16), px(70, 70)), (YEL, YEL, 0, 0))
    dl = clp(init=[CM("a", 0, 0), CM("a", 0, 50)], tick=[CF("a", [{"t": "if", "c": CMP(">", CLP("y"), N(30)), "then": [{"t": "cldel"}], "else": []}]), SET("r", CNT("a"))])
    check("クローン: このクローンを消す(条件に合う物だけ)", play(dl, frames=2)[0][0], 1)
    check("クローン: 消した枠はまた使える", play(clp(init=[CM("a", 0, 0), CF("a", [{"t": "cldel"}]), CM("a", 1, 1), CM("a", 2, 2), SET("r", CNT("a"))]), frames=1)[0][0], 2)
    check("クローン: ぜんぶ消す", play(clp(init=[CM("a", 0, 0), CM("a", 1, 1), {"t": "cldelall", "s": "a"}, SET("r", CNT("a"))]), frames=1)[0][0], 0)
    hat = {"id": 30, "x": 0, "y": 0, "hat": "onclone", "s": "a", "body": [{"t": "clset", "x": N(50), "y": N(60)}, {"t": "change", "v": "s", "e": N(1)}]}
    px, vals, err, src = shot(clp(init=[CM("a", 0, 0)], tick=[BG, CF("a", [{"t": "cldraw"}])], hats=[hat]))
    check("クローン: クローンができたとき(初期化が走る)", (px(50, 60), px(0, 0), vals[1], err), (YEL, 0, 1, ""))
    check("クローン: できたときの中でも別のクローンを作れる", play(clp(init=[CM("a", 0, 0), SET("r", CNT("b"))], hats=[{"id": 31, "x": 0, "y": 0, "hat": "onclone", "s": "a", "body": [CM("b", 1, 1), {"t": "clset", "x": N(7), "y": N(8)}]},
                                                                                  {"id": 32, "x": 0, "y": 50, "hat": "onclone", "s": "b", "body": []}], tick=[CF("a", [SET("s", CLP("x"))])]), frames=2)[0][:2], [1, 7])
    tb = clp(init=[SS("b", 10, 10), CM("a", 10, 10), CM("a", 60, 60)], tick=[CF("a", [{"t": "if", "c": {"t": "cltouch", "s": "b"}, "then": [chg("r")], "else": []}])])
    check("クローン: このクローンが [スプライト] に触れた(重なる 1 つだけ)", play(tb, frames=1)[0][0], 1)
    tn = clp(init=[SS("b", 10, 10), CM("a", 60, 60)], tick=[CF("a", [{"t": "if", "c": {"t": "not", "a": {"t": "cltouch", "s": "b"}}, "then": [chg("r")], "else": []}])])
    check("クローン: でない(触れていない)", play(tn, frames=1)[0][0], 1)
    tc = clp(init=[CM("a", 10, 10), CM("a", 60, 60), CM("b", 11, 11), CM("b", 90, 90)], tick=[CF("a", [{"t": "if", "c": {"t": "cltouchc", "s": "b"}, "then": [chg("r")], "else": []}])])
    check("クローン: このクローンが [スプライト] のクローンに触れた", play(tc, frames=1)[0][0], 1)
    nest = clp(init=[CM("a", 0, 0), CM("a", 1, 1), CM("a", 2, 2), CM("b", 0, 0), CM("b", 1, 1)], tick=[CF("a", [CF("b", [chg("r")])])])
    check("クローン: 入れ子(3 × 2 = 6 回)", play(nest, frames=1)[0][0], 6)
    check("クローン: 枠の外では何も起きない(落ちない)", play(clp(init=[{"t": "clmove", "x": N(1), "y": N(1)}, {"t": "cldel"}, SET("r", CLP("x")), CM("a", 0, 0)]), frames=1)[1:2], ("",))
    sp3 = [SPR("a", ["ee"], ["cc"])]
    check("クローン: 見た目を次にする(各クローンごと)", play(clp(init=[CM("a", 0, 0), CM("a", 1, 1)], tick=[CF("a", [{"t": "clnext"}, SET("r", CLP("costume"))])], sprites=sp3), frames=1)[0][0], 2)
    check("クローン: 幅・高さ・大きさ", play(clp(init=[SS("a", 0, 0), {"t": "spscale", "s": "a", "e": N(3)}, CM("a", 0, 0), CF("a", [SET("r", CLP("w")), SET("s", CLP("h")), SET("t", CLP("scale"))])]), frames=1)[0], [6, 6, 3])
    d = tempfile.mkdtemp(); path = os.path.join(d, "g.sn"); open(path, "w", encoding="utf-8").write(gen(nest))
    r = subprocess.run([sys.executable, os.path.join(HERE, "sign.py"), "--strict", path], capture_output=True, text=True, timeout=60)
    check("クローン: 生成した Sign は --strict でもエラーなし", "エラー" in r.stderr, False)
    # --- 厳格モード ---
    srcs = [gen(proj(["a"], init=[SET("a", N(1))], tick=[{"t": "if", "c": CMP("<", V("a"), N(5)), "then": [{"t": "change", "v": "a", "e": N(1)}], "else": []},
                                                        {"t": "for", "v": "a", "n": N(3), "body": []}])),
            gen({"vars": ["a"], "scripts": [{"id": 1, "x": 0, "y": 0, "hat": "tick", "body": []}, {"id": 2, "x": 0, "y": 0, "hat": "key", "k": "left", "body": [SET("a", N(1))]},
                                             {"id": 3, "x": 0, "y": 0, "hat": "click", "body": [SET("a", {"t": "mx"})]}, {"id": 4, "x": 0, "y": 0, "hat": "mouse", "body": []},
                                             {"id": 5, "x": 0, "y": 0, "hat": "keyup", "k": "a", "body": []}]})]
    for k, src in enumerate(srcs):
        d = tempfile.mkdtemp(); path = os.path.join(d, "g.sn"); open(path, "w", encoding="utf-8").write(src)
        r = subprocess.run([sys.executable, os.path.join(HERE, "sign.py"), "--strict", path], capture_output=True, text=True, timeout=60)
        check(f"生成した Sign は --strict でもエラーなし({'イベントあり' if k else '基本'})", ("エラー" in r.stderr, r.returncode), (False, 0))

def ui():
    try:
        from playwright.sync_api import sync_playwright
    except ImportError:
        print("(Playwright が無いので、画面の操作の試験は飛ばします)"); return
    import socket
    s = socket.socket(); s.bind(("127.0.0.1", 0)); port = s.getsockname()[1]; s.close()
    srv = subprocess.Popen([sys.executable, os.path.join(HERE, "sign_editor.py"), "--port", str(port), "--no-open"], stdout=subprocess.DEVNULL)
    time.sleep(1.0)
    game = os.path.join(HERE, "sign_projects", "blocks_game.sn"); had = os.path.exists(game)
    old = open(game, encoding="utf-8").read() if had else None
    try:
        with sync_playwright() as p:
            b = p.chromium.launch(); pg = b.new_page(viewport={"width": 1500, "height": 1000})
            errs = []; pg.on("pageerror", lambda e: errs.append(str(e)))
            pg.goto(f"http://127.0.0.1:{port}/scratch"); pg.wait_for_timeout(400)
            code = lambda: pg.inner_text("#code")
            def drag(src, dst_xy, offset=(8, 8)):
                src.scroll_into_view_if_needed(); pg.wait_for_timeout(80)
                bb = src.bounding_box(); sx, sy = bb["x"] + offset[0], bb["y"] + offset[1]
                pg.mouse.move(sx, sy); pg.mouse.down(); pg.mouse.move(sx + 40, sy + 20, steps=3); pg.mouse.move(*dst_xy, steps=12); pg.mouse.up(); pg.wait_for_timeout(250)
            check("画面: 見本が読み込まれ Sign ができている", ("tick : z ?" in code(), "(rect " in code()), (True, True))
            n0 = code().count("(rect ")
            tgt = pg.locator("#wsin .blk.cmd", has_text="数字").first; tb = tgt.bounding_box()
            drag(pg.locator("#palette .blk.cmd", has_text="四角").first, (tb["x"] + 12, tb["y"] + tb["height"] + 10))
            check("画面: 棚の「四角」を積み重ねの下へ落とすと増える", code().count("(rect "), n0 + 1)
            rects = pg.locator("#wsin .blk.cmd", has_text="四角"); last = rects.nth(rects.count() - 1)
            last.scroll_into_view_if_needed(); slot = last.locator(".slot").first; sb = slot.bounding_box()
            drag(pg.locator("#palette .blk.num", has_text="乱数").first, (sb["x"] + sb["width"] / 2, sb["y"] + sb["height"] / 2), (6, 8))
            check("画面: 乱数の部品を穴へ入れると式になる", "(rnd " in code().split("tick :")[1], True)
            pg.fill("#palette .varbox input", "たま"); pg.click("#palette .varbox button"); pg.wait_for_timeout(200)
            check("画面: 変数をつくる", "たま" in " ".join(pg.locator("#palette .chip").all_inner_texts()), True)
            # 棚へ戻すと消える
            blk = pg.locator("#wsin .blk.cmd", has_text="四角").last; blk.scroll_into_view_if_needed(); bb = blk.bounding_box()
            pg.mouse.move(bb["x"] + 8, bb["y"] + 8); pg.mouse.down(); pg.mouse.move(bb["x"] - 100, bb["y"], steps=4); pg.mouse.move(120, 300, steps=8); pg.mouse.up(); pg.wait_for_timeout(250)
            check("画面: ブロックを棚へ戻すと消える", code().count("(rect "), n0)
            # 数の穴へ打ち込む
            inp = pg.locator("#wsin .blk.cmd", has_text="四角").first.locator("input[type=text]").first
            inp.fill("33"); pg.wait_for_timeout(200)
            check("画面: 穴に数を打つと Sign に出る", "33" in code(), True)
            n_hats = pg.locator("#wsin .blk.hat").count()
            wb = pg.locator("#ws").bounding_box()
            drag(pg.locator("#palette .blk.hat", has_text="押されたとき").first, (wb["x"] + wb["width"] - 140, wb["y"] + 40), (10, 10))
            check("画面: イベントの帽子を置くと増える", pg.locator("#wsin .blk.hat").count(), n_hats + 1)
            newhat = pg.locator("#wsin .blk.hat", has_text="押されたとき").last
            newhat.locator("select").select_option("space"); pg.wait_for_timeout(100)
            nb = newhat.bounding_box()
            drag(pg.locator("#palette .blk.cmd", has_text="ゲームをおわる").first, (nb["x"] + 14, nb["y"] + nb["height"] + 12), (10, 10))
            check("画面: 帽子の下にブロックを積むと on_key に入る", "code = 32 :" in code() and "(QUIT # 1)" in code(), True)
            hn = pg.locator("#wsin .blk.hat").count()
            drag(pg.locator("#palette .blk.hat", has_text="ミリ秒ごと").first, (wb["x"] + wb["width"] - 140, wb["y"] + 330), (10, 10))
            check("画面: 「ミリ秒ごと」の帽子を置くと増える", pg.locator("#wsin .blk.hat").count(), hn + 1)
            eh = pg.locator("#wsin .blk.hat", has_text="ミリ秒ごと").last; eh.locator("input[type=text]").fill("250"); pg.wait_for_timeout(150)
            eb = eh.bounding_box()
            drag(pg.locator("#palette .blk.cmd", has_text="ゲームをおわる").first, (eb["x"] + 14, eb["y"] + eb["height"] + 12), (10, 10))
            check("画面: 時計の帽子の下に積むと on_timer と周期が出る", ("on_timer : id ?" in code(), "(tmevery # 250)" in code()), (True, True))
            pg.fill("#msgName", "あたり"); pg.click("#msgMake"); pg.wait_for_timeout(200)
            check("画面: メッセージをつくる", "あたり" in " ".join(pg.locator("#palette .chip").all_inner_texts()), True)
            hn = pg.locator("#wsin .blk.hat").count()
            drag(pg.locator("#palette .blk.hat", has_text="受け取ったとき").first, (wb["x"] + wb["width"] - 140, wb["y"] + 450), (10, 10))
            mh = pg.locator("#wsin .blk.hat", has_text="受け取ったとき").last; mb = mh.bounding_box()
            drag(pg.locator("#palette .blk.cmd", has_text="に送る").first, (mb["x"] + 14, mb["y"] + mb["height"] + 12), (10, 10))
            check("画面: 受け取る帽子と送るブロックで mh1・msend が出る", (pg.locator("#wsin .blk.hat").count(), "mh1 : v ?" in code(), "(msend " in code(), "(mdisp 0)" in code()), (hn + 1, True, True, True))
            hn = pg.locator("#wsin .blk.hat").count()
            drag(pg.locator("#palette .blk.hat", has_text="クローンができたとき").first, (wb["x"] + wb["width"] - 140, wb["y"] + 560), (10, 10))
            ch = pg.locator("#wsin .blk.hat", has_text="クローンができたとき").last; cb = ch.bounding_box()
            drag(pg.locator("#palette .blk.cmd", has_text="このクローンを消す").first, (cb["x"] + 14, cb["y"] + cb["height"] + 12), (10, 10))
            tb = pg.locator("#wsin .blk.cmd", has_text="数字").first.bounding_box()
            drag(pg.locator("#palette .cblk .head", has_text="各クローンについて").first, (tb["x"] + 12, tb["y"] + tb["height"] + 10))
            check("画面: クローンの帽子・各クローンについて を置くと clhat と foreach の関数が出る", (pg.locator("#wsin .blk.hat").count(), "clhat1 : z ?" in code(), "(CK0 # i)" in code()), (hn + 1, True, True))
            pg.click("#btnPrev"); pg.wait_for_function("!document.querySelector('#stage').hidden", timeout=30000)
            check("画面: プレビューの画像が出る", pg.evaluate("document.querySelector('#stage').src.startsWith('data:image/png')"), True)
            pg.check("#auto"); pg.wait_for_timeout(900)
            check("画面: 自動反映でゲームのファイルができる", os.path.exists(game) and "tick : z ?" in open(game, encoding="utf-8").read(), True)
            # --- スプライト ---
            check("画面: 見本のおばけが棚に出る", pg.locator("#palette .sprow", has_text="おばけ").count(), 1)
            pg.click("#spNew"); pg.wait_for_selector("#spdlg[open]")
            check("画面: 新しいスプライトで絵のエディタが開く", pg.input_value("#spName"), "スプライト")
            cvb = pg.locator("#spcv").bounding_box()
            def cell(x, y): return (cvb["x"] + (x + .5) * cvb["width"] / 8, cvb["y"] + (y + .5) * cvb["height"] / 8)
            pg.click("#spSw .sw[data-ch=c]"); pg.mouse.click(*cell(1, 2))
            pg.click("#spSw .sw[data-ch=h]"); pg.mouse.move(*cell(3, 3)); pg.mouse.down(); pg.mouse.move(*cell(5, 3), steps=6); pg.mouse.up()
            pg.wait_for_timeout(200)
            check("画面: ドットをぬる(クリック・ドラッグ)", pg.evaluate("(()=>{const p=JSON.parse(localStorage.getItem('sign_scratch_project'));const r=p.sprites.at(-1).costumes[0];return [r[2],r[3]]})()"), [".c......", "...hhh.."])
            pg.click("#tEr"); pg.mouse.click(*cell(4, 3)); pg.wait_for_timeout(100)
            check("画面: 消しゴムで透明にする", pg.evaluate("JSON.parse(localStorage.getItem('sign_scratch_project')).sprites.at(-1).costumes[0][3]"), "...h.h..")
            pg.click("#tFill"); pg.click("#spSw .sw[data-ch=e]"); pg.mouse.click(*cell(7, 7)); pg.wait_for_timeout(100)
            filled = pg.evaluate("JSON.parse(localStorage.getItem('sign_scratch_project')).sprites.at(-1).costumes[0]")
            check("画面: バケツで同じ色のつながりをぬる(囲まれた所は残る)", (filled[0], filled[2].count("e"), filled[3]), ("e" * 8, 7, "eeehehee"))
            pg.click("#spAddC"); pg.click("#spDupC"); pg.wait_for_timeout(100)
            check("画面: 見た目を足す・複製する", pg.locator("#spTabs .btn").count(), 3)
            pg.click("#spDelC"); pg.wait_for_timeout(50)
            check("画面: 見た目を消す", pg.locator("#spTabs .btn").count(), 2)
            pg.fill("#spW", "6"); pg.fill("#spH", "5"); pg.press("#spH", "Tab"); pg.wait_for_timeout(100)
            check("画面: 大きさを変えると全部の見た目が合う", pg.evaluate("(()=>{const s=JSON.parse(localStorage.getItem('sign_scratch_project')).sprites.at(-1);return [s.w,s.h,s.costumes.every(c=>c.length===5&&c.every(r=>r.length===6))]})()"), [6, 5, True])
            pg.fill("#spName", "ほし"); pg.press("#spName", "Tab"); pg.click("#spClose"); pg.wait_for_selector("#spdlg", state="hidden"); pg.wait_for_timeout(250)
            check("画面: 名前を変えて閉じる→棚に出る", pg.locator("#palette .sprow", has_text="ほし").count(), 1)
            # ブロックを置く: 「ほしを描く」を毎こまの積み重ねの下へ
            tb = pg.locator("#wsin .blk.cmd", has_text="数字").first.bounding_box()
            drag(pg.locator("#palette .blk.cmd", has_text="を描く").first, (tb["x"] + 12, tb["y"] + tb["height"] + 10))
            check("画面: 「スプライトを描く」を積むと sdraw が出る", "(sdraw" in code().split("tick :")[1], True)
            check("画面: 絵が Sign に入る(状態の番地と BLIT)", ("ART" in code(), "cmd # 6" in code(), "loadart" in code()), (True, True, True))
            # 名前を変えるとブロックの指定も追いかける
            sel = pg.locator("#wsin .blk.sprite select").last; names = sel.locator("option").all_inner_texts()
            check("画面: ブロックのスプライトの選びに名前が並ぶ", ("ほし" in names, "おばけ" in names), (True, True))
            sel.select_option("おばけ"); pg.wait_for_timeout(100)
            pg.locator("#palette .sprow", has_text="おばけ").locator("button", has_text="絵").click(); pg.wait_for_selector("#spdlg[open]")
            pg.fill("#spName", "ghost"); pg.press("#spName", "Tab"); pg.click("#spClose"); pg.wait_for_selector("#spdlg", state="hidden"); pg.wait_for_timeout(250)
            check("画面: 名前を変えるとブロックの指定も追いかける", pg.locator("#wsin .blk.sprite select").last.input_value(), "ghost")
            dr = pg.evaluate("document.querySelector('#spdlg').open"); check("画面: エディタは閉じている", dr, False)
            pg.locator("#palette .sprow", has_text="ほし").locator("button", has_text="×").click(); pg.wait_for_timeout(150)
            check("画面: スプライトを消す", pg.locator("#palette .sprow", has_text="ほし").count(), 0)
            pg.click("#btnPrev"); pg.wait_for_function("!document.querySelector('#stage').hidden", timeout=30000)
            check("画面: スプライトを使ったゲームもプレビューできる", pg.evaluate("document.querySelector('#stage').src.startsWith('data:image/png')") and "エラー" not in pg.inner_text("#status"), True)
            check("画面: ページにエラーがない", errs, [])
            b.close()
    finally:
        srv.terminate()
        if had: open(game, "w", encoding="utf-8").write(old)
        elif os.path.exists(game): os.unlink(game)

if NODE is None:
    print("(node が無いので、コード生成の試験は飛ばします)")
else:
    def guarded():
        global bad
        try: main()
        except Exception as e:                          # 試験の途中の例外も食い違いに数える
            import traceback; traceback.print_exc(); bad += 1
    si.run_with_big_stack(guarded)
    if os.environ.get("SIGN_NO_UI") != "1": ui()
print("\n" + ("全部通った" if not bad else f"{bad} 件 食い違い")); sys.exit(1 if bad else 0)
