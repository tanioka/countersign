"""test_console.py — sign_console.py(ライブ・コーディング)の試験。"""
import io, os, subprocess, sys, tempfile, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sign_interp as si, sign_console as sc

bad = 0
def check(name, got, want):
    global bad
    ok = got == want
    if not ok: bad += 1
    print(("ok  " if ok else "NG  ") + name + ("" if ok else f"\n    得た: {got!r}\n    期待: {want!r}"))

DEMO = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "live_demo.sn"), encoding="utf-8").read()
tmp = tempfile.mkdtemp()
path = os.path.join(tmp, "g.sn")
def write(src):
    with open(path, "w", encoding="utf-8") as f: f.write(src)
    t = time.time() + write.n; write.n += 1; os.utime(path, (t, t))          # 保存の時刻を必ず進める
write.n = 1

def make(reinit=False):
    disp, timer, inp = sc.setup("null", True, "")
    out = io.StringIO()
    con = sc.Console(path, 60, reinit, out)
    con.display, con.timer = disp, timer
    return con, out

def pix(c): return si.MEMORY.get(0x3000), si.MEMORY.get(0x3004)

def main():
    write(DEMO)
    con, out = make()
    for _ in range(5): con.frame()
    x5, y5 = pix(con)
    check("動き出す(init が 1 回走り、tick が回る)", (con.frames, x5 != 20 * 16), (5, True))
    # 保存で定義が入れ替わる。状態(位置)は続きから
    write(DEMO.replace("BALL : 0xFFCC00", "BALL : 0x00FF00").replace("GRAV : 1", "GRAV : 0"))
    con.frame()
    check("保存すると再読み込みされる", con.loads, 2)
    check("再読み込みでも init は走り直さない(位置が飛ばない)", abs(pix(con)[0] - x5) <= 40 + 16, True)
    vy = si.MEMORY.get(0x300C)
    for _ in range(3): con.frame()
    check("GRAV を 0 にすると縦の速さが変わらない", si.MEMORY.get(0x300C), vy)
    # 構文エラー: 前の定義のまま続ける
    n = con.frames
    write(DEMO + "\nbroken : x ?? (\n")
    con.frame(); con.frame()
    check("構文エラーでも止まらず続ける", con.frames, n + 2)
    check("エラーの場所を知らせる", "エラー" in out.getvalue() and ":" in out.getvalue(), True)
    check("エラーは 1 回だけ(同じ版を読み直さない)", out.getvalue().count("エラー:"), 1)
    # 直して保存すると戻る
    write(DEMO.replace("SIZE : 8", "SIZE : 4"))
    con.frame()
    check("直して保存すると再び読める", con.loads, 3)
    # 実行時のエラー: そのこまで止め、直して保存すると続きから
    write(DEMO.replace("draw : z ? seq4 (clear BG)", "draw : z ? seq4 (nosuch BG)").replace("(rect ((get X) / 16)", "(rect ((get X) / 16)"))
    con.frame()
    paused_after = con.paused
    f = con.frames
    con.frame()
    write(DEMO)
    con.frame()
    check("実行時のエラーは止めて待つ", (paused_after or "エラー" in out.getvalue()), True)
    check("直して保存すると続きから動く", (con.paused, con.frames > f), (False, True))
    # tick が -1 で終わり
    write(DEMO.replace("tick : z ? seq3 (step (get X) (get Y) (get VX) (get VY)) (draw 0) (drain 0)", "tick : z ? 0 - 1"))
    con.frame()
    check("tick が -1 を返すと終わる", con.frame(), False)
    # --reinit: 保存のたびに init
    write(DEMO)
    con, out = make(reinit=True)
    for _ in range(3): con.frame()
    write(DEMO + "\n")
    con.frame()
    check("--reinit は保存のたびに init を呼ぶ(位置が初めに戻る)", si.MEMORY.get(0x3000) <= 20 * 16 + 80, True)
    # 定義でない行は読まない
    write(DEMO + "\nX # 9999\n")
    con, out = make()
    con.frame()
    check("定義でない行は読まず、知らせる", ("定義でない行が 1" in out.getvalue(), si.MEMORY.get(0x3000) != 9999), (True, True))
    # 最初から壊れていたら待つ
    write("tick : z ? (\n")
    con, out = make()
    con.frame(); con.frame()
    check("最初から壊れていても落ちない", (con.env, con.frames), (None, 0))
    write(DEMO)
    con.frame()
    check("直すと始まる", con.frames, 1)
    # スイカ版: 動かしたまま定義を替える(果物の置き場は残る)
    SU = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "suika_live.sn"), encoding="utf-8").read()
    write(SU)
    con, out = make()
    for _ in range(40): con.frame()
    k0 = si.MEMORY.get(0x3020)
    write(SU.replace("PASSES : 4", "PASSES : 3"))
    for _ in range(40): con.frame()
    check("スイカ版: 保存しても続きから動く(果物の数は残る)", (con.loads, con.paused, si.MEMORY.get(0x3020) >= k0), (2, False, True))
    # --- イベント(コールバック) ---
    EV = """seq2 : a b ? b
seq3 : a b c ? c
A : 0x3000
B : 0x3004
C : 0x3008
L : 0x3100
cnt : z ? seq2 (C # ((@C) + 1)) 0
on_key : code ?
	code = 113 : 0 - 1
	seq3 (A # ((@A) + 1)) (L # code) 0
on_keyup : code ? B # ((@B) + 1)
on_click : x y b ? seq3 (L + 4 # x) (L + 8 # y) (L + 12 # b)
on_mouse : x y ? L + 16 # (x * 1000 + y)
init : z ? seq3 (A # 0) (B # 0) (C # 0)
tick : z ? cnt 0
"""
    def run_ev(src, script, frames=60, **kw):
        write(src)
        disp, timer, inp = sc.setup("null", True, script)
        out = io.StringIO(); con = sc.Console(path, 60, False, out); con.display, con.timer = disp, timer
        n = 0
        for _ in range(frames):
            n += 1
            if not con.frame(): break
            timer.write(4, 16)                                  # 仮想の時計を 1 こま分(16ms)進める
        return con, out.getvalue(), n
    con, out, n = run_ev(EV, "100:kd:a,200:ku:a,300:kd:b")
    check("イベント: on_key が 1 回ずつ呼ばれる(code は ASCII)", (si.MEMORY.get(0x3000), si.MEMORY.get(0x3100)), (2, 98))
    check("イベント: on_keyup が呼ばれる", si.MEMORY.get(0x3004), 1)
    con, out, n = run_ev(EV, "100:kd:a,110:kd:a,120:kd:a,130:ku:a")
    check("イベント: 押しっぱなしの自動繰り返しは呼ばない", si.MEMORY.get(0x3000), 1)
    con, out, n = run_ev(EV, "100:md:2:30:40,200:mm:5:6")
    check("イベント: on_click に x y button、on_mouse に x y", (si.MEMORY.get(0x3104), si.MEMORY.get(0x3108), si.MEMORY.get(0x310C), si.MEMORY.get(0x3110)), (30, 40, 2, 5006))
    con, out, n = run_ev(EV, "100:kd:q")
    check("イベント: -1 を返すと終わる", (n < 60, con.frames <= 8), (True, True))
    con, out, n = run_ev(EV, "100:close")
    check("イベント: on_close が無ければ閉じるで終わる", n < 60, True)
    con, out, n = run_ev(EV + "on_close : z ? 0\n", "100:close", frames=30)
    check("イベント: on_close を定義すると、0 を返せば続ける", n, 30)
    con, out, n = run_ev(EV + "on_close : z ? 0 - 1\n", "100:close")
    check("イベント: on_close が -1 を返すと終わる", n < 60, True)
    con, out, n = run_ev(EV.replace("on_keyup : code ? B # ((@B) + 1)", "g : i ? 0\non_keyup : code ? [0 ~+ 0 ~ 5] $g"), "100:kd:a,110:ku:a,200:kd:b", frames=60)
    check("イベント: 関数の誤りは場所を知らせて止める", ("エラー" in out and "on_keyup" in out, con.paused), (True, True))
    write(EV.replace("g : i ? 0\non_keyup : code ? [0 ~+ 0 ~ 5] $g", "on_keyup : code ? 0"))
    con.frame(); con.timer.write(4, 16); con.frame()
    check("イベント: 直して保存すると続きから動く", (con.paused, si.MEMORY.get(0x3000) >= 1), (False, True))
    # 定義しなければ行列に触れない(従来のゲームが自分で読める)
    con, out, n = run_ev("""A : 0x3000
inp : 0x9300000
init : z ? A # 0
tick : z ? A # (@(inp + 0x00))
""", "50:kd:a,60:kd:b", frames=20)
    check("イベントを定義しなければ、出来事の行列に触れない", si.MEMORY.get(0x3000), 2)
    # 保存で定義が入れ替わる: 途中で on_key の中身を替える
    write(EV)
    disp, timer, inp = sc.setup("null", True, "100:kd:a,400:kd:b")
    out = io.StringIO(); con = sc.Console(path, 60, False, out); con.display, con.timer = disp, timer
    for _ in range(12): con.frame(); timer.write(4, 16)
    write(EV.replace("seq3 (A # ((@A) + 1)) (L # code) 0", "seq3 (A # ((@A) + 10)) (L # code) 0"))
    for _ in range(40): con.frame(); timer.write(4, 16)
    check("イベント: 動かしたまま on_key を替えられる(1 + 10)", si.MEMORY.get(0x3000), 11)
    # --- スプライト(BLIT)の見本 ---
    SP = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "sprite_demo.sn"), encoding="utf-8").read()
    def run_sp(script, frames):
        write(SP)
        disp, timer, inp = sc.setup("null:96x96", True, script)
        out = io.StringIO(); con = sc.Console(path, 60, False, out); con.display, con.timer = disp, timer
        for _ in range(frames): con.frame(); timer.write(4, 16)
        return disp, out.getvalue()
    d, out = run_sp("", 3)
    W = 96
    check("スプライト: 絵が置かれる(2 倍。上段の黄、白目、黒目、透明の角)", (d.pix[40 * W + 44], d.pix[44 * W + 44], d.pix[46 * W + 46], d.pix[40 * W + 40], out), (0xFFCC00, 0xFFFFFF, 0x202020, 0x101830, ""))
    d, out = run_sp("20:kd:28", 5)                                   # 左へ 4 動いて、左右反転(X=36)
    check("スプライト: 向きで左右反転(黒目の位置が入れ替わる)", (d.pix[46 * W + 38], d.pix[46 * W + 46]), (0x202020, 0xFFFFFF))
    d, out = run_sp("20:kd:30", 5)                                   # 拡大 3
    check("スプライト: 拡大が変わる(3 倍)", d.pix[50 * W + 50], 0x202020)
    # --- 時計のアラーム(on_timer) ---
    TM = """
tm : 0x9200000
id_ : tm + 0x08
after : tm + 0x0C
every : tm + 0x10
cancel : tm + 0x14
seq2 : a b ? b
seq3 : a b c ? c
log : i ? seq2 ((0x3200 + ((@0x3200) * 4) + 4) # i) ((0x3200) # ((@0x3200) + 1))
on_timer : id ? seq2 (log id) (id = 9 : 0 - 1 | 0)
init : z ? seq3 (0x3200 # 0) ((id_ # 1) | 0) ((after # 50) | 0)
tick : z ? 0
"""
    def run_tm(src, frames, extra=None):
        write(src)
        disp, timer, inp = sc.setup("null", True, "")
        out = io.StringIO(); con = sc.Console(path, 60, False, out); con.display, con.timer = disp, timer
        for k in range(frames):
            if extra: extra(k, timer)
            if not con.frame(): break
            timer.write(4, 16)
        return con, out.getvalue(), timer
    con, out, timer = run_tm(TM, 10)
    check("タイマー: 50 ミリ秒後に 1 回だけ on_timer が呼ばれる", (si.MEMORY.get(0x3200), si.MEMORY.get(0x3204), out), (1, 1, ""))
    EV2 = TM.replace("((after # 50) | 0)", "((every # 40) | 0)")
    con, out, timer = run_tm(EV2, 20)                                  # 320 ms → 40 ごと = 7 回(こまは 16 ms 刻み)
    check("タイマー: n ミリ秒ごとに何度も呼ばれる", si.MEMORY.get(0x3200) in (6, 7, 8), True)
    EV3 = TM.replace("((after # 50) | 0)", "((after # 50) | 0) ((id_ # 2) | 0) ((after # 100) | 0)").replace("seq3 (0x3200 # 0) ((id_ # 1) | 0) (", "seq5 (0x3200 # 0) ((id_ # 1) | 0) (").replace("| 0)\ntick", "| 0) 0 0\ntick")
    EV3 = TM.replace("init : z ? seq3 (0x3200 # 0) ((id_ # 1) | 0) ((after # 50) | 0)", "seq5 : a b c d e ? e\ninit : z ? seq5 (0x3200 # 0) ((id_ # 1) | 0) ((after # 50) | 0) ((id_ # 2) | 0) ((after # 100) | 0)")
    con, out, timer = run_tm(EV3, 12)
    check("タイマー: 番号ごとに違う時刻で、早い順に呼ばれる", (si.MEMORY.get(0x3200), si.MEMORY.get(0x3204), si.MEMORY.get(0x3208)), (2, 1, 2))
    EV4 = EV3.replace("((after # 100) | 0)", "((after # 100) | 0) ((cancel # 2) | 0)").replace("seq5 (0x3200 # 0)", "seq6 (0x3200 # 0)").replace("init : z ? seq6", "seq6 : a b c d e f ? f\ninit : z ? seq6")
    con, out, timer = run_tm(EV4, 12)
    check("タイマー: 取り消すと鳴らない", (si.MEMORY.get(0x3200), si.MEMORY.get(0x3204)), (1, 1))
    EV5 = TM.replace("((after # 50) | 0)", "((id_ # 9) | 0) ((after # 20) | 0)").replace("seq3 (0x3200 # 0) ((id_ # 1) | 0) (", "seq5 : a b c d e ? e\ninit : z ? seq5 (0x3200 # 0) ((id_ # 1) | 0) ((after # 10) | 0) ((id_ # 9) | 0) (").replace("init : z ? seq3","init0 : z ? seq3")
    con, out, timer = run_tm(EV5, 50)
    check("タイマー: on_timer が -1 を返すと終わる", con.frames < 50, True)
    NOT = TM.replace("on_timer", "on_timerX")
    con, out, timer = run_tm(NOT, 10)
    check("タイマー: on_timer が無ければ何も起きない", (si.MEMORY.get(0x3200), out), (0, ""))

    # tick が無い
    write("init : z ? 0\n")
    con, out = make()
    con.frame()
    check("tick が無いと知らせて待つ", "tick が定義されていません" in out.getvalue(), True)

# --- 窓を開けないとき(tkinter が無い・画面が無い): トレースバックで落ちず、理由を知らせて「窓が閉じられた」ことにして終わる ---
HERE = os.path.dirname(os.path.abspath(__file__))
code = ("import sys, runpy; sys.modules['tkinter'] = None; sys.argv = ['sign_console.py', %r, '--display=window:4:96x96']; "
        "runpy.run_path(%r, run_name='__main__')") % (os.path.join(HERE, "star_catch.sn"), os.path.join(HERE, "sign_console.py"))
r = subprocess.run([sys.executable, "-c", code], capture_output=True, timeout=60)
e = r.stderr.decode()
check("窓を開けない: 理由を知らせて終わる(トレースバックなし・終了コード 0)", (r.returncode, "Traceback" in e, "エラー: 窓を開けません" in e), (0, False, True))

si.run_with_big_stack(main)
print("\n" + ("全部通った" if not bad else f"{bad} 件 食い違い")); sys.exit(1 if bad else 0)
