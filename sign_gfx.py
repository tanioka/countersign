"""sign_gfx.py — 描画装置(メモリマップド)。インタープリタがバックエンドになる。

Sign のプログラムは、番地への書き込み `#` と読み出し `@` だけで描く。装置は番地の帯(base から SIZE)に
置かれ、インタープリタは帯への書き込み・読み出しを装置に回す(UART と同じ考え方)。
レジスタは全部 Int。番地はバイト単位で 4 刻みを使う(実機に載せ替えても番地の並びが変わらないように)。

    base + 0x00  WIDTH    R   幅(画素)
    base + 0x04  HEIGHT   R   高さ(画素)
    base + 0x08  COLOR    RW  現在の色 0xRRGGBB
    base + 0x0C  X        RW  座標 x
    base + 0x10  Y        RW  座標 y
    base + 0x14  CMD      W   命令(下の表)。書いた瞬間に実行する
    base + 0x18  ARG0     RW  命令の引数 0(X2 / 幅)
    base + 0x1C  ARG1     RW  命令の引数 1(Y2 / 高さ)
    base + 0x20  STATUS   R   0: 正常、1: 範囲外などで無視した、2: 知らない命令
    base + 0x24  FRAME    R   PRESENT した回数
    base + 0x1000 + 4*(y*WIDTH + x)   RW   画素(0xRRGGBB)。直に書いても読んでもよい

    CMD 1 PLOT    (X,Y) に COLOR の画素
    CMD 2 CLEAR   全面を COLOR で塗る
    CMD 3 PRESENT いまの画面をバックエンドへ出す(PNG の保存・文字での表示・ウィンドウ更新)
    CMD 4 LINE    (X,Y)-(ARG0,ARG1) に COLOR の線
    CMD 5 RECT    (X,Y) から 幅 ARG0 高さ ARG1 を COLOR で塗る
    CMD 6 BLIT    スプライト。番地 SRC に置いた 幅 ARG0 × 高さ ARG1 の絵(1 画素 1 語、0xRRGGBB、行を上から・左から並べる)を (X,Y) に描く
    base + 0x28  SRC     RW  BLIT の絵の先頭の番地(インタープリタのメモリ)
    base + 0x2C  TRANS   RW  透明にする色(この色の画素は描かない。未設定か負なら無し)。未書き込みの語・負の語・Int でない語は、いつも透明
    base + 0x30  SCALE   RW  拡大(整数、既定 1。1 画素を SCALE×SCALE の四角で描く)
    base + 0x34  FLIP    RW  向き。ビット 0 で左右、ビット 1 で上下を反転(既定 0)。ビット 2(値 4)は「型抜き」:
                         0 でない語を、語の色ではなく COLOR で描く(0・負・未書き込みは透明)。文字(font.sn)がこれで描く
  BLIT は画面からはみ出した所を捨てて STATUS=1 にする。幅×高さは 65536 まで(それを越えたら何もせず STATUS=1)。

範囲外の座標は黙って捨てて STATUS=1。未書き込みのレジスタを読むと __(インタープリタの規則どおり)。
時間(タイマー装置 Timer。TIMER_BASE = 0x9200000):
    base + 0x00  NOW    R   起動からの経過ミリ秒
    base + 0x04  SLEEP  W   書いたミリ秒だけ待つ(待つ間もウィンドウは応答する)。負や Int でない値は無視
    base + 0x08  ID     RW  アラームの番号(次に書く AFTER / EVERY の相手)
    base + 0x0C  AFTER  W   n(0 以上)ミリ秒後に 1 回鳴らす。同じ番号は置き換え
    base + 0x10  EVERY  W   n(1 以上)ミリ秒ごとに鳴らす。遅れた分は 1 回にまとめる
    base + 0x14  CANCEL W   その番号のアラームを取り消す
    鳴ったアラームは、sign_console.py が 1 こまの頭に on_timer : id ? で呼ぶ(入力の出来事のあと、早い順)。
    virtual 指定なら実際には待たず、時計だけを進める(試験・録画用。決定的)。

入力(Input 装置。INPUT_BASE = 0x9300000)。出来事の待ち行列を、先頭だけ覗いて、書いて捨てる(読みに副作用を持たせない):
    base + 0x00  COUNT   R   待っている出来事の数
    base + 0x04  TYPE    R   先頭の種類。0 なし / 1 キー押下 / 2 キー離す / 3 マウス移動 / 4 マウス押下 / 5 マウス離す / 6 閉じる
    base + 0x08  CODE    R   先頭のキー符号、またはマウスのボタン(1 左 2 中 3 右)
    base + 0x0C  EX      R   先頭の出来事のときのマウス x(表示の画素。倍率を掛ける前)
    base + 0x10  EY      R   同じく y
    base + 0x14  POP     W   何を書いても先頭を捨てる(空なら何もしない)
    base + 0x20  MX      R   いまのマウス x
    base + 0x24  MY      R   いまのマウス y
    base + 0x28  MBTN    R   いま押されているボタンのビット(1 左 2 中 4 右)
    base + 0x100 + 4*code  R   そのキーがいま押されていれば 1、でなければ 0
  キー符号: 印字できる文字は ASCII(a は 97)、Backspace 8、Tab 9、Return 13、Escape 27、Space 32、
            左 0x1C 右 0x1D 上 0x1E 下 0x1F(ASCII の FS/GS/RS/US)。行列は 256 件で、あふれたら古い方から捨てる。
  走らせ方: window なら本物の入力。--input=SCRIPT なら台本(ミリ秒:種類:…、コンマ区切り)を、タイマーの時刻が来たら
            行列へ入れる。例 100:kd:a,150:ku:a,200:mm:10:5,300:md:1:10:5,400:close  (キーは文字か数)

バックエンド: png:ファイル名({n} があれば PRESENT の番号を入れる) / ascii(端末に明るさで出す) /
  window[:倍率](tkinter のウィンドウ。PRESENT で更新する。入力装置を読まないプログラムは、終わっても閉じるまで残し、読むプログラム(ゲームなど)は、終わると窓も閉じる) / null。
"""
import os, struct, sys, zlib
from array import array
from sign_mem import DevMem

BASE_DEFAULT = 0x9100000
R_WIDTH, R_HEIGHT, R_COLOR, R_X, R_Y, R_CMD, R_ARG0, R_ARG1, R_STATUS, R_FRAME = range(0x00, 0x28, 4)
R_SRC, R_TRANS, R_SCALE, R_FLIP = 0x28, 0x2C, 0x30, 0x34
FB = 0x1000
PLOT, CLEAR, PRESENT, LINE, RECT, BLIT = 1, 2, 3, 4, 5, 6

def write_png(path, w, h, pix):
    if pix and (max(pix) > 0xFFFFFF or min(pix) < 0): pix = [c & 0xFFFFFF for c in pix]
    a = array("I", pix)
    if a.itemsize != 4: a = array("L", pix)
    if sys.byteorder == "little": a.byteswap()             # 画素ごとに 4 バイト(先頭は 0)の並びにして、先頭を除いた 3 バイトずつを集める
    b = a.tobytes()
    rgb = bytearray(3 * w * h)
    rgb[0::3], rgb[1::3], rgb[2::3] = b[1::4], b[2::4], b[3::4]
    row = 3 * w
    raw = bytearray((row + 1) * h)                         # 各行の先頭 1 バイトはフィルタ種別(0 = なし)
    for y in range(h): raw[y * (row + 1) + 1:(y + 1) * (row + 1)] = rgb[y * row:(y + 1) * row]
    def chunk(tag, data):
        body = tag + data
        return struct.pack(">I", len(data)) + body + struct.pack(">I", zlib.crc32(body) & 0xFFFFFFFF)
    with open(path, "wb") as f:
        f.write(b"\x89PNG\r\n\x1a\n" + chunk(b"IHDR", struct.pack(">IIBBBBB", w, h, 8, 2, 0, 0, 0))
                + chunk(b"IDAT", zlib.compress(bytes(raw))) + chunk(b"IEND", b""))

class Display(DevMem):
    def __init__(self, w=64, h=32, backend="ascii", base=BASE_DEFAULT):
        self.w, self.h, self.base = w, h, base
        self.size = FB + 4 * w * h
        self.pix = [0] * (w * h)
        self.dirty = set(range(h))                         # 最後の PRESENT のあとに変わった行(window は変わった行だけ送る)
        self.hexc = {}                                     # 色 → "#rrggbb"
        self.reg = {R_COLOR: 0xFFFFFF, R_X: 0, R_Y: 0, R_ARG0: 0, R_ARG1: 0, R_STATUS: 0, R_FRAME: 0}
        self.backend = backend
        self.win = None                                    # window バックエンドの Tk 一式(最初の PRESENT で作る)
        self.on_event = None                               # 入力装置の push(種類, 符号, x, y)

    # --- 速い道(インタープリタの run_pure)への申し出 ---
    pure_write_ok = True                                    # 書き込みは記録して、成功したあと順に再生してよい(読みは今までどおり普通の道)
    def pure_write_safe(self, off, v):
        """この書き込みを後で再生しても同じ結果になるか。BLIT はインタープリタのメモリを読むので、書き込みの順が変わらないよう除く"""
        return not (off == R_CMD and v == BLIT)

    # --- インタープリタが呼ぶ口 ---
    def read(self, off):
        if off == R_WIDTH: return self.w
        if off == R_HEIGHT: return self.h
        if off >= FB:
            i = (off - FB) // 4
            return self.pix[i] if 0 <= i < len(self.pix) else None
        return self.reg.get(off)

    def write(self, off, v):
        if not isinstance(v, int) or isinstance(v, bool): self.reg[R_STATUS] = 1; return
        if off >= FB:
            i = (off - FB) // 4
            if 0 <= i < len(self.pix): self.pix[i] = v & 0xFFFFFF; self.dirty.add(i // self.w)
            return
        if off == R_CMD: return self.command(v)
        if off in (R_COLOR, R_X, R_Y, R_ARG0, R_ARG1, R_SRC, R_TRANS, R_SCALE, R_FLIP): self.reg[off] = v & 0xFFFFFF if off == R_COLOR else v

    # --- 命令 ---
    def put(self, x, y, c):
        if 0 <= x < self.w and 0 <= y < self.h: self.pix[y * self.w + x] = c; self.dirty.add(y)
        else: self.reg[R_STATUS] = 1

    def command(self, cmd):
        r = self.reg; r[R_STATUS] = 0
        x, y, c, a0, a1 = r[R_X], r[R_Y], r[R_COLOR], r[R_ARG0], r[R_ARG1]
        if cmd == PLOT: self.put(x, y, c)
        elif cmd == CLEAR: self.pix = [c] * (self.w * self.h); self.dirty = set(range(self.h))
        elif cmd == PRESENT: self.present()
        elif cmd == LINE:                                  # Bresenham
            dx, dy, sx, sy = abs(a0 - x), -abs(a1 - y), 1 if x < a0 else -1, 1 if y < a1 else -1
            err = dx + dy
            while True:
                self.put(x, y, c)
                if x == a0 and y == a1: break
                e2 = 2 * err
                if e2 >= dy: err += dy; x += sx
                if e2 <= dx: err += dx; y += sy
        elif cmd == RECT:
            if a0 > 0 and a1 > 0:                          # 行ごとに切り出して塗る。はみ出した画素は捨てて STATUS=1
                x0, x1, y0, y1 = max(x, 0), min(x + a0, self.w), max(y, 0), min(y + a1, self.h)
                if x0 < x1 and y0 < y1:
                    fill, w = [c] * (x1 - x0), self.w
                    for yy in range(y0, y1): self.pix[yy * w + x0:yy * w + x1] = fill
                    self.dirty.update(range(y0, y1))
                if x0 != x or x1 != x + a0 or y0 != y or y1 != y + a1: r[R_STATUS] = 1
        elif cmd == BLIT: self.blit()
        else: r[R_STATUS] = 2

    def blit(self):
        r = self.reg
        w, h, src = r.get(R_ARG0, 0), r.get(R_ARG1, 0), r.get(R_SRC)
        sc, flip, trans = r.get(R_SCALE) or 1, r.get(R_FLIP) or 0, r.get(R_TRANS)
        mem = self.memory()
        if mem is None or not isinstance(src, int) or w <= 0 or h <= 0 or w * h > 65536 or sc < 1 or sc > 64: r[R_STATUS] = 1; return
        x0, y0, cut = r[R_X], r[R_Y], False
        for row in range(h):
            sr = h - 1 - row if flip & 2 else row
            for col in range(w):
                sx = w - 1 - col if flip & 1 else col
                v = mem.get(src + 4 * (sr * w + sx))
                if not isinstance(v, int) or isinstance(v, bool) or v < 0 or v == trans: continue
                if flip & 4:
                    if v == 0: continue
                    v = r.get(R_COLOR, 0)
                v &= 0xFFFFFF
                for dy in range(sc):
                    y = y0 + row * sc + dy
                    for dx in range(sc):
                        x = x0 + col * sc + dx
                        if 0 <= x < self.w and 0 <= y < self.h: self.pix[y * self.w + x] = v; self.dirty.add(y)
                        else: cut = True
        if cut: r[R_STATUS] = 1

    def present(self):
        n = self.reg[R_FRAME] = self.reg[R_FRAME] + 1
        b = self.backend
        if b.startswith("png:"):
            write_png(b[4:].replace("{n}", str(n)), self.w, self.h, self.pix)
        elif b == "window" or b.startswith("window:"):
            self.show_window(int(b[7:]) if b[7:].isdigit() else 4)
        elif b == "ascii":
            ramp = " .:-=+*#%@"
            for y in range(self.h):
                row = ""
                for c in self.pix[y * self.w:(y + 1) * self.w]:
                    lum = (((c >> 16) & 255) * 299 + ((c >> 8) & 255) * 587 + (c & 255) * 114) // 1000
                    row += ramp[lum * (len(ramp) - 1) // 255]
                sys.stdout.write(row + "\n")
            sys.stdout.flush()

    # --- window バックエンド ---
    # tkinter は作ったスレッドからしか触れない。インタープリタが走るスレッドで作り、同じスレッドで更新する。
    def show_window(self, scale):
        if self.win is None:
            try:
                import tkinter as tk
                root = tk.Tk(); root.title("Sign display")
                img = tk.PhotoImage(width=self.w, height=self.h)
                label = tk.Label(root, image=img.zoom(scale), borderwidth=0); label.pack()
            except Exception as e:                          # tkinter が入っていない・画面(DISPLAY)が無い、など。落とさず、理由を知らせて「窓が閉じられた」ことにする
                print(f"エラー: 窓を開けません({type(e).__name__}): {e}。tkinter(Linux では python3-tk)と画面(DISPLAY)があるか確かめるか、--display=png:ファイル名:幅x高さ か --display=ascii:幅x高さ を使ってください", file=sys.stderr)
                self.win = {"open": False}
                if self.on_event: self.on_event(6, 0, 0, 0)
                return
            self.win = {"tk": tk, "root": root, "img": img, "label": label, "scale": scale, "open": True}
            def closed():
                if self.on_event: self.on_event(6, 0, 0, 0)
                self.win.update(open=False); root.destroy()
            root.protocol("WM_DELETE_WINDOW", closed)
            self.bind_input(root, scale)
            self.take_focus(root)
        win = self.win
        if not win["open"]: return                          # 閉じられた後の PRESENT は捨てる
        if os.environ.get("SIGN_KEYDEBUG"):
            self.dbg_n = getattr(self, "dbg_n", 0) + 1
            if self.dbg_n <= 60 or self.dbg_n % 60 == 0: print(f"画面更新の呼び出し {self.dbg_n} 回目: 変わった行 {len(self.dirty)}", file=sys.stderr)
        if self.dirty:                                      # 変わった行だけ Tk へ送る
            hx, w = self.hexc, self.w
            for y in sorted(self.dirty):
                row = " ".join([hx.get(c) or hx.setdefault(c, "#%06x" % c) for c in self.pix[y * w:(y + 1) * w]])
                win["img"].put("{" + row + "}", to=(0, y))
            self.dirty = set()
            zoomed = win["img"].zoom(win["scale"]); win["label"].configure(image=zoomed); win["label"].image = zoomed
        try: win["root"].update()
        except win["tk"].TclError: win["open"] = False

    def take_focus(self, root):
        """窓を前に出してキーボードの焦点を取る。取らないと、キーはこの窓でなく、起動した端末へ行って、入力が利かない
        (macOS・Windows では、別の窓から起動した窓は焦点を持たずに開くことがある)。窓をクリックしても焦点が移る。"""
        try:
            root.lift(); root.attributes("-topmost", True); root.update()
            root.attributes("-topmost", False); root.focus_force()
        except Exception: pass
        root.bind("<Button-1>", lambda e: root.focus_force(), add="+")

    TK_KEYS = {"Left": 0x1C, "Right": 0x1D, "Up": 0x1E, "Down": 0x1F, "Escape": 27, "Return": 13,
               "BackSpace": 8, "Tab": 9, "space": 32}

    def bind_input(self, root, scale):
        def code(e):
            if e.keysym in self.TK_KEYS: return self.TK_KEYS[e.keysym]
            return ord(e.char) if e.char and ord(e.char[0]) < 128 else 0
        def ev(kind):
            def f(e):
                if os.environ.get("SIGN_KEYDEBUG") and kind in (1, 2, 4): print(f"入力の届き方: 種類 {kind} キー {e.keysym!r} → 符号 {code(e) if kind in (1, 2) else e.num}", file=sys.stderr)
                if not self.on_event: return
                if kind in (1, 2):
                    c = code(e)
                    if c: self.on_event(kind, c, 0, 0)
                elif kind == 3: self.on_event(3, 0, e.x // scale, e.y // scale)
                else: self.on_event(kind, e.num, e.x // scale, e.y // scale)
            return f
        root.bind("<KeyPress>", ev(1)); root.bind("<KeyRelease>", ev(2)); root.bind("<Motion>", ev(3))
        root.bind("<ButtonPress>", ev(4)); root.bind("<ButtonRelease>", ev(5))

    def pump(self):
        w = self.win
        if w and w["open"]:
            try: w["root"].update()
            except w["tk"].TclError: w["open"] = False

    def finish(self):
        """プログラムが終わったとき。入力を読まないプログラムの window は、利用者が閉じるまで残す。入力を読むもの(ゲームなど)は閉じる。"""
        w = self.win
        stay = bool(w and w["open"] and not getattr(self, "reads_input", False))   # 入力を読むプログラム(ゲームなど)は、終わったら窓も閉じる
        if os.environ.get("SIGN_KEYDEBUG"): print(f"プログラムが終わりました(窓は {'開いたまま' if stay else '閉じます'})", file=sys.stderr)
        if stay:
            try: w["root"].mainloop()
            except w["tk"].TclError: pass
        self.release()

    def release(self):
        """Tk の画像と窓は、作ったスレッドの中で片付ける(別のスレッドで捨てられると
        「main thread is not in main loop」「Tcl_AsyncDelete: async handler deleted by the wrong thread」が出る)。"""
        w, self.win = self.win, None
        if not w: return
        try:
            w["label"].image = None; w["label"].configure(image="")
            if w["open"]: w["root"].destroy()
        except Exception: pass
        w["img"] = w["label"] = w["root"] = None
        w.clear()
        import gc; gc.collect()

TIMER_BASE = 0x9200000

class Timer:
    """時計。+0x00 NOW(ミリ秒)、+0x04 SLEEP(書いた分待つ)。
    アラーム(sign_console.py が on_timer で呼ぶ): +0x08 ID に番号を書いてから、
      +0x0C AFTER に n を書く … n ミリ秒後に 1 回、+0x10 EVERY に n を書く … n ミリ秒ごと(n は 1 以上)、
      +0x14 CANCEL に番号を書く … 取り消す。同じ番号で書き直すと置き換わる。"""
    def __init__(self, display=None, virtual=False, base=TIMER_BASE):
        import time
        self.base, self.size, self.display, self.virtual = base, 0x20, display, virtual
        self.t0, self.fake = time.monotonic(), 0
        self.time = time
        self.alarm_id = 0
        self.alarms = {}                                       # 番号 → [時刻, 周期 または None]

    def now(self):
        return self.fake if self.virtual else int((self.time.monotonic() - self.t0) * 1000)

    def read(self, off):
        return self.now() if off == 0 else (self.alarm_id if off == 8 else None)

    def due(self):
        """時刻が来たアラームの番号を、早い順に。くり返しは次へ進める(遅れた分はまとめて 1 回)。"""
        now = self.now()
        ids = sorted((a[0], i) for i, a in self.alarms.items() if a[0] <= now)
        for _, i in ids:
            a = self.alarms[i]
            if a[1] is None: del self.alarms[i]
            else:
                while a[0] <= now: a[0] += a[1]
        return [i for _, i in ids]

    def write(self, off, v):
        if not isinstance(v, int) or isinstance(v, bool): return
        if off == 8: self.alarm_id = v; return
        if off in (0x0C, 0x10) and v >= (0 if off == 0x0C else 1):
            self.alarms[self.alarm_id] = [self.now() + v, v if off == 0x10 else None]; return
        if off == 0x14: self.alarms.pop(v, None); return
        if off != 4 or v < 0: return
        if self.virtual: self.fake += v; return
        end = self.time.monotonic() + v / 1000
        while (left := end - self.time.monotonic()) > 0:       # window が開いていれば、待つ間も更新を回す
            if self.display is not None: self.display.pump()
            self.time.sleep(min(left, 0.01))

INPUT_BASE = 0x9300000
KD, KU, MM, MD, MU, CLOSE = 1, 2, 3, 4, 5, 6

class Input:
    def __init__(self, timer=None, script="", base=INPUT_BASE):
        self.base, self.size, self.timer = base, 0x100 + 4 * 256, timer
        self.q, self.keys, self.mx, self.my, self.btn = [], set(), 0, 0, 0
        self.display = None                                  # main が Display を結ぶ(入力を読んだかを知らせる)
        self.script = sorted(self.parse_script(script), key=lambda e: e[0])

    @staticmethod
    def parse_script(text):
        out = []
        for item in filter(None, (t.strip() for t in text.split(","))):
            f = item.split(":")
            t, kind = int(f[0]), f[1]
            code = lambda x: int(x) if x.lstrip("-").isdigit() else ord(x)
            if kind in ("kd", "ku"): out.append((t, KD if kind == "kd" else KU, code(f[2]), 0, 0))
            elif kind == "mm": out.append((t, MM, 0, int(f[2]), int(f[3])))
            elif kind in ("md", "mu"): out.append((t, MD if kind == "md" else MU, int(f[2]), int(f[3]), int(f[4])))
            elif kind == "close": out.append((t, CLOSE, 0, 0, 0))
            else: raise ValueError(f"台本の種類が分かりません: {item}")
        return out

    def push(self, kind, code, x, y):
        if os.environ.get("SIGN_KEYDEBUG") and kind in (KD, KU, MD): print(f"入力装置が受け取った: 種類 {kind} 符号 {code}(行列の長さ {len(self.q) + 1})", file=sys.stderr)
        if kind == KD: self.keys.add(code)
        elif kind == KU: self.keys.discard(code)
        elif kind == MM: self.mx, self.my = x, y
        elif kind == MD: self.btn |= 1 << (code - 1); self.mx, self.my = x, y
        elif kind == MU: self.btn &= ~(1 << (code - 1)); self.mx, self.my = x, y
        self.q.append((kind, code, x, y))
        del self.q[:-256]

    def poll(self):                                          # 台本のうち時刻が来た物を行列へ
        if self.script and self.timer is not None:
            now = self.timer.now()
            while self.script and self.script[0][0] <= now: self.push(*self.script.pop(0)[1:])

    def read(self, off):
        self.poll()
        if self.display is not None and off == 0x00: self.display.reads_input = True   # 入力を読むプログラムは、終わるとき窓も閉じる
        head = self.q[0] if self.q else (0, 0, 0, 0)
        if off == 0x00:
            if self.q and os.environ.get("SIGN_KEYDEBUG"): print(f"プログラムが行列を見た: 長さ {len(self.q)}", file=sys.stderr)
            return len(self.q)
        if off in (0x04, 0x08, 0x0C, 0x10): return head[(off - 0x04) // 4]
        if off == 0x20: return self.mx
        if off == 0x24: return self.my
        if off == 0x28: return self.btn
        if off >= 0x100: return 1 if (off - 0x100) // 4 in self.keys else 0
        return None

    def write(self, off, v):
        self.poll()                                          # 時刻の来た台本を先に入れてから捨てる
        if off == 0x14 and self.q: self.q.pop(0)

def parse_spec(spec):
    """--display=ascii / --display=png:out.png / --display=png:f{n}.png:128x64 / --display=window:4:128x64"""
    w, h, parts = 64, 32, spec.split(":")
    if "x" in parts[-1] and parts[-1].replace("x", "").isdigit():
        w, h = map(int, parts.pop().split("x"))
    return Display(w, h, ":".join(parts))
