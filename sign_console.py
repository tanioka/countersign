"""sign_console.py — ライブ・コーディングの小さなゲーム機(Fantasy Console)。

ゲームを動かしたまま、ソースを保存すると定義だけ入れ替わる。ゲームの状態は番地(メモリ)に置いてあるので、
定義を差し替えても止まらず、続きから動く。

ゲームの書き方(約束は 2 つだけ):
  tick : z ? …    1 こま分。ゲーム機が 1 秒に fps 回(既定 60)呼ぶ。-1 を返すと終わる
  init : z ? …    始めに 1 回(省いてもよい。--reinit なら保存のたびにも呼ぶ)
  ファイルの中の「定義」(`名前 : …`・export・演算子の定義)だけを読む。定義でない行(`ss 0 0` のような式)は
  保存のたびに繰り返したくないので読まない(初めの値は init に書く)。

  イベント(省いてよい。定義した物だけ呼ぶ。1 こまの頭に、たまった出来事を古い順に呼んでから tick):
    on_key : code ?             キーが押されたとき(1 回。押しっぱなしの自動繰り返しは呼ばない)。code は ASCII(a は 97)、左 28 右 29 上 30 下 31、スペース 32
    on_keyup : code ?           キーが離されたとき
    on_click : x y button ?     マウスのボタンが押されたとき(button は 1 左 2 中 3 右)。x y は画面の画素
    on_release : x y button ?   マウスのボタンが離されたとき
    on_mouse : x y ?            マウスが動いたとき
    on_timer : id ?             時計のアラームが鳴ったとき(アラームは timer 装置に書いて頼む。sign_gfx.py の Timer を見よ)
    on_close ?  : z ?           窓が閉じられたとき(定義が無ければ、そのまま終わる。-1 を返しても終わる)
  どれも -1 を返すと終わる。出来事を 1 つでも定義すると、ゲーム機が出来事の行列を読み切る(自分で drain するゲームには何も起きない)。
  上の物を何も定義しなければ、行列には触れない(従来どおり、ゲームが自分で読む)。

  画面・入力・時計の装置は sign_gfx.py と同じ(gfx 0x9100000、timer 0x9200000、inp 0x9300000)。待ちはゲーム機がするので、
  tick の中で sleep しない。

使い方:
  python3 sign_console.py game.sn                          窓(80x104 を 4 倍)で動かす
  python3 sign_console.py game.sn --display=window:5:80x104 --fps=30 --reinit
  python3 sign_console.py game.sn --sys[=作業フォルダ]       システムコール装置(sign_sys.py)を付ける
  python3 sign_console.py led.sn --display=null --gpio[=バックエンド]   GPIO 装置(sign_gpio.py。Raspberry Pi のピン)を付ける。窓が要らなければ --display=null
  python3 sign_console.py x.sn --db[=フォルダ]                        SQLite 装置(sign_db.py)を付ける
  python3 sign_console.py x.sn --net[=local|ホスト,…]                 ネットワーク装置(sign_net.py。TCP・UDP・TLS)を付ける。--net-proxy=URL|env、--net-ca=PEM も使える
  python3 sign_console.py x.sn --sound[=バックエンド]                 音の装置(sign_audio.py。WAV を鳴らす)を付ける
  python3 sign_console.py x.sn --i2c[=バックエンド] --spi[=バックエンド]   I2C・SPI 装置(sign_bus.py)を付ける
  python3 sign_console.py game.sn --display=png:f{n}.png:80x104 --timer=virtual --frames=100   窓なしの確認

直し方:
  保存すると次のこまから新しい定義になる。書き間違い(構文・実行時のエラー)は、場所を知らせて前の定義のまま続ける
  (tick の実行中に起きたら、そのこまで止めて、次に保存して直るまで待つ。状態は残る)。
  最初から壊れていたら、直して保存するまで待つ。
"""
import os, sys, time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sign_interp as si
import sign_gfx

DEF_KINDS = ("def", "export", "opdef")
CAUGHT = (SyntaxError, si.SignError, NotImplementedError, RecursionError, OSError)


class Console:
    def __init__(self, path, fps=60, reinit=False, out=sys.stderr):
        self.path, self.fps, self.reinit, self.out = path, fps, reinit, out
        self.env, self.mtime, self.paused, self.inited = None, None, False, False
        self.frames, self.loads, self.ignored, self.errors = 0, 0, 0, 0
        self.display = None
        self.timer = None
        self.inp = None
        self.down = set()                                           # いま押されているキー(自動繰り返しを見分ける)
        si.IMPORT_STACK.append(os.path.abspath(path))

    # --- 読み込み ---
    def say(self, msg):
        print(msg, file=self.out); self.out.flush()

    def report(self, e):
        self.errors += 1
        loc = getattr(e, "loc", None)
        if loc:
            f, ln, col = loc
            name = os.path.relpath(f) if f else "<入力>"
            self.say(f"エラー: {name}:{ln}:{col}: {e}")
            src = si.SRC_LINES.get(f)
            if src and 0 < ln <= len(src):
                self.say(f"  {ln:>4} | {src[ln - 1]}")
                self.say(f"       | {''.join(c if c == chr(9) else ' ' for c in src[ln - 1][:col - 1])}^")
        elif isinstance(e, RecursionError): self.say("エラー: 再帰が深すぎます")
        else: self.say(f"エラー: {e}")

    def load(self):
        """ソースを読み直して、定義だけで新しい環境を作る。失敗したら前の環境のまま False。"""
        mtime = self.mtime
        try:
            mtime = os.stat(self.path).st_mtime_ns
            with open(self.path, encoding="utf-8") as fh: src = fh.read()
            nodes = si.parse_source(src)
            defs = [n for n in nodes if n[0] in DEF_KINDS]
            env = si.Env()
            si.hoist_lambdas(defs, env)
            for n in defs: si.ev_place(n, env)
        except CAUGHT as e:
            self.mtime = mtime                                      # 同じ壊れた版を何度も読まない
            self.report(e)
            self.say("  → 前の定義のまま続けます。直して保存してください" if self.env else "  → 直して保存してください")
            return False
        self.env, self.mtime, self.paused = env, mtime, False
        self.ignored = len(nodes) - len(defs)
        self.loads += 1
        return True

    def changed(self):
        try: return os.stat(self.path).st_mtime_ns != self.mtime
        except OSError: return False

    def call(self, name):
        f = self.env.vars.get(name)
        if f is None: return None
        return si.finalize(si.run_with(f, [0]))

    # --- イベント ---
    HANDLERS = ("on_key", "on_keyup", "on_click", "on_release", "on_mouse", "on_close", "on_timer")

    def input_device(self):
        if self.inp is None:
            self.inp = next((d for d in si.DEVICES if isinstance(d, sign_gfx.Input)), None)
        return self.inp

    def fire(self, name, args):
        """1 つの出来事を渡す。続けてよければ True、終わりなら False、エラーなら None(paused)。"""
        f = self.env.vars.get(name)
        if f is None: return True
        try: v = si.finalize(si.run_with(f, args))
        except CAUGHT as e:
            self.report(e); self.say(f"  → {name} で止めます。直して保存すると続きから動きます"); self.paused = True
            return None
        return not (isinstance(v, int) and not isinstance(v, bool) and v == -1)

    def dispatch(self):
        """たまった出来事を古い順に、定義された関数へ渡す(入力の出来事、続けてアラーム)。続けてよければ True、終わりなら False(エラーなら paused)。"""
        env, inp = self.env, self.input_device()
        if not any(env.vars.get(h) is not None for h in self.HANDLERS): return True
        if inp is not None:
            inp.poll()
            while inp.q:
                kind, code, x, y = inp.q.pop(0)
                name, args = None, []
                if kind == sign_gfx.KD:
                    if code in self.down: continue                       # 押しっぱなしの繰り返し
                    self.down.add(code); name, args = "on_key", [code]
                elif kind == sign_gfx.KU: self.down.discard(code); name, args = "on_keyup", [code]
                elif kind == sign_gfx.MD: name, args = "on_click", [x, y, code]
                elif kind == sign_gfx.MU: name, args = "on_release", [x, y, code]
                elif kind == sign_gfx.MM: name, args = "on_mouse", [x, y]
                elif kind == sign_gfx.CLOSE:
                    if env.vars.get("on_close") is None: return False
                    name, args = "on_close", [0]
                if not name: continue
                r = self.fire(name, args)
                if r is None: return True
                if r is False: return False
        if env.vars.get("on_timer") is not None and hasattr(self.timer, "due"):
            for i in self.timer.due():
                r = self.fire("on_timer", [i])
                if r is None: return True
                if r is False: return False
        return True

    def after_load(self, first):
        """読み込めた直後の確かめと init。"""
        if first and self.ignored:
            self.say(f"注意: 定義でない行が {self.ignored} あります(読みません。初めの値は init に書きます)")
        if self.env.vars.get("tick") is None:
            self.say("エラー: tick が定義されていません(tick : z ? … を書いてください)"); self.paused = True; return
        if not self.inited or self.reinit:
            try: self.call("init")
            except CAUGHT as e:
                self.report(e); self.paused = True; return
            self.inited = True

    # --- 1 こま ---
    def frame(self):
        """1 こま進める。終わりなら False。"""
        if self.env is None or self.changed():
            first = self.env is None
            if self.load():
                if not first: self.say(f"再読み込み({self.loads} 回目)")
                self.after_load(first)
        if self.display is not None and self.display.win is not None and not self.display.win["open"]:
            return False
        if self.paused or self.env is None: return True
        if not self.dispatch(): return False
        if self.paused: return True
        v = None
        try: v = self.call("tick")
        except CAUGHT as e:
            self.report(e); self.say("  → このこまで止めます。直して保存すると続きから動きます"); self.paused = True
        self.frames += 1
        return not (isinstance(v, int) and not isinstance(v, bool) and v == -1)

    def run(self, max_frames=None):
        period = 1000 // max(1, self.fps)
        while max_frames is None or self.frames < max_frames:
            t0 = time.monotonic()
            if not self.frame(): break
            if max_frames is not None and (self.paused or self.env is None): break      # 台本つきの確認では待たない
            left = period if getattr(self.timer, "virtual", False) else period - int((time.monotonic() - t0) * 1000)   # 試験用の仮想時計は、実際にかかった時間を引かない
            if self.timer is not None: self.timer.write(4, max(left, 1))           # 窓があれば待つ間も更新を回す
            elif left > 0: time.sleep(left / 1000)

    def close(self):
        for d in si.DEVICES:
            if hasattr(d, "release"): d.release()


def setup(display_spec, virtual, script, sys_root=None, gpio=None, i2c=None, spi=None, sound=None, net=None, net_ca=None, net_proxy=None, db=None):
    """sign_interp.py の起動と同じ装置を付ける。"""
    del si.DEVICES[:]
    disp = sign_gfx.parse_spec(display_spec)
    si.DEVICES.append(disp)
    timer = sign_gfx.Timer(disp, virtual)
    inp = sign_gfx.Input(timer, script)
    si.DEVICES += [timer, inp]
    disp.on_event = inp.push
    if sys_root is not None:                                        # システムコール装置(sign_sys.py)。"" なら今のフォルダ
        import sign_sys
        si.DEVICES.append(si._dev(lambda: sign_sys.Sys(sys_root or None)))
    if gpio is not None:                                            # GPIO 装置(sign_gpio.py)。"" なら auto
        import sign_gpio
        si.DEVICES.append(si._dev(lambda: sign_gpio.Gpio(gpio or None)))
    if db is not None:                                              # SQLite 装置(sign_db.py)
        import sign_db
        si.DEVICES.append(si._dev(lambda: sign_db.Db(db or None)))
    if net is not None:                                             # ネットワーク装置(sign_net.py)
        import sign_net
        si.DEVICES.append(si._dev(lambda: sign_net.Net(net or None, ca=net_ca, proxy=net_proxy)))
    if sound is not None:                                           # 音の装置(sign_audio.py)
        import sign_audio
        si.DEVICES.append(si._dev(lambda: sign_audio.Sound(sound or None)))
    for spec, cls in ((i2c, "I2c"), (spi, "Spi")):                  # I2C・SPI 装置(sign_bus.py)
        if spec is not None:
            import sign_bus
            si.DEVICES.append(si._dev(lambda: getattr(sign_bus, cls)(spec or None)))
    return disp, timer, inp


def main(argv):
    opts = {"display": "window:4:80x104", "fps": 60, "frames": None, "input": "", "timer": False, "reinit": False, "strict": False, "sys": None, "gpio": None, "i2c": None, "spi": None, "sound": None, "net": None, "net_ca": None, "net_proxy": None, "db": None}
    paths = []
    for a in argv:
        if a.startswith("--display="): opts["display"] = a[10:]
        elif a.startswith("--fps="): opts["fps"] = int(a[6:])
        elif a.startswith("--frames="): opts["frames"] = int(a[9:])
        elif a.startswith("--input="): opts["input"] = a[8:]
        elif a == "--timer=virtual": opts["timer"] = True
        elif a == "--reinit": opts["reinit"] = True
        elif a == "--strict": opts["strict"] = True
        elif a == "--sys" or a.startswith("--sys="): opts["sys"] = a[6:]
        elif a == "--gpio" or a.startswith("--gpio="): opts["gpio"] = a[7:]
        elif a == "--net" or a.startswith("--net="): opts["net"] = a[6:]
        elif a == "--db" or a.startswith("--db="): opts["db"] = a[5:]
        elif a.startswith("--net-ca="): opts["net_ca"] = a[9:]
        elif a.startswith("--net-proxy="): opts["net_proxy"] = a[12:]
        elif a == "--sound" or a.startswith("--sound="): opts["sound"] = a[8:]
        elif a == "--i2c" or a.startswith("--i2c="): opts["i2c"] = a[6:]
        elif a == "--spi" or a.startswith("--spi="): opts["spi"] = a[6:]
        elif a.startswith("--"): print(f"知らない指定: {a}", file=sys.stderr); return 2
        else: paths.append(a)
    if len(paths) != 1:
        print(__doc__, file=sys.stderr); return 2
    si.STRICT_GATES = opts["strict"]
    status = []

    def go():
        try:
            disp, timer, _ = setup(opts["display"], opts["timer"], opts["input"], opts["sys"], opts.get("gpio"), opts.get("i2c"), opts.get("spi"), opts.get("sound"), opts.get("net"), opts.get("net_ca"), opts.get("net_proxy"), opts.get("db"))
        except SystemExit:                                          # 装置を用意できなかった(理由は知らせ済み)。終了コードで伝える
            status.append(1); return
        con = Console(paths[0], opts["fps"], opts["reinit"])
        con.display, con.timer = disp, timer
        try: con.run(opts["frames"])
        except KeyboardInterrupt: pass
        finally:
            if con.errors and opts["frames"] is not None: status.append(1)
            con.close()

    si.run_with_big_stack(go)
    for kind, msg in si.WARNINGS: print(f"警告: {kind}: {msg}", file=sys.stderr)
    return status[0] if status else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
