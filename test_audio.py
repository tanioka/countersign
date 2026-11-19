#!/usr/bin/env python3
"""音の装置(sign_audio.py)の試験。実際には鳴らさない: fake、偽の winsound(Windows の代役)、偽の再生コマンド(Linux の代役)で確かめる。python test_audio.py"""
import io, os, subprocess, sys, tempfile, time, wave
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import sign_audio as A

bad = 0
def check(name, got, want):
    global bad
    ok = got == want; bad += not ok
    print(("ok  " if ok else "NG  ") + name + ("" if ok else f"\n    得た: {got!r}\n    期待: {want!r}"))

ROOT = tempfile.mkdtemp()
import shutil
shutil.copy(os.path.join(HERE, "chime.wav"), os.path.join(ROOT, "chime.wav"))
open(os.path.join(ROOT, "notwav.wav"), "wb").write(b"hello world, not a wav")
os.mkdir(os.path.join(ROOT, "sub")); shutil.copy(os.path.join(HERE, "chime.wav"), os.path.join(ROOT, "sub", "c2.wav"))
NAME = 0x600000
def dev(be=None, root=ROOT):
    d = A.Sound(backend=be or A.FakeBackend(quiet=True), root=root); d.mem = {}; return d
def put(d, s, buf=NAME):
    for i, b in enumerate(s.encode("utf-8")): d.mem[buf + 4 * i] = b
    d.write(A.PATH, buf); d.write(A.PLEN, len(s.encode("utf-8")))
def go(d, cmd): d.write(A.GO, cmd); return d.read(A.RET)

# --- 音(TONE) ---
w = A.tone_wav(440, 100, 100)
f = wave.open(io.BytesIO(w))
check("TONE の WAV: 22050Hz・16 ビット・モノラル・100ms", (f.getframerate(), f.getsampwidth(), f.getnchannels(), f.getnframes()), (22050, 2, 1, 2205))
import struct
pcm = struct.unpack("<%dh" % f.getnframes(), f.readframes(f.getnframes()))
check("TONE: 両端は静か(プチッを避ける)で、真ん中は大きい", (abs(pcm[0]) < 50, abs(pcm[-1]) < 500, max(pcm) > 20000), (True, True, True))
half = A.tone_wav(440, 100, 50); pf = struct.unpack("<%dh" % 2205, wave.open(io.BytesIO(half)).readframes(2205))
check("TONE: 音量 50 は振幅が約半分", 0.45 < max(pf) / max(pcm) < 0.55, True)
check("TONE: 音量 0 は無音", set(struct.unpack("<%dh" % 2205, wave.open(io.BytesIO(A.tone_wav(440, 100, 0))).readframes(2205))), {0})
be = A.FakeBackend(quiet=True); d = dev(be)
check("TONE: 既定の 440Hz・200ms で鳴る", (go(d, 2), be.log), (0, ["tone 440Hz 200ms"]))
d.write(A.FREQ, 880); d.write(A.MS, 50); d.write(A.VOL, 30)
check("TONE: 高さ・長さを変えられる", (go(d, 2), be.log[-1]), (0, "tone 880Hz 50ms"))
for k, v in ((A.FREQ, 19), (A.FREQ, 20001), (A.MS, 0), (A.MS, 10001), (A.VOL, 101), (A.VOL, -1)):
    d2 = dev(); d2.write(k, v); r = go(d2, 2)
    check(f"TONE: 範囲外(レジスタ {k:#x} = {v})は -22", r, -22)
d.write(A.FREQ, True); d.write(A.MS, "5")
check("整数でない書き込みは捨てる", (d.read(A.FREQ), d.read(A.MS)), (880, 50))
check("BUSY: 鳴っている間は 1、STOP で 0", (A.Sound(backend=A.FakeBackend(quiet=True)).read(A.BUSY), ), (0,))
be = A.FakeBackend(quiet=True); d = dev(be); d.write(A.MS, 300); go(d, 2)
check("BUSY: TONE の直後は 1", d.read(A.BUSY), 1)
check("STOP", (go(d, 3), d.read(A.BUSY), be.log[-1]), (0, 0, "stop"))
check("知らない命令は -22", go(d, 9), -22)

# --- WAV ファイル(PLAY) ---
be = A.FakeBackend(quiet=True); d = dev(be); put(d, "chime.wav")
check("PLAY: chime.wav を鳴らす", (go(d, 1), be.log), (0, ["play chime.wav"]))
check("PLAY: 鳴っている(WAV の長さ 0.6 秒から見積もる)", d.read(A.BUSY), 1)
put(d, "sub/c2.wav"); check("PLAY: 下のフォルダの中", (go(d, 1), be.log[-1]), (0, "play c2.wav"))
put(d, "nothing.wav"); check("PLAY: 無いファイルは -2", go(d, 1), -2)
put(d, "notwav.wav"); check("PLAY: WAV でない(RIFF/WAVE の印が無い)は -22", go(d, 1), -22)
put(d, "../chime.wav"); check("PLAY: 作業フォルダの外(..)は -13", go(d, 1), -13)
put(d, os.path.join(ROOT, "chime.wav")); r1 = go(d, 1)
put(d, "/etc/passwd"); r2 = go(d, 1)
check("PLAY: 絶対パス: 作業フォルダの中なら通り、外は -13", (r1, r2), (0, -13))
os.symlink("/etc/hostname", os.path.join(ROOT, "link.wav")) if os.name == "posix" and os.path.exists("/etc/hostname") else None
if os.path.islink(os.path.join(ROOT, "link.wav")):
    put(d, "link.wav"); check("PLAY: 外へのシンボリックリンクは -13", go(d, 1), -13)
put(d, ""); check("PLAY: 名前の長さ 0 は -22", go(d, 1), -22)
d3 = dev(); d3.write(A.PATH, 0x700000); d3.write(A.PLEN, 3); check("PLAY: 名前のバッファが未書き込みは -22", go(d3, 1), -22)
put(d, "x" * 2000); check("PLAY: 名前が長すぎる(1024 超)は -22", go(d, 1), -22)
put(d, "日本語.wav"); check("PLAY: 日本語の名前(UTF-8)も見つかれば鳴る/無ければ -2", go(d, 1), -2)
shutil.copy(os.path.join(HERE, "chime.wav"), os.path.join(ROOT, "日本語.wav")); check("PLAY: 日本語の名前のファイル", (go(d, 1), be.log[-1]), (0, "play 日本語.wav"))

# --- Windows の代役(偽の winsound) ---
class FakeWinsound:
    SND_FILENAME, SND_ASYNC, SND_MEMORY, SND_PURGE = 0x20000, 1, 4, 0x40
    calls = []
    @classmethod
    def PlaySound(cls, a, flags): cls.calls.append((a if isinstance(a, (str, type(None))) else "<%d バイト>" % len(a), flags))
sys.modules["winsound"] = FakeWinsound
wb = A.make_backend("winsound"); d = dev(wb); put(d, "chime.wav")
go(d, 1); go(d, 2); go(d, 3)
check("Windows(winsound): ファイル・メモリ・止める の呼び方", [(c[0] if c[0] is None or c[0].startswith("<") else os.path.basename(c[0]), c[1]) for c in FakeWinsound.calls],
      [("chime.wav", 0x20001), ("<%d バイト>" % len(A.tone_wav(440, 200, 100)), 5), (None, 0x40)])
check("Windows: 自動(auto)選びは winsound", A.make_backend("auto").name, "winsound")
del sys.modules["winsound"]; sys.modules["winsound"] = None            # import できない状態(Linux)

# --- Linux の代役(偽の再生コマンド paplay: 渡されたファイルの名前と大きさを記録する) ---
if os.name == "posix":
    bindir = tempfile.mkdtemp(); logf = os.path.join(bindir, "log")
    script = os.path.join(bindir, "paplay")
    open(script, "w").write(f'#!/bin/sh\necho "$1 $(wc -c < "$1")" >> {logf}\nsleep ${{FAKE_SLEEP:-0}}\n')
    os.chmod(script, 0o755)
    old = os.environ["PATH"]; os.environ["PATH"] = bindir + os.pathsep + "/usr/bin" + os.pathsep + "/bin"
    try:
        cb = A.make_backend("command")
        check("Linux(command): 見つかったコマンドは paplay", cb.cmd, ["paplay"])
        check("Linux: 自動(auto)選びは command(winsound が無いので)", A.make_backend("auto").name, "command")
        d = dev(cb); put(d, "chime.wav"); r = go(d, 1)
        for _ in range(50):
            if os.path.exists(logf) and open(logf).read().strip(): break
            time.sleep(0.05)
        line = open(logf).read().split()
        check("Linux: PLAY で paplay にファイルを渡す", (r, os.path.basename(line[0]), int(line[1]) == os.path.getsize(os.path.join(ROOT, "chime.wav"))), (0, "chime.wav", True))
        os.unlink(logf); d.write(A.MS, 100); r = go(d, 2)
        for _ in range(50):
            if os.path.exists(logf) and open(logf).read().strip(): break
            time.sleep(0.05)
        line = open(logf).read().split()
        check("Linux: TONE は一時の WAV を作って渡す(サイズは 44 + 2×2205 バイト)", (r, line[0].endswith(".wav"), int(line[1])), (0, True, 44 + 2 * 2205))
        os.environ["FAKE_SLEEP"] = "5"; go(d, 2)
        time.sleep(0.2)
        check("Linux: コマンドが動いている間は BUSY=1、STOP で止まって 0", (d.read(A.BUSY), go(d, 3), d.read(A.BUSY)), (1, 0, 0))
        d.release()
        check("Linux: release でコマンドを止める", cb.proc, None)
        del os.environ["FAKE_SLEEP"]
        os.environ["PATH"] = os.path.join(bindir, "nonexistent")
        try: A.make_backend("command"); ok = False
        except ImportError: ok = True
        dn = A.Sound(spec="command", root=ROOT); dn.mem = {}; put(dn, "chime.wav")
        check("Linux: 再生コマンドが無いと ImportError、装置は -19", (ok, go(dn, 1)), (True, -19))
        check("Linux: auto でコマンドも無ければ fake", A.make_backend("auto").name, "fake")
    finally:
        os.environ["PATH"] = old

# --- pygame.mixer の代役 ---
class FakeChannel:
    def __init__(self, owner): self.owner = owner
    def get_busy(self): return self.owner.playing
class FakeSnd:
    def __init__(self, path=None, file=None):
        self.src = path if path is not None else "<%d バイト>" % len(file.read())
        FakeMixer.made.append(self.src)
    def play(self): FakeMixer.playing = True; FakeMixer.plays += 1; return FakeChannel(FakeMixer)
class FakeMixer:
    made, plays, playing, inited, quit_called = [], 0, False, False, False
    Sound = FakeSnd
    @staticmethod
    def get_init(): return FakeMixer.inited
    @staticmethod
    def init(): FakeMixer.inited = True
    @staticmethod
    def stop(): FakeMixer.playing = False
    @staticmethod
    def quit(): FakeMixer.quit_called = True
class FakePygame: mixer = FakeMixer
sys.modules["pygame"] = FakePygame
pb = A.make_backend("pygame"); d = dev(pb); put(d, "chime.wav")
check("pygame: 初期化と PLAY(Sound にファイルを渡して鳴らす)", (go(d, 1), FakeMixer.inited, os.path.basename(FakeMixer.made[-1]), d.read(A.BUSY)), (0, True, "chime.wav", 1))
check("pygame: TONE はメモリの WAV を渡す", (go(d, 2), FakeMixer.made[-1] == "<%d バイト>" % len(A.tone_wav(440, 200, 100))), (0, True))
FakeMixer.playing = False
check("pygame: 鳴り終わると BUSY=0(正確に聞ける)", d.read(A.BUSY), 0)
go(d, 2); check("pygame: STOP", (go(d, 3), d.read(A.BUSY)), (0, 0))
d.release(); check("pygame: release で mixer を閉じる", FakeMixer.quit_called, True)
check("pygame: 標準出力のあいさつ文を消す設定", os.environ.get("PYGAME_HIDE_SUPPORT_PROMPT"), "1")
sys.modules["pygame"] = None
try: A.make_backend("pygame"); ok = False
except ImportError: ok = True
dn = A.Sound(spec="pygame", root=ROOT); dn.mem = {}; put(dn, "chime.wav")
check("pygame が無ければ ImportError、装置は -19", (ok, go(dn, 1)), (True, -19))

# --- simpleaudio の代役 ---
class FakePlay:
    def __init__(self): self.on, self.stopped = True, False
    def is_playing(self): return self.on
    def stop(self): self.on, self.stopped = False, True
class FakeWave:
    def __init__(self, src): self.src = src
    def play(self): p = FakePlay(); FakeSA.plays.append((self.src, p)); return p
class FakeWaveObject:
    @staticmethod
    def from_wave_file(path): return FakeWave(os.path.basename(path))
    @staticmethod
    def from_wave_read(w): return FakeWave("<%d フレーム>" % w.getnframes())
class FakeSA: WaveObject, plays = FakeWaveObject, []
sys.modules["simpleaudio"] = FakeSA
sb = A.make_backend("simpleaudio"); d = dev(sb); put(d, "chime.wav")
check("simpleaudio: PLAY・TONE の呼び方", (go(d, 1), go(d, 2), [x[0] for x in FakeSA.plays]), (0, 0, ["chime.wav", "<4410 フレーム>"]))
check("simpleaudio: 新しい音を始めると前の音は止まる", (FakeSA.plays[0][1].stopped, d.read(A.BUSY)), (True, 1))
FakeSA.plays[1][1].on = False; check("simpleaudio: 鳴り終わると BUSY=0", d.read(A.BUSY), 0)
go(d, 1); check("simpleaudio: STOP", (go(d, 3), FakeSA.plays[-1][1].stopped, d.read(A.BUSY)), (0, True, 0))
sys.modules["simpleaudio"] = None

try: A.make_backend("nanika"); ok = False
except ValueError: ok = True
check("知らないバックエンド名はエラー", ok, True)

# --- Sign から ---
def sign(*flags):
    r = subprocess.run([sys.executable, os.path.join(HERE, "sign.py"), os.path.join(HERE, "sound_demo.sn"), *flags], capture_output=True, timeout=60, cwd=HERE)
    return r.stderr.decode().splitlines()
check("sound_demo.sn: chime.wav のあと ド・ミ・ソ・ド", sign("--sound=fake"), ["[sound] play chime.wav", "[sound] tone 262Hz 300ms", "[sound] tone 330Hz 300ms", "[sound] tone 392Hz 300ms", "[sound] tone 523Hz 600ms"])
print("\n" + ("全部通った" if not bad else f"{bad} 件 食い違い")); sys.exit(1 if bad else 0)
