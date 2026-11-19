"""sign_audio.py — 音の装置(WAV ファイルを鳴らす・ピーという音を出す)。Windows と Linux(と macOS)で動く。
仕様に定めの無い拡張で、sign_gfx.py・sign_sys.py・sign_gpio.py・sign_bus.py の装置と同じ位置づけ。付けたときだけ使える(`--sound` か `--sound=バックエンド`)。

    SOUND_BASE = 0x9800000
    base + 0x00  PATH   RW  WAV ファイルの名前を入れたバッファの番地(1 語 = 1 バイト・4 バイト刻み。sign_sys.py と同じ形)
    base + 0x04  PLEN   RW  名前の長さ(バイト)
    base + 0x08  FREQ   RW  音の高さ(Hz、20〜20000。既定 440)
    base + 0x0C  MS     RW  音の長さ(ミリ秒、1〜10000。既定 200)
    base + 0x10  VOL    RW  音量 0〜100(既定 100)。TONE に効く(WAV ファイルは元の音量のまま)
    base + 0x14  GO     W   1 PLAY: PATH・PLEN の WAV ファイルを鳴らす。2 TONE: FREQ・MS・VOL の正弦波を鳴らす。3 STOP: 止める
                            鳴らし始めたらすぐ戻る(鳴り終わるのを待たない)。鳴っている途中で新しい音を始めると、前の音は止まって新しい音になる
    base + 0x18  RET    R   結果。0 なら成功、負なら -エラー番号
    base + 0x1C  BUSY   R   いま鳴っていれば 1、そうでなければ 0

  ファイル名は作業フォルダ(インタープリタを起動したフォルダ)の中だけ(sign_sys.py と同じ。`..`・絶対パス・外へのシンボリックリンクは 13)。
  エラー番号(Linux の errno に合わせる): 2 見つからない / 13 作業フォルダの外 / 5 再生に失敗 / 19 音を出す手段が無い(再生用のコマンドが無い・音の装置が無い)/ 22 引数がおかしい・WAV でない。
  WAV の確認は先頭の RIFF/WAVE の印だけ(中身の形式が再生側に合わない場合は、再生側の失敗として 5)。ファイルは 64 MiB まで。

バックエンド(--sound=名前。省くと auto):
    auto     winsound(Windows)→ 再生コマンド(Linux: paplay → pw-play → aplay → ffplay → play(sox)、macOS: afplay)→ pygame → simpleaudio の順で、最初に使えるもの。どれも無ければ fake
    winsound Windows の標準(追加の導入は要らない)
    pygame   pygame.mixer(pip install pygame)。Windows・Linux・macOS どれでも。「鳴っているか」を正確に聞ける。標準出力に出るあいさつ文は消してある
    simpleaudio  simpleaudio(pip install simpleaudio)。こちらも「鳴っているか」を聞ける(新しい Python 向けの配布が無いことがある。その場合は pygame を使う)
    command  Linux/macOS の再生用コマンド(上の順で探す)
    fake     鳴らさない(試験・音の無い環境用)。鳴らした内容を標準エラーに「[sound] play chime.wav」「[sound] tone 440Hz 200ms」と出す。fake:quiet なら出さない
"""
import math, os, shutil, struct, subprocess, sys, tempfile, time, wave, io
from sign_mem import DevMem

SOUND_BASE = 0x9800000
PATH, PLEN, FREQ, MS, VOL, GO, RET, BUSY = 0x00, 0x04, 0x08, 0x0C, 0x10, 0x14, 0x18, 0x1C
PLAY, TONE, STOP = 1, 2, 3
ENOENT, EIO, EACCES, ENODEV, EINVAL = 2, 5, 13, 19, 22
MAXPATH, MAXWAV, RATE = 1024, 64 << 20, 22050


def tone_wav(freq, ms, vol):
    """正弦波の WAV(16 ビット・モノラル・22050Hz)を作る。両端の 5 ミリ秒は音量を上げ下げして、プチッという音を避ける。"""
    n = max(1, RATE * ms // 1000)
    amp, ramp = 32767 * max(0, min(100, vol)) // 100 * 0.8, max(1, RATE * 5 // 1000)
    frames = bytearray()
    for i in range(n):
        env = min(1.0, i / ramp, (n - 1 - i) / ramp + 0.0)
        frames += struct.pack("<h", int(amp * env * math.sin(2 * math.pi * freq * i / RATE)))
    buf = io.BytesIO()
    with wave.open(buf, "wb") as w:
        w.setnchannels(1); w.setsampwidth(2); w.setframerate(RATE); w.writeframes(bytes(frames))
    return buf.getvalue()


def wav_seconds(data=None, path=None):
    try:
        with wave.open(io.BytesIO(data) if data is not None else path, "rb") as w: return w.getnframes() / float(w.getframerate())
    except Exception: return None


class FakeBackend:
    name = "fake"
    def __init__(self, quiet=False): self.quiet, self.log, self.end = quiet, [], 0.0
    def say(self, text):
        self.log.append(text)
        if not self.quiet: print("[sound] " + text, file=sys.stderr)
    def play_file(self, path, secs=None): self.say("play " + os.path.basename(path)); self.end = time.monotonic() + (secs or 0)
    def play_bytes(self, data, desc="tone"): self.say(desc); self.end = time.monotonic() + (wav_seconds(data) or 0)
    def stop(self): self.say("stop"); self.end = 0.0
    def busy(self): return time.monotonic() < self.end
    def close(self): self.end = 0.0


class WinsoundBackend:
    name = "winsound"
    def __init__(self):
        import winsound                                # Windows 以外では ImportError
        self.w, self.end = winsound, 0.0
    def play_file(self, path, secs=None):
        self.w.PlaySound(path, self.w.SND_FILENAME | self.w.SND_ASYNC); self.end = time.monotonic() + (secs or 0)
    def play_bytes(self, data, desc="tone"):
        self.w.PlaySound(data, self.w.SND_MEMORY | self.w.SND_ASYNC); self.end = time.monotonic() + (wav_seconds(data) or 0)
    def stop(self): self.w.PlaySound(None, self.w.SND_PURGE); self.end = 0.0
    def busy(self): return time.monotonic() < self.end           # winsound には「鳴っているか」を聞く手段が無いので、WAV の長さから見積もる
    def close(self): self.stop()


class CommandBackend:
    name = "command"
    CANDIDATES = [["paplay"], ["pw-play"], ["aplay", "-q"], ["ffplay", "-nodisp", "-autoexit", "-loglevel", "quiet"], ["play", "-q"], ["afplay"]]
    def __init__(self):
        self.cmd = next((c for c in self.CANDIDATES if shutil.which(c[0])), None)
        if self.cmd is None: raise ImportError("再生用のコマンド(paplay・pw-play・aplay・ffplay・play・afplay)が見つからない")
        self.proc, self.tmp = None, None
    def launch(self, path):                              # (呼ぶ前に stop() しておく)
        self.proc = subprocess.Popen(self.cmd + [path], stdin=subprocess.DEVNULL, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    def play_file(self, path, secs=None): self.stop(); self.launch(path)
    def play_bytes(self, data, desc="tone"):
        self.stop()
        fd, self.tmp = tempfile.mkstemp(suffix=".wav"); os.write(fd, data); os.close(fd)
        self.launch(self.tmp)
    def stop(self):
        if self.proc is not None and self.proc.poll() is None:
            self.proc.terminate()
            try: self.proc.wait(1)
            except Exception: self.proc.kill()
        self.proc = None
        if self.tmp:
            try: os.unlink(self.tmp)
            except OSError: pass
            self.tmp = None
    def busy(self): return self.proc is not None and self.proc.poll() is None
    def close(self): self.stop()


class PygameBackend:
    name = "pygame"
    def __init__(self):
        os.environ.setdefault("PYGAME_HIDE_SUPPORT_PROMPT", "1")        # import 時の「Hello from the pygame community」を標準出力に出さない
        import pygame
        self.pg, self.ch, self.snd = pygame, None, None
        if not pygame.mixer.get_init(): pygame.mixer.init()
    def play_file(self, path, secs=None): self.snd = self.pg.mixer.Sound(path); self.pg.mixer.stop(); self.ch = self.snd.play()
    def play_bytes(self, data, desc="tone"): self.snd = self.pg.mixer.Sound(file=io.BytesIO(data)); self.pg.mixer.stop(); self.ch = self.snd.play()
    def stop(self): self.pg.mixer.stop(); self.ch = None
    def busy(self): return bool(self.ch is not None and self.ch.get_busy())
    def close(self):
        try: self.pg.mixer.stop(); self.pg.mixer.quit()
        except Exception: pass


class SimpleaudioBackend:
    name = "simpleaudio"
    def __init__(self):
        import simpleaudio
        self.sa, self.po = simpleaudio, None
    def start(self, wo):
        self.stop(); self.po = wo.play()
    def play_file(self, path, secs=None): self.start(self.sa.WaveObject.from_wave_file(path))
    def play_bytes(self, data, desc="tone"): self.start(self.sa.WaveObject.from_wave_read(wave.open(io.BytesIO(data), "rb")))
    def stop(self):
        if self.po is not None: self.po.stop()
        self.po = None
    def busy(self): return bool(self.po is not None and self.po.is_playing())
    def close(self): self.stop()


def make_backend(spec):
    name, _, opt = (spec or "auto").partition(":")
    if name in ("", "auto"):
        for n in ("winsound", "command", "pygame", "simpleaudio"):
            try: return make_backend(n)
            except ImportError: pass
        print("注意: 音を出す手段(paplay・pw-play・aplay・ffplay・play・pygame・simpleaudio)が見つからないので、練習用の fake を使います(音は出ません)", file=sys.stderr)
        return FakeBackend()
    if name == "fake": return FakeBackend(quiet=(opt == "quiet"))
    if name == "winsound": return WinsoundBackend()
    if name == "command": return CommandBackend()
    if name == "pygame": return PygameBackend()
    if name == "simpleaudio": return SimpleaudioBackend()
    raise ValueError(f"知らない音のバックエンド: {spec}(auto / winsound / command / pygame / simpleaudio / fake)")


class Sound(DevMem):
    def __init__(self, spec=None, root=None, base=SOUND_BASE, backend=None):
        self.base, self.size = base, 0x20
        self.root = os.path.realpath(root or os.getcwd())
        self.be, self.warned = backend, False
        self.spec = spec
        self.reg, self.ret = {FREQ: 440, MS: 200, VOL: 100}, 0

    def backend(self):
        if self.be is None: self.be = make_backend(self.spec)
        return self.be

    def read(self, off):
        if off == RET: return self.ret
        if off == BUSY:
            try: return 1 if self.backend().busy() else 0
            except Exception: return 0
        return self.reg.get(off)

    def write(self, off, v):
        if not isinstance(v, int) or isinstance(v, bool): return
        if off in (PATH, PLEN, FREQ, MS, VOL): self.reg[off] = v
        elif off == GO: self.ret = self.go(v)

    def resolve(self):
        mem, p, n = self.memory(), self.reg.get(PATH), self.reg.get(PLEN, 0)
        if mem is None or not isinstance(p, int) or not 0 < n <= MAXPATH: return -EINVAL
        out = bytearray()
        for i in range(n):
            b = mem.get(p + 4 * i)
            if not isinstance(b, int) or isinstance(b, bool) or not 1 <= b <= 255: return -EINVAL
            out.append(b)
        try: name = out.decode("utf-8")
        except UnicodeDecodeError: return -EINVAL
        full = os.path.realpath(os.path.join(self.root, name))
        try:
            if os.path.commonpath([self.root, full]) != self.root: return -EACCES
        except ValueError: return -EACCES                  # Windows で別のドライブ
        if os.path.isabs(name) and os.path.realpath(name) != full: return -EACCES
        if not os.path.isfile(full): return -ENOENT
        return full

    def go(self, cmd):
        r = self.reg
        try:
            if cmd == STOP: self.backend().stop(); return 0
            if cmd == PLAY:
                full = self.resolve()
                if isinstance(full, int): return full
                if os.path.getsize(full) > MAXWAV: return -EINVAL
                with open(full, "rb") as f: head = f.read(12)
                if len(head) < 12 or head[:4] != b"RIFF" or head[8:12] != b"WAVE": return -EINVAL
                self.backend().play_file(full, wav_seconds(path=full)); return 0
            if cmd == TONE:
                f, ms, vol = r.get(FREQ, 440), r.get(MS, 200), r.get(VOL, 100)
                if not 20 <= f <= 20000 or not 1 <= ms <= 10000 or not 0 <= vol <= 100: return -EINVAL
                self.backend().play_bytes(tone_wav(f, ms, vol), f"tone {f}Hz {ms}ms"); return 0
            return -EINVAL
        except ImportError: return -ENODEV
        except OSError as e: return -(e.errno if isinstance(e.errno, int) and e.errno > 0 else EIO)
        except Exception as e:
            if not self.warned: self.warned = True; print(f"SOUND: {type(e).__name__}: {e}", file=sys.stderr)
            return -EIO

    def finish(self): self.release()
    def release(self):
        if self.be is not None:
            try: self.be.close()
            except Exception: pass
