"""sign_sys.py — システムコール装置(OS の機能を番地で呼ぶ)。標準入出力・時刻・ファイルの読み書き(作業フォルダの中だけ)。
仕様に定めの無い拡張で、sign_gfx.py の装置と同じ位置づけ。付けたときだけ使える(`--sys` か `--sys=DIR`)。

使い方(Sign から): 番号と引数の番地に書き、GO に何か書くと実行され、RET を読むと結果が取れる。
    SYS_BASE = 0x9400000
    base + 0x00  NR    W   システムコールの番号
    base + 0x04  ARG0  W   引数 0
    base + 0x08  ARG1  W   引数 1
    base + 0x0C  ARG2  W   引数 2
    base + 0x14  GO    W   何か書くと実行
    base + 0x18  RET   R   結果。0 以上なら成功の値、負なら -エラー番号(下の表)
  バッファ(buf)は、インタープリタのメモリの番地から 1 語 = 1 バイト(0〜255)・4 バイト刻みで並べる(`cat : i ? @(BUF + (i*4))` の形)。
  パスは「バッファ + 長さ」で渡す(UTF-8 のバイトの並び)。

  番号  名前      引数                         結果
   1   READ      fd, buf, n                   読んだバイト数(0 = 終わり)。fd 0 = 標準入力(ある分だけ。待つのは 1 バイト以上)
   2   WRITE     fd, buf, n                   書いたバイト数。fd 1 = 標準出力、2 = 標準エラー
   3   OPEN      path_buf, path_len, mode     fd(3 以上)。mode 0 = 読む、1 = 書く(作り直す)、2 = 足して書く
   4   CLOSE     fd                           0
   5   TIME_S    —                            1970 年からの秒
   6   TIME_MS   —                            1970 年からのミリ秒
   7   SIZE      path_buf, path_len           ファイルの大きさ(バイト)

  エラー番号(Linux の errno に合わせる): 2 ENOENT 見つからない / 5 EIO / 9 EBADF 開いていない fd / 13 EACCES 作業フォルダの外・許されない /
  22 EINVAL 引数がおかしい / 24 EMFILE 開きすぎ(同時に 16 まで)/ 38 ENOSYS 知らない番号。
  作業フォルダ(root)の外へ出る(`..`・絶対パス・シンボリックリンクの先)は 13。1 回の入出力は 1 MiB まで、パスは 1024 バイトまで。
"""
import os, sys, time
from sign_mem import DevMem

SYS_BASE = 0x9400000
NR, A0, A1, A2, GO, RET = 0x00, 0x04, 0x08, 0x0C, 0x14, 0x18
ENOENT, EIO, EBADF, EACCES, EINVAL, EMFILE, ENOSYS = 2, 5, 9, 13, 22, 24, 38
MAXIO, MAXPATH, MAXFD = 1 << 20, 1024, 16


class Sys(DevMem):
    def __init__(self, root=None, base=SYS_BASE):
        self.base, self.size = base, 0x20
        self.root = os.path.realpath(root or os.getcwd())
        self.reg, self.files, self.ret = {}, {}, 0
        self.next_fd = 3

    # --- 装置の口 ---
    def read(self, off):
        return self.ret if off == RET else self.reg.get(off)

    def write(self, off, v):
        if not isinstance(v, int) or isinstance(v, bool): return
        if off in (NR, A0, A1, A2): self.reg[off] = v
        elif off == GO: self.ret = self.call()

    def finish(self): self.release()

    def release(self):
        for f in self.files.values():
            try: f.close()
            except OSError: pass
        self.files.clear()

    # --- 部品 ---
    def get_bytes(self, buf, n):
        mem = self.memory()
        if mem is None or n < 0 or n > MAXIO: return None
        out = bytearray()
        for i in range(n):
            v = mem.get(buf + 4 * i)
            if not isinstance(v, int) or isinstance(v, bool) or not 0 <= v <= 255: return None
            out.append(v)
        return bytes(out)

    def resolve(self, pbuf, plen):
        """パスを作業フォルダの中の本物のパスにする。外なら EACCES、おかしければ EINVAL(戻りは (パス, 0) か (None, -errno))。"""
        if not (0 < plen <= MAXPATH): return None, -EINVAL
        raw = self.get_bytes(pbuf, plen)
        if raw is None or b"\0" in raw: return None, -EINVAL
        try: rel = raw.decode("utf-8")
        except UnicodeDecodeError: return None, -EINVAL
        path = os.path.realpath(os.path.join(self.root, rel))          # 絶対パスは join で root を無視するので、下の検査で落ちる。シンボリックリンクはここで解決される
        try: inside = os.path.commonpath([self.root, path]) == self.root
        except ValueError: inside = False
        if not inside: return None, -EACCES
        return path, 0

    # --- 実行 ---
    def call(self):
        nr, a0, a1, a2 = (self.reg.get(k) for k in (NR, A0, A1, A2))
        ints = lambda *xs: all(isinstance(x, int) and not isinstance(x, bool) for x in xs)
        try:
            if nr == 5: return int(time.time())
            if nr == 6: return int(time.time() * 1000)
            if nr == 1:                                                    # READ
                if not ints(a0, a1, a2) or a2 < 0 or a2 > MAXIO: return -EINVAL
                if a0 == 0: data = sys.stdin.buffer.read1(a2) if a2 else b""
                elif a0 in self.files: data = self.files[a0].read(a2)
                else: return -EBADF
                if not self.put_bytes(a1, data): return -EINVAL
                return len(data)
            if nr == 2:                                                    # WRITE
                if not ints(a0, a1, a2) or a2 < 0 or a2 > MAXIO: return -EINVAL
                data = self.get_bytes(a1, a2)
                if data is None: return -EINVAL
                if a0 in (1, 2):
                    sys.stdout.flush(); sys.stderr.flush()
                    out = sys.stdout if a0 == 1 else sys.stderr
                    out.buffer.write(data); out.buffer.flush()
                elif a0 in self.files: self.files[a0].write(data)
                else: return -EBADF
                return len(data)
            if nr == 3:                                                    # OPEN
                if not ints(a0, a1, a2) or a2 not in (0, 1, 2): return -EINVAL
                if len(self.files) >= MAXFD: return -EMFILE
                path, err = self.resolve(a0, a1)
                if err: return err
                f = open(path, {0: "rb", 1: "wb", 2: "ab"}[a2])
                fd = self.next_fd; self.next_fd += 1; self.files[fd] = f
                return fd
            if nr == 4:                                                    # CLOSE
                if not ints(a0) or a0 not in self.files: return -EBADF
                self.files.pop(a0).close(); return 0
            if nr == 7:                                                    # SIZE
                if not ints(a0, a1): return -EINVAL
                path, err = self.resolve(a0, a1)
                if err: return err
                return os.path.getsize(path)
        except FileNotFoundError: return -ENOENT
        except PermissionError: return -EACCES
        except IsADirectoryError: return -EINVAL
        except OSError: return -EIO
        return -ENOSYS
