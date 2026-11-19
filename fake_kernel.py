"""fake_kernel.py — --real-dev の生成物を試すための疑似カーネル(エミュレータの svc の相手)。
openat・close・ioctl・read・write・nanosleep・clock_gettime だけを、Linux の I2C(/dev/i2c-N)と GPIO v2(/dev/gpiochip0)の流儀で模す。
I2C の相手は sign_bus の部品(FakeI2c・FakeAht25)をそのまま使うので、処理系の --i2c=fake… と同じ答えになるはず。
これは私の理解した Linux の仕様のモデルで、本物のカーネルではない(実機では未実行)。"""
import os, struct, sys, socket, select, threading, random, errno as _errno
sys.path.insert(0, __import__("os").path.dirname(__import__("os").path.abspath(__file__)))
M64 = (1 << 64) - 1
ENOENT, EIO, ENXIO, EINVAL, ENOTTY, EPERM = 2, 5, 6, 22, 25, 1
I2C_SLAVE, I2C_RDWR = 0x0703, 0x0707
GET_LINE, GET_VALUES, SET_VALUES = 0xC250B407, 0xC010B40E, 0xC010B40F


class ExecDone(Exception): pass


class Kernel:
    def __init__(self, i2c=None, stdin=b"", spi=None):
        self.spi = spi
        self.i2c, self.fds, self.next_fd = i2c, {}, 3
        self.stdin = list(stdin)
        self.sleeps, self.clock = [], 1_000_000       # clock: ミリ秒(nanosleep で進む)
        self.levels, self.inputs, self.modes, self.log = {}, {}, {}, []      # GPIO: 出力の値・入力の電圧(試験が入れる)・向き(フラグ)・変化の列
        self.syscalls, self.maps, self.map_fail = [], [], False
        self.i2c_buses = {1}                                           # /dev/i2c-N があるバス

    # ---- スレッド(協調。ブロックする呼び出し clone・futex・sched_yield でだけ切り替わる。同時には 1 つしか走らない) ----
    # self.sched_seed を整数にすると、切り替え先を乱数で選ぶ(いろいろな順番を試す)。None は先に入れた物から。
    def ctx_of(self, cpu):
        c = getattr(cpu, "_ctx", None)
        if c is None:
            if not hasattr(self, "ctxs"): self.ctxs = []; self.stopped = False; self.rng = random.Random(getattr(self, "sched_seed", None)) if getattr(self, "sched_seed", None) is not None else None; self.thread_error = None
            c = cpu._ctx = dict(cpu=cpu, ev=threading.Event(), state="run", addr=None, tid=1000 + len(self.ctxs))
            self.ctxs.append(c)
            cpu.exit_group = self.exit_group
        return c

    def preempt(self, cpu, every=23):
        """cpu(主スレッド)から始めて、every 命令ごと(乱数の幅つき)にスレッドを強制的に切り替える。子は設定を受け継ぐ。"""
        ctx = self.ctx_of(cpu)
        rng = self.rng if self.rng is not None else random.Random(0)
        cpu.tick_every = every
        def hook(c):
            c.tick_every = max(3, every + (rng.randrange(-every // 2, every // 2 + 1)))
            self.switch(self.ctx_of(c), "ready")
        cpu.tick_hook = hook

    def exit_group(self):
        self.stopped = True
        for c in getattr(self, "ctxs", []): c["ev"].set()

    def switch(self, me, state):
        """me を state('ready' = 譲る / 'wait' = futex で眠る / 'dead')にして、ほかの走れる物へ渡す。戻ったら続きを走る。"""
        me["state"] = state
        ready = [c for c in self.ctxs if c["state"] == "ready" and (c is not me)]
        if state == "ready": ready = [c for c in self.ctxs if c["state"] == "ready"]
        if not ready:
            if state == "dead" or state == "wait":
                if not any(c["state"] == "run" for c in self.ctxs if c is not me):
                    self.deadlock = True; self.stopped = True; self.exit_group()
                    if state == "wait": raise RuntimeError("デッドロック(全部のスレッドが futex で眠った)")
                return
            me["state"] = "run"; return
        nxt = self.rng.choice(ready) if self.rng is not None else ready[0]
        if nxt is me: me["state"] = "run"; return
        nxt["state"] = "run"; type(me["cpu"]).epoch[0] += 1
        if state == "ready": me["state"] = "ready"
        nxt["ev"].set()
        if state == "dead": return
        me["ev"].wait(); me["ev"].clear()
        if self.stopped: raise SystemExit
        me["state"] = "run"

    def clone_thread(self, cpu):
        me = self.ctx_of(cpu); flags = cpu.r["x0"]
        child = object.__new__(type(cpu)); child.__dict__.update(cpu.__dict__)
        child.r = dict(cpu.r); child.nzcv = list(cpu.nzcv); child.steps = 0; child.exit = None
        child.r["x0"] = 0; child.r["sp"] = cpu.r["x1"]
        child.tpidr = cpu.r["x3"] if flags & 0x80000 else getattr(cpu, "tpidr", 0)
        if hasattr(child, "_ctx"): del child._ctx
        c = self.ctx_of(child); c["state"] = "ready"; pc = cpu.pc
        def body():
            c["ev"].wait(); c["ev"].clear()
            if self.stopped: return
            try: child.run("", limit=getattr(self, "thread_limit", 5_000_000), pc0=pc)
            except SystemExit: return
            except BaseException as e: self.thread_error = e; self.stopped = True; self.exit_group(); return
            self.switch(c, "dead")
        t = threading.Thread(target=body, daemon=True); t.start()
        self.threads_made = getattr(self, "threads_made", 0) + 1
        if self.rng is not None and self.rng.random() < 0.5: self.switch(me, "ready")
        return c["tid"]

    def futex(self, cpu):
        x = lambda i: cpu.r["x%d" % i]; me = self.ctx_of(cpu); op = x(1) & 0x7F; ad = x(0)
        self.futexes = getattr(self, "futexes", []) + [(op, ad)]
        if op == 0:
            if cpu.load(ad, 4) != (x(2) & 0xFFFFFFFF): return -11
            me["addr"] = ad; self.switch(me, "wait"); return 0
        if op == 1:
            n = 0
            for c in self.ctxs:
                if c["state"] == "wait" and c["addr"] == ad and n < (x(2) & 0x7FFFFFFF): c["state"] = "ready"; c["addr"] = None; n += 1
            if self.rng is not None and self.rng.random() < 0.5: self.switch(me, "ready")
            return n
        return -38

    def cstr(self, cpu, a):
        out = bytearray()
        while cpu.mem.get(a, 0): out.append(cpu.mem[a]); a += 1
        return bytes(out).decode()

    def newfd(self, kind, **kw):
        fd = self.next_fd; self.next_fd += 1; self.fds[fd] = dict(kind=kind, **kw); return fd

    def handle(self, cpu, n):
        r = cpu.r; x = lambda i: r["x%d" % i]
        self.syscalls.append(n)
        if n == 222 and x(0) == 0 and x(3) & 0x20:                     # 無名の mmap(アドレス 0): 空きの番地を順に返す(スレッドの積み)
            self.maps.append((x(0), x(1), x(2), x(3), x(4)))
            if getattr(self, "anon_fail", False): return -12
            a = getattr(self, "mmap_next", 0x20000000); self.mmap_next = a + ((x(1) + 0xFFFF) & ~0xFFFF); return a
        if n == 222:                                                   # mmap(アドレス, 長さ, 保護, フラグ, fd, 0)
            f = self.fds.get(x(4))
            if f is not None and f["kind"] == "fb":                    # fbdev の mmap: エミュレータの空きの番地を返す。画素は cpu.mem の中(kernel.fb_base から)
                self.fb_base = 0x70000000; self.fb_len = x(1); self.maps.append((x(0), x(1), x(2), x(3), x(4))); return self.fb_base
            self.maps.append((x(0), x(1), x(2), x(3), x(4))); return -17 if self.map_fail else x(0)
        if n == 56:                                                    # openat
            p = self.cstr(cpu, x(1))
            if p.startswith("/dev/i2c-") and p[9:].isdigit():
                if self.i2c is None or int(p[9:]) not in self.i2c_buses: return -ENOENT
                return self.newfd("i2c", bus=int(p[9:]), addr=None)
            if p.startswith("/dev/input/event") and p[16:].isdigit():       # evdev: kernel.evdev = {番号: [バッチ(24 バイトの input_event の並び), None(= 1 回 EAGAIN), "ENODEV", ...]}
                ev = getattr(self, "evdev", {}).get(int(p[16:]))
                return -ENOENT if ev is None else self.newfd("ev", q=ev)
            if p == "/dev/fb0":                                         # kernel.fb = dict(xres, yres, bpp, ro, rl, go, gl, bo, bl, to, tl)。None なら無い
                return -ENOENT if getattr(self, "fb", None) is None else self.newfd("fb")
            if p == "/dev/gpiochip0": return self.newfd("chip")
            if p == "/etc/resolv.conf":
                rc = getattr(self, "resolv", None)
                return -ENOENT if rc is None else self.newfd("vfile", data=rc, pos=0)
            if p.startswith("/dev/spidev") and len(p) == 14 and p[11].isdigit() and p[12] == "." and p[13].isdigit():
                return -ENOENT if self.spi is None else self.newfd("spi", bus=int(p[11]), cs=int(p[13]), mode=0)
            return -ENOENT
        if n == 57:
            f = self.fds.pop(x(0), None)
            if f is not None and f.get("s"): f["s"].close()
            if f is not None and f.get("rfd") is not None: os.close(f["rfd"])
            return 0 if f is not None else -9
        if n == 437:                                                   # openat2(AT_FDCWD, path, how, 24)
            root = getattr(self, "sysroot", None)
            if root is None: return -ENOENT
            rel = self.cstr(cpu, x(1)); flags, mode, res = cpu.load(x(2), 8), cpu.load(x(2) + 8, 8), cpu.load(x(2) + 16, 8)
            if res != 8 or x(3) != 24: return -EINVAL
            full = os.path.realpath(os.path.join(root, rel)) if not rel.startswith("/") else None
            if full is None or os.path.commonpath([os.path.realpath(root), full]) != os.path.realpath(root): return -18
            try: rfd = os.open(full, flags, mode)
            except OSError as e: return -(e.errno or 5)
            return self.newfd("file", rfd=rfd)
        if n == 62:
            f = self.fds.get(x(0))
            if f and f["kind"] == "mem":
                if x(2) == 2: return len(f["data"])
                f["pos"] = x(1) if x(2) == 0 else f["pos"] + x(1); return f["pos"]
            if not f or f.get("rfd") is None: return -9
            return os.lseek(f["rfd"], x(1), x(2))
        if n in (198, 200, 201, 202, 203, 204, 206, 207, 208, 73): return self.net(cpu, n)
        if n == 29: return self.ioctl(cpu, x(0), x(1) & 0xFFFFFFFF, x(2))
        if n == 63:                                                    # read
            fd, buf, cnt = x(0), x(1), x(2)
            if fd == 0:
                if not self.stdin: return 0
                cpu.mem[buf] = self.stdin.pop(0); return 1
            f = self.fds.get(fd)
            if f and f["kind"] == "ev":
                q = f["q"]
                if not q: return -11
                head = q[0]
                if head is None: q.pop(0); return -11
                if head == "ENODEV": return -19
                take = head[:cnt // 24 * 24]; q[0] = head[len(take):]
                if not q[0]: q.pop(0)
                for i, b in enumerate(take): cpu.mem[buf + i] = b
                return len(take)
            if f and f["kind"] == "vfile":
                data = f["data"][f["pos"]:f["pos"] + cnt]; f["pos"] += len(data)
                for i, b in enumerate(data): cpu.mem[buf + i] = b
                return len(data)
            if f and f["kind"] == "file":
                try: data = os.read(f["rfd"], cnt)
                except OSError as e: return -(e.errno or 5)
                for i, b in enumerate(data): cpu.mem[buf + i] = b
                return len(data)
            if not f or f["kind"] != "i2c" or f["addr"] is None: return -9 if not f else -EINVAL
            return self.i2c_xfer(cpu, f, b"", buf, cnt)
        if n == 64:                                                    # write(fd ≥ 3)
            fd, buf, cnt = x(0), x(1), x(2)
            f = self.fds.get(fd)
            if f and f["kind"] == "mem":
                data = bytes(cpu.mem.get(buf + i, 0) for i in range(cnt)); p0 = f["pos"]
                f["data"][p0:p0 + cnt] = data; f["pos"] = p0 + cnt; return cnt
            if f and f["kind"] == "file":
                try: return os.write(f["rfd"], bytes(cpu.mem.get(buf + i, 0) for i in range(min(cnt, 4096))))     # 一度に 4096 まで(続きは呼び出し側)
                except OSError as e: return -(e.errno or 5)
            if not f or f["kind"] != "i2c" or f["addr"] is None: return -9 if not f else -EINVAL
            return self.i2c_xfer(cpu, f, bytes(cpu.mem.get(buf + i, 0) for i in range(cnt)), None, 0, wlen=cnt)
        if n == 101:                                                   # nanosleep
            sec, ns = cpu.load(x(0), 8), cpu.load(x(0) + 8, 8)
            self.sleeps.append(sec * 1000 + ns // 1_000_000); self.clock += sec * 1000 + ns // 1_000_000; return 0
        if n == 113:                                                   # clock_gettime
            if x(0) == 0:
                import time; t = time.time(); cpu.store(x(1), int(t), 8); cpu.store(x(1) + 8, int((t % 1) * 1e9), 8); return 0
            ms = self.clock
            cpu.store(x(1), ms // 1000, 8); cpu.store(x(1) + 8, (ms % 1000) * 1_000_000, 8); return 0
        # ---- 音(aplay を子プロセスで起動する流儀)。kernel.child = True なら clone は 0(子)を返し、execve で ExecDone を投げる。kernel.aplay = False なら aplay が無い ----
        if n == 279: return self.newfd("mem", data=bytearray(), pos=0)         # memfd_create
        if n == 48:                                                    # faccessat
            self.cstr(cpu, x(1)); return 0 if getattr(self, "aplay", True) else -ENOENT
        if n == 220 and x(0) & 0x10000:
            self.clones = getattr(self, "clones", []) + [(x(0), x(1), x(3))]
            if getattr(self, "clone_fail", False): return -11
            return self.clone_thread(cpu)  # clone(CLONE_THREAD …): 取り合いのない協調スレッド
        if n == 98: return self.futex(cpu)
        if n == 124: self.switch(self.ctx_of(cpu), "ready"); return 0   # sched_yield
        if n == 220:                                                   # clone(fork)
            self.forks = getattr(self, "forks", 0) + 1
            if getattr(self, "child", False): return 0
            self.snd_running = True; return 4321
        if n == 167: self.prctls = getattr(self, "prctls", []) + [(x(0), x(1))]; return 0
        if n == 24:                                                    # dup3(old, new, 0): old の中身を標準入力として記録
            f = self.fds.get(x(0)); self.dups = getattr(self, "dups", []) + [(x(0), x(1))]
            if f is not None and f["kind"] == "mem": self.stdin_data = bytes(f["data"])
            elif f is not None and f.get("rfd") is not None: self.stdin_data = os.pread(f["rfd"], 1 << 27, 0)
            return x(1)
        if n == 221:                                                   # execve
            path = self.cstr(cpu, x(0)); argv, a = [], x(1)
            while cpu.load(a, 8): argv.append(self.cstr(cpu, cpu.load(a, 8))); a += 8
            self.execs = getattr(self, "execs", []) + [(path, argv, x(2))]; raise ExecDone()
        if n == 260:                                                   # wait4(pid, status, options, rusage)
            self.waits = getattr(self, "waits", []) + [(x(0), x(2))]
            if getattr(self, "exit_on_poll", False) and x(2) & 1: self.snd_running = False
            if getattr(self, "snd_running", False) and x(2) & 1: return 0
            self.snd_running = False; return x(0)
        if n == 129: self.kills = getattr(self, "kills", []) + [(x(0), x(1))]; self.snd_running = False; return 0
        return -38

    # ---- ソケット(実際のループバックの socket を使う。実機の Linux のモデル)----
    def sa_get(self, cpu, a):
        port = (cpu.mem.get(a + 2, 0) << 8) | cpu.mem.get(a + 3, 0)
        return ".".join(str(cpu.mem.get(a + 4 + i, 0)) for i in range(4)), port

    def sa_put(self, cpu, a, addr):
        ip, port = addr
        data = struct.pack("<H", 2) + struct.pack(">H", port) + bytes(int(t) for t in ip.split(".")) + bytes(8)
        for i, b in enumerate(data): cpu.mem[a + i] = b

    def net(self, cpu, n):
        r = cpu.r; x = lambda i: r["x%d" % i]
        self.netlog = getattr(self, "netlog", []); self.netlog.append(n)
        try:
            if n == 198:
                if x(0) != 2 or x(1) not in (1, 2): return -97
                return self.newfd("sock", s=socket.socket(socket.AF_INET, x(1)))
            f = self.fds.get(cpu.load(x(0), 4) if n == 73 else x(0)); s = f.get("s") if f else None
            if s is None: return -88 if f else -9
            if n == 208:
                if x(1) == 1 and x(2) == 2: s.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
                if x(1) == 1 and x(2) == 21: f["sndtimeo"] = cpu.load(x(3), 8)
                return 0
            if n == 203:
                ip, port = self.sa_get(cpu, x(1)); s.settimeout(3); s.connect((ip, port)); s.settimeout(None); return 0
            if n == 200: s.bind(self.sa_get(cpu, x(1))); return 0
            if n == 201: s.listen(x(1)); return 0
            if n == 202:
                c, _ = s.accept(); return self.newfd("sock", s=c)
            if n == 204:
                self.sa_put(cpu, x(1), s.getsockname()); cpu.store(x(2), 16, 4); return 0
            if n == 206:
                data = bytes(cpu.mem.get(x(1) + i, 0) for i in range(x(2)))
                self.sends = getattr(self, "sends", []) + [len(data)]
                if x(4):
                    ip, port = self.sa_get(cpu, x(4))
                    if port == 53:
                        if getattr(self, "dns_port", None) is None: return -101
                        port = self.dns_port
                    return s.sendto(data, (ip, port))
                return s.send(data[:1000])                              # 一度に送れるのは 1000 まで(続きは呼び出し側が繰り返す)
            if n == 207:
                if x(3) & 0x40: s.setblocking(False)
                try:
                    if x(4): data, addr = s.recvfrom(x(2)); self.sa_put(cpu, x(4), addr); cpu.store(x(5), 16, 4)
                    else: data = s.recv(x(2))
                finally: s.setblocking(True)
                for i, b in enumerate(data): cpu.mem[x(1) + i] = b
                return len(data)
            if n == 73:
                ts = cpu.load(x(2), 8) * 1000 + cpu.load(x(2) + 8, 8) // 1_000_000
                self.waits = getattr(self, "waits", []) + [ts]
                rd, _, _ = select.select([s], [], [], min(ts, 300) / 1000)
                if not rd: self.clock += ts; return 0
                cpu.store(x(0) + 6, 1, 2); return 1
        except BlockingIOError: return -11
        except socket.timeout: return -110
        except OSError as e: return -(e.errno or 5)
        return -38

    def i2c_xfer(self, cpu, f, wdata, rbuf, rlen, wlen=None):
        try: out = self.i2c.transfer(f["bus"], f["addr"], wdata, rlen)
        except OSError as e: return -(e.errno or EIO)
        for i, b in enumerate(out): cpu.mem[rbuf + i] = b
        return wlen if wlen is not None else len(out)

    def ioctl(self, cpu, fd, req, arg):
        f0 = self.fds.get(fd)
        if f0 is not None and f0["kind"] == "fb":
            fb = self.fb; bp = fb["bpp"]
            if req == 0x4600:                                          # FBIOGET_VSCREENINFO(160 バイト)
                vals = {0: fb["xres"], 4: fb["yres"], 8: fb["xres"], 12: fb["yres"], 24: bp, 32: fb["ro"], 36: fb["rl"], 44: fb["go"], 48: fb["gl"], 56: fb["bo"], 60: fb["bl"], 68: fb["to"], 72: fb["tl"]}
                for i in range(160): cpu.mem[arg + i] = 0
                for o, v in vals.items():
                    for i in range(4): cpu.mem[arg + o + i] = (v >> (8 * i)) & 0xFF
                return 0
            if req == 0x4602:                                          # FBIOGET_FSCREENINFO(80 バイト)
                line = fb["xres"] * bp // 8 + fb.get("pad", 0); self.fb_line = line
                for i in range(80): cpu.mem[arg + i] = 0
                for o, v in {24: line * fb["yres"], 48: line}.items():
                    for i in range(4): cpu.mem[arg + o + i] = (v >> (8 * i)) & 0xFF
                return 0
            return -25
        f = self.fds.get(fd)
        if not f: return -9
        if f["kind"] == "i2c":
            if req == I2C_SLAVE:
                if not 0 <= arg <= 127: return -EINVAL
                f["addr"] = arg; return 0
            if req == I2C_RDWR:
                msgs, nm = cpu.load(arg, 8), cpu.load(arg + 8, 4)
                wdata, rbuf, rlen, addr = b"", None, 0, None
                for i in range(nm):
                    m = msgs + 16 * i
                    addr = cpu.load(m, 2); flags = cpu.load(m + 2, 2); ln = cpu.load(m + 4, 2); buf = cpu.load(m + 8, 8)
                    if flags & 1: rbuf, rlen = buf, ln
                    else: wdata += bytes(cpu.mem.get(buf + j, 0) for j in range(ln))
                try: out = self.i2c.transfer(f["bus"], addr, wdata, rlen)
                except OSError as e: return -(e.errno or EIO)
                for i, b in enumerate(out): cpu.mem[rbuf + i] = b
                return nm
            return -ENOTTY
        if f["kind"] == "spi":
            if req == 0x40016B01:                                  # SPI_IOC_WR_MODE
                f["mode"] = cpu.mem.get(arg, 0); return 0 if f["mode"] <= 3 else -EINVAL
            if req == 0x40206B00:                                  # SPI_IOC_MESSAGE(1)
                tx, rx, ln, speed = cpu.load(arg, 8), cpu.load(arg + 8, 8), cpu.load(arg + 16, 4), cpu.load(arg + 20, 4)
                if cpu.mem.get(arg + 25, 0) != 8: return -EINVAL
                data = bytes(cpu.mem.get(tx + i, 0) for i in range(ln))
                try: out = self.spi.transfer(f["bus"], f["cs"], f["mode"], speed, data)
                except OSError as e: return -(e.errno or EIO)
                for i, b in enumerate(out): cpu.mem[rx + i] = b
                return ln
            return -ENOTTY
        if f["kind"] == "chip" and req == GET_LINE:
            pin = cpu.load(arg, 4); flags = cpu.load(arg + 288, 8); nl = cpu.load(arg + 560, 4)
            if nl != 1 or pin >= 64 or cpu.load(arg + 256, 4) != 0x6e676973: return -EINVAL
            fd2 = self.newfd("line", pin=pin, flags=flags)
            self.modes[pin] = flags
            if flags & 8: self.levels.setdefault(pin, 0)
            cpu.store(arg + 588, fd2, 4); return 0
        if f["kind"] == "line":
            pin = f["pin"]
            if req == GET_VALUES:
                mask = cpu.load(arg + 8, 8)
                if mask != 1: return -EINVAL
                v = self.levels.get(pin, 0) if f["flags"] & 8 else self.inputs.get(pin, 1 if f["flags"] & 0x100 else 0)
                cpu.store(arg, v & 1, 8); return 0
            if req == SET_VALUES:
                if not f["flags"] & 8: return -EPERM
                v = cpu.load(arg, 8) & 1; self.levels[pin] = v; self.log.append((pin, v)); return 0
        return -ENOTTY
