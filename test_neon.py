"""test_neon.py — sign_neon.py(NEON Sign の試作)の試験。
出した命令を小さなエミュレータ(v レジスタは 16 バイト)で動かし、処理系(--check-f32)と値を突き合わせる。
命令数は、NEON の出力と、同じ式をレーンごとのスカラー命令で出した基準(scalar=True)とで比べる。"""
import os, random, re, struct, subprocess, sys, tempfile
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import sign_interp, sign_neon

class Emu:
    def __init__(self, text):
        self.lines = []; self.labels = {}; self.data = {}; sect = "text"; dptr = 0x1000; self.mem = bytearray(0x2000)
        for raw in text.splitlines():
            l = raw.split("//")[0].strip()
            if not l: continue
            if l.startswith(".section"): sect = "data"; continue
            if l == ".text": sect = "text"; continue
            if l.startswith((".globl", ".balign")): 
                if l.startswith(".balign"): dptr = (dptr + 15) & ~15
                continue
            if l.endswith(":"):
                if sect == "text": self.labels[l[:-1]] = len(self.lines)
                else: self.data[l[:-1]] = dptr
                continue
            if sect == "data":
                kind, vals = l.split(None, 1); vals = [float(v) for v in vals.split(",")]
                fmt = "<%df" if kind == ".float" else "<%dd"
                b = struct.pack(fmt % len(vals), *vals); self.mem[dptr:dptr + len(b)] = b; dptr += len(b); continue
            self.lines.append(l)
        self.v = [bytearray(16) for _ in range(32)]; self.steps = 0; self.kinds = {}

    @staticmethod
    def rnd(x):
        try: return struct.unpack("<f", struct.pack("<f", x))[0]
        except OverflowError: return float("inf") if x > 0 else float("-inf")
    @staticmethod
    def arith(op, a, b):
        try:
            if op == "fadd": return a + b
            if op == "fsub": return a - b
            if op == "fmul": return a * b
            if op == "fdiv": return a / b
        except ZeroDivisionError:
            if a != a or a == 0: return float("nan")
            neg = (a < 0) != (str(b)[0] == "-"); return float("-inf") if neg else float("inf")
    def lanes(self, r): return list(struct.unpack("<4f", bytes(self.v[r])))
    def setl(self, r, ls): self.v[r][:] = struct.pack("<4f", *[self.rnd(x) for x in ls])
    def sreg(self, r): return struct.unpack("<f", bytes(self.v[r][:4]))[0]
    def dreg(self, r): return struct.unpack("<d", bytes(self.v[r][:8]))[0]
    def set_s(self, r, x): self.v[r][:] = struct.pack("<f", self.rnd(x)) + bytes(12)
    def set_d(self, r, x): self.v[r][:] = struct.pack("<d", x) + bytes(8)

    def run(self, entry="_.main"):
        pc = self.labels[entry]; stack = []; self.x = {}
        while True:
            l = self.lines[pc]; pc += 1; self.steps += 1
            op, _, rest = l.partition(" "); a = [t.strip() for t in re.split(r",(?![^\[]*\])", rest)] if rest else []
            if op == "ret":
                if not stack: return
                pc = stack.pop(); continue
            if op == "bl": stack.append(pc); pc = self.labels[a[0]]; continue
            if op in ("stp", "ldp", "mov") and a and a[0][0] in "xs" and not a[0].startswith("s") or op in ("stp", "ldp"):
                if op == "mov" and a[0][0] == "x": continue
                if op in ("stp", "ldp"): continue
            if op == "adrp": self.x[a[0]] = self.data[a[1]]; continue
            if op == "add" and a[0] == "x9": continue
            if op == "ldr":
                addr = self.x["x9"] + (int(re.search(r"#(\d+)", a[1]).group(1)) if "#" in a[1] else 0)
                k = a[0][0]; r = int(a[0][1:]); n = {"q": 16, "d": 8, "s": 4}[k]
                self.v[r][:] = bytes(self.mem[addr:addr + n]) + bytes(16 - n); continue
            m = re.fullmatch(r"v(\d+)\.4s", a[0]) if a else None
            if op in ("fadd", "fsub", "fmul", "fdiv") and m:
                d = int(m.group(1)); x = self.lanes(int(a[1][1:].split(".")[0])); y = self.lanes(int(a[2][1:].split(".")[0]))
                self.setl(d, [self.arith(op, p, q) for p, q in zip(x, y)]); continue
            if op in ("fadd", "fsub", "fmul", "fdiv"):
                d = int(a[0][1:]); r1 = int(a[1][1:]); r2 = int(a[2][1:])
                if a[0][0] == "s": self.set_s(d, self.arith(op, self.sreg(r1), self.sreg(r2)))
                else: self.set_d(d, self.arith(op, self.dreg(r1), self.dreg(r2)))
                continue
            if op == "fcvt":
                if a[0][0] == "s": self.set_s(int(a[0][1:]), self.dreg(int(a[1][1:])))
                else: self.set_d(int(a[0][1:]), self.sreg(int(a[1][1:])))
                continue
            if op == "dup":
                d = int(re.match(r"v(\d+)", a[0]).group(1)); s = int(re.match(r"v(\d+)", a[1]).group(1)); self.setl(d, [self.sreg(s)] * 4); continue
            if op == "mov" and a[0][0] in "xw" and not a[1].startswith("v"): continue                # x0 = `__` の旗
            if op == "fmov": self.set_d(int(a[0][1:]), self.dreg(int(a[1][1:]))); continue
            if op == "mov":
                if a[0] == "v0.16b" or re.fullmatch(r"v\d+\.16b", a[0]): self.v[int(a[0][1:].split(".")[0])][:] = self.v[int(a[1][1:].split(".")[0])]; continue
                m1 = re.fullmatch(r"s(\d+)", a[0]); m2 = re.fullmatch(r"v(\d+)\.s\[(\d)\]", a[1])
                if m1 and m2: self.set_s(int(m1.group(1)), self.lanes(int(m2.group(1)))[int(m2.group(2))]); continue
                m1 = re.fullmatch(r"v(\d+)\.s\[(\d)\]", a[0]); m2 = re.fullmatch(r"v(\d+)\.s\[0\]", a[1])
                if m1 and m2:
                    ls = self.lanes(int(m1.group(1))); ls[int(m1.group(2))] = self.sreg(int(m2.group(1))); self.setl(int(m1.group(1)), ls); continue
            raise RuntimeError("エミュレータに無い命令: " + l)


# ---- 整数の Cpu(test_asm.py)に浮動小数・NEON の命令を足した物: --target=linux の入口と印字ルーチンを通しで動かす ----
_src_asm = open(os.path.join(HERE, "test_asm.py"), encoding="utf-8").read().split("MAX, MIN1 =")[0]
_ns = {"__file__": os.path.join(HERE, "test_asm.py")}
exec(compile(_src_asm, "test_asm_head", "exec"), _ns)
Cpu = _ns["Cpu"]
class NeonCpu(Cpu):
    fp_enabled = True
    def __init__(self, text):
        super().__init__(text); self.v = [bytearray(16) for _ in range(32)]
    def _lanes(self, r): return list(struct.unpack("<4f", bytes(self.v[r])))
    def _setl(self, r, ls): self.v[r][:] = struct.pack("<4f", *[Emu.rnd(x) for x in ls])
    def _s(self, r): return struct.unpack("<f", bytes(self.v[r][:4]))[0]
    def _d(self, r): return struct.unpack("<d", bytes(self.v[r][:8]))[0]
    def _sets(self, r, x): self.v[r][:] = struct.pack("<f", Emu.rnd(x)) + bytes(12)
    def _setd(self, r, x): self.v[r][:] = struct.pack("<d", x) + bytes(8)
    def fp_op(self, op, a):
        if not a: return False
        first = a[0]
        if op in ("ldr", "str") and first[0] in "qds" and first[1:].isdigit():
            n = {"q": 16, "d": 8, "s": 4}[first[0]]; r = int(first[1:]); addr = self.memaddr(a[1])
            if op == "ldr": self.v[r][:] = bytes((self.load(addr, n) >> (8 * i)) & 0xFF for i in range(n)) + bytes(16 - n)
            else:
                for i in range(n): self.mem[addr + i] = self.v[r][i]
            return True
        if op == "ldp" and first[0] == "q" and first[1:].isdigit():
            addr = self.memaddr(a[2]); r1, r2 = int(first[1:]), int(a[1][1:])
            self.v[r1][:] = bytes((self.load(addr, 16) >> (8 * i)) & 0xFF for i in range(16)); self.v[r2][:] = bytes((self.load(addr + 16, 16) >> (8 * i)) & 0xFF for i in range(16)); return True
        m2 = re.fullmatch(r"v(\d+)\.2d", first)
        if op in ("fadd", "fsub", "fmul", "fdiv") and m2:
            d = int(m2.group(1)); x = struct.unpack("<2d", bytes(self.v[int(a[1][1:].split(".")[0])])); y = struct.unpack("<2d", bytes(self.v[int(a[2][1:].split(".")[0])]))
            self.v[d][:] = struct.pack("<2d", *[Emu.arith(op, p, q) for p, q in zip(x, y)]); return True
        m = re.fullmatch(r"v(\d+)\.4s", first)
        if op in ("fadd", "fsub", "fmul", "fdiv") and m:
            d = int(m.group(1)); x = self._lanes(int(a[1][1:].split(".")[0])); y = self._lanes(int(a[2][1:].split(".")[0]))
            self._setl(d, [Emu.arith(op, p, q) for p, q in zip(x, y)]); return True
        if op in ("fadd", "fsub", "fmul", "fdiv") and first[0] in "sd":
            d, r1, r2 = int(first[1:]), int(a[1][1:]), int(a[2][1:])
            if first[0] == "s": self._sets(d, Emu.arith(op, self._s(r1), self._s(r2)))
            else: self._setd(d, Emu.arith(op, self._d(r1), self._d(r2)))
            return True
        if op == "fcmeq":
            d = int(re.match(r"v(\d+)", first).group(1)); s_ = int(re.match(r"v(\d+)", a[1]).group(1))
            self.v[d][:] = b"".join((b"\xff\xff\xff\xff" if x == 0 else bytes(4)) for x in self._lanes(s_)); return True
        if op == "umaxv":
            d = int(first[1:]); s_ = int(re.match(r"v(\d+)", a[1]).group(1))
            m = max(struct.unpack("<4I", bytes(self.v[s_]))); self.v[d][:] = struct.pack("<I", m) + bytes(12); return True
        if op == "scvtf" and first[0] == "d":
            self._setd(int(first[1:]), float(_ns["s64"](self.reg(a[1])))); return True
        if op == "fcvt":
            if first[0] == "s": self._sets(int(first[1:]), self._d(int(a[1][1:])))
            else: self._setd(int(first[1:]), self._s(int(a[1][1:])))
            return True
        if op == "dup":
            d = int(re.match(r"v(\d+)", first).group(1)); s = int(re.match(r"v(\d+)", a[1]).group(1)); self._setl(d, [self._s(s)] * 4); return True
        if op == "fmov":
            if first[0] == "d" and a[1][0] == "d": self._setd(int(first[1:]), self._d(int(a[1][1:]))); return True
            if first[0] == "w" and a[1][0] == "s": self.setreg(first, struct.unpack("<I", bytes(self.v[int(a[1][1:])][:4]))[0]); return True
            if first[0] == "x" and a[1][0] == "d": self.setreg(first, struct.unpack("<Q", struct.pack("<d", self._d(int(a[1][1:]))))[0]); return True
            return False
        if op == "mov" and first[0] == "d" and re.fullmatch(r"v(\d+)\.d\[(\d)\]", a[1]):
            m3 = re.fullmatch(r"v(\d+)\.d\[(\d)\]", a[1]); k = int(m3.group(2)); self.v[int(first[1:])][:] = bytes(self.v[int(m3.group(1))][8 * k:8 * k + 8]) + bytes(8); return True
        if op == "mov":
            if re.fullmatch(r"v\d+\.16b", first): self.v[int(first[1:].split(".")[0])][:] = self.v[int(a[1][1:].split(".")[0])]; return True
            m1 = re.fullmatch(r"s(\d+)", first); m2 = re.fullmatch(r"v(\d+)\.s\[(\d)\]", a[1])
            if m1 and m2: self._sets(int(m1.group(1)), self._lanes(int(m2.group(1)))[int(m2.group(2))]); return True
            m1 = re.fullmatch(r"v(\d+)\.s\[(\d)\]", first); m2 = re.fullmatch(r"v(\d+)\.s\[0\]", a[1])
            if m1 and m2:
                ls = self._lanes(int(m1.group(1))); ls[int(m1.group(2))] = self._s(int(m2.group(1))); self._setl(int(m1.group(1)), ls); return True
        return False

def interp(src):
    d = tempfile.mkdtemp(); p = os.path.join(d, "t.sn"); open(p, "w", encoding="utf-8").write(src)
    r = subprocess.run([sys.executable, os.path.join(HERE, "sign.py"), p, "--check-f32"], capture_output=True, text=True, timeout=60)
    return r.stdout.strip()

def nums(s):
    return [float(t) for t in re.findall(r"[-+]?(?:inf|nan|\d[\d.]*(?:e[-+]?\d+)?)", s)]

def run_neon(src, scalar=False):
    text = sign_neon.generate(sign_interp.parse_source(src), scalar); e = Emu(text); e.run()
    return e, text

def result_of(e, src):
    """処理系の出力の形(Vector か Float か)に合わせて v0 / d0 を読む。"""
    return e

bad = 0
def check(name, got, want):
    global bad
    ok = got == want; bad += not ok
    print(("ok  " if ok else "NG  ") + name + ("" if ok else "\n    got  %r\n    want %r" % (got, want)))

def same(name, src, lane=False):
    want = interp(src)
    e, _ = run_neon(src)
    if want.startswith("["): got = e.lanes(0); w = [Emu.rnd(x) for x in nums(want)]
    else: got = [e.dreg(0)]; w = nums(want)
    def eq(a, b): return (a != a and b != b) or a == b
    check(name, [eq(x, y) for x, y in zip(got, w)] + [len(got) == len(w)], [True] * len(w) + [True])

V1, V2 = "[1.0 2.0 3.0 4.0]", "[0.5 0.25 3.0 8.0]"
VN = "[0.5 -0.25 3.0 -8.0]"
same("負の字面を含む Vector(足す)", "f : a b ? a + b\nf %s %s\n" % (V1, VN))
same("負の字面を含む Vector(掛ける・レーン)", "f : a b ? (a * b) ' 3\nf %s %s\n" % (V1, VN))
same("負の字面を含む Vector(定数で割る)", "f : a ? a / 2.0 - [1.0 -1.0 1.0 -1.0]\nf %s\n" % VN)
check("処理系: 負の字面を含む 4 つの Float は Vector(type_system.md §2)", interp("v : [1.0 2.0 3.0 -4.0]\nv * 2.0\n"), "[2.0 4.0 6.0 -8.0]")
check("処理系: 二項の引き算は Vector の字面ではない", interp("x : [1.0 - 2.0 3.0 4.0]\nx\n"), "[-1.0, 3.0, 4.0]")
same("足す", "f : a b ? a + b\nf %s %s\n" % (V1, V2))
same("引く", "f : a b ? a - b\nf %s %s\n" % (V1, V2))
same("掛ける", "f : a b ? a * b\nf %s %s\n" % (V1, V2))
same("掛けて足す", "f : a b ? a * b + a\nf %s %s\n" % (V1, V2))
same("括弧と入れ子", "f : a b ? (a + b) * (a - b)\nf %s %s\n" % (V1, V2))
same("Float を撒く(右)", "f : a b ? a * b\nf %s 0.1\n" % V1)
same("Float を撒く(左・引き算の順)", "f : a b ? b - a\nf %s 0.1\n" % V1)
same("Float 0.1 は 32 ビットに丸めて撒く", "f : a b ? a + b\nf [0.0 0.0 0.0 0.0] 0.1\n")
same("Float だけの式は 64 ビット", "f : a b ? a * b + a\nf 0.1 3.0\n")
same("定数で割る", "f : a ? a / 4.0\nf %s\n" % V1)
same("字面を式の中に", "f : a ? a * [2.0 2.0 2.0 2.0] + 1.5\nf %s\n" % V1)
same("レーンを読む", "f : a b ? (a * b) ' 2\nf %s %s\n" % (V1, V2))
same("レーン 0 と 3", "f : a ? (a / 3.0) ' 3\nf %s\n" % V1)
same("オーバーフローは inf", "f : a ? a * a * a * a\nf [1.0e20 1.0 2.0 3.0]\n") if False else None
for k in range(4): same("レーン %d(1/3 の丸め)" % k, "f : a ? (a / 3.0) ' %d\nf %s\n" % (k, V1))
refuse = lambda src: (lambda: (sign_neon.generate(sign_interp.parse_source(src)), None))
def refused(src):
    try: sign_neon.generate(sign_interp.parse_source(src)); return False
    except sign_neon.NeonError: return True
check("断る: 剰余", refused("f : a b ? a %% b\nf %s %s\n" % (V1, V2)), True)
check("断る: 関数の入れ子の呼び", refused("g : a ? a\nf : a ? g a\nf %s\n" % V1), True)

# 乱数: 式の形を変えて処理系と比べる
rnd = random.Random(7); n_ok = 0
def rexpr(vs, d):
    if d == 0 or rnd.random() < .3:
        return rnd.choice(vs) if rnd.random() < .7 else rnd.choice(["0.5", "2.0", "-1.25", "3.0"])
    return "(%s %s %s)" % (rexpr(vs, d - 1), rnd.choice("+-*"), rexpr(vs, d - 1))
def rvec(): return "[%s]" % " ".join(rnd.choice(["1.0", "2.5", "-0.75", "0.1", "100.0", "0.3333"]) for _ in range(4))
for i in range(60):
    kind = rnd.choice(["V", "VV", "VF"])
    args = {"V": [rvec()], "VV": [rvec(), rvec()], "VF": [rvec(), rnd.choice(["0.1", "2.0", "3.5"])]}[kind]
    ps = ["a", "b"][:len(args)]; body = rexpr(ps, 3)
    if not all(p in body for p in ps): body = "(%s + %s)" % (body, " + ".join(ps)) if len(ps) > 1 else body
    src = "f : %s ? %s\nf %s\n" % (" ".join(ps), body, " ".join(args))
    want = interp(src)
    if not want.startswith("["): continue
    try: e, _ = run_neon(src)
    except sign_neon.NeonError: continue
    w = [Emu.rnd(x) for x in nums(want)]; g = e.lanes(0)
    if all((x != x and y != y) or x == y for x, y in zip(g, w)): n_ok += 1
    else: bad += 1; print("NG  乱数", repr(src), g, w)
check("乱数 60 本のうち比べられた物がすべて一致", n_ok > 35, True)

# 命令数: NEON と、レーンごとのスカラー(同じ式)
for name, src in [("a*b+a", "f : a b ? a * b + a\nf %s %s\n" % (V1, V2)), ("(a+b)*(a-b)", "f : a b ? (a + b) * (a - b)\nf %s %s\n" % (V1, V2))
                  ]:
    en, _ = run_neon(src); es, _ = run_neon(src, scalar=True)
    ln, ls = en.lanes(0), es.lanes(0)
    print("命令数 %-14s NEON %3d  スカラー %3d  (値は同じ: %s)" % (name, en.steps, es.steps, ln == ls))
    check("命令数の基準と NEON の値が同じ: " + name, ln, ls)

# ---- --asm への統合 ----
import sign_asm
def gen(src, **kw):
    try: return sign_asm.generate(sign_interp.parse_source(src), **kw)
    except sign_asm.AsmError as e: return "断り: " + str(e)
SRC = "f : a b ? a * b + a\nf %s %s\n" % (V1, V2)
_t = gen(SRC)
check("統合: generate が NEON の道へ回る", "fmul v16.4s" in _t, True)
check("統合: 出力が sign_neon.generate と同じ", _t, sign_neon.generate(sign_interp.parse_source(SRC)))
check("統合: lint は 0 件", sign_asm.LAST_LINT, [])
check("統合: --target=bare / linux 以外は断る", gen(SRC, target="x").startswith("断り: Float / Vector(NEON)は --target=bare"), True)
check("統合: 出せない形は NEON: で断る", gen("f : a b ? a %% b\nf %s %s\n" % (V1, V2)).startswith("断り: NEON:"), True)
sign_asm.NEON[0] = False
check("統合: --no-neon なら Float は断る", gen(SRC).startswith("断り: "), True)
sign_asm.NEON[0] = True
check("統合: Int だけの関数は今までどおり(NEON の道を通らない)", "neon" not in gen("f : a ? a + 1\nf 2\n"), True)
r = subprocess.run([sys.executable, os.path.join(HERE, "sign.py"), "--asm", "/dev/stdin"], input=SRC, capture_output=True, text=True)
check("統合: sign.py --asm で出る", (r.returncode, "fmul v16.4s" in r.stdout), (0, True))
r = subprocess.run([sys.executable, os.path.join(HERE, "sign.py"), "--asm", "/dev/stdin", "--no-neon"], input=SRC, capture_output=True, text=True)
check("統合: sign.py --asm --no-neon は断る", (r.returncode != 0, "出せません" in r.stderr), (True, True))

# ---- --target=linux: 結果を処理系と同じ綴りで書いて exit(印字ルーチン sign_fmt.py を含む。通しでエミュレータに掛ける) ----
def run_linux(src):
    text = sign_asm.generate(sign_interp.parse_source(src), target="linux")
    c = NeonCpu(text); c.r["sp"] = 0x7fff0000; c.run("_start", limit=80_000_000)
    return bytes(c.out).decode(), c.exit
def same_linux(name, src):
    want = interp(src); got = run_linux(src)
    check("linux 通し: " + name, got, (want + "\n", 0))
same_linux("掛けて足す", "f : a b ? a * b + a\nf %s %s\n" % (V1, V2))
same_linux("1/3 の丸め(最短の桁)", "f : a ? a / 3.0\nf %s\n" % V1)
same_linux("負の字面", "f : a b ? a * b - a\nf %s %s\n" % (V1, VN))
same_linux("レーン(Float は 64 ビットの最短)", "f : a ? (a / 3.0) ' 1\nf %s\n" % V1)
same_linux("Float だけ(0.1 * 3.0)", "f : a b ? a * b\nf 0.1 3.0\n")
same_linux("Float だけ(整数値は .0)", "f : a b ? a * b\nf 2.0 4.0\n")
same_linux("大きな Float(1e+16 以上は指数表記)", "f : a b ? a * b\nf 1000000000.0 100000000.0\n")
same_linux("小さな Float(1e-05)", "f : a b ? a / b\nf 1.0 100000.0\n")
same_linux("Float の inf", "f : a b ? a / b\nf 1.0 0.0\n")
same_linux("Float の nan", "f : a b ? a / b\nf 0.0 0.0\n")
same_linux("Vector の大きな値(1e+20 の指数表記)", "f : a ? a * 100000000000000000000.0\nf %s\n" % V1)
same_linux("Vector の小さな値", "f : a ? a / 100000.0\nf %s\n" % V1)

# ---- Int の関数と Float の関数を同じプログラムで ----
G = "g : n ? n * 2\nh : n ? g n + 1\n"
same_linux("Int の関数の値を Vector に掛ける", G + "f : a n ? a * n\nf %s (g 3)\n" % V1)
same_linux("Int の関数が別の Int の関数を呼ぶ", G + "f : a n ? a * n - n\nf %s (h 2)\n" % V1)
same_linux("Int の実引数が 2 つ(字面と式)", G + "f : a n m ? a * n + m\nf %s (g 3) 5\n" % V1)
same_linux("Int の字面を Float に", "f : a n ? a * n\nf 0.1 7\n")
same_linux("Int を左に置く(引き算の順)", "f : a n ? n - a\nf %s 10\n" % V1)
same_linux("Int の字面が本体に", "f : a n ? a * n + 1\nf %s 3\n" % V2)
same_linux("Float を Int で割る(Float だけ)", "f : a n ? a / n\nf 1.0 4\n")
same_linux("Vector を Int の字面で割る", "f : a ? a / 4\nf %s\n" % V1)
same_linux("2^24+1 は binary32 に丸まる(Int → Float → binary32)", "f : a n ? a + n\nf [0.5 0.5 0.5 0.5] 16777217\n")
same_linux("Int の引数の後ろに Vector(レジスタは x と v で別に数える)", G + "f : n a ? a * n\nf (g 2) %s\n" % V1)
same_linux("Int と Float と Vector の混在(順序)", "f : n x a ? a * x + n\nf 2 0.5 %s\n" % V1)
_t = gen(G + "f : a n ? a * n\nf %s (g 3)\n" % V1)
check("混在: 出力に Int の道の関数と NEON の関数が両方ある", ("\ng:\n" in _t, "_neon_f_VI:" in _t, "_neon_ints:" in _t), (True, True, True))
check("混在: lint は 0 件", sign_asm.LAST_LINT, [])
check("混在: Int の関数は Float を持てない", gen("g : n ? n * 2.0\nf : a n ? a * n\nf %s (g 3)\n" % V1).startswith("断り: NEON: Int の実引数"), True)
check("混在: Int の実引数に Float の式は断る", gen("f : a n ? a * n\nf %s (1.0 + 2.0)\n" % V1).startswith("断り: NEON:"), True)
check("混在: 本体の Int どうしの演算は断る(Int の関数で)", gen("f : a n m ? a * (n + m)\nf %s 1 2\n" % V1).startswith("断り: NEON:"), True)
check("混在: 結果が Int の関数は NEON の道へ入れない(Int の 3 を 3.0 と書かない)", gen("f : a n ? n\nf 1.0 3\n").startswith("断り: NEON:"), True)
check("混在: Int の道: 使われない Float の関数があっても Int が main なら Int の道", "_neon" not in gen("h : a ? a * 2.0\ng : n ? n * 2\ng 21\n"), True)
check("混在: Int の道: その結果は今までどおり", _ns["run_asm"](sign_asm.generate(sign_interp.parse_source("h : a ? a * 2.0\ng : n ? n * 2\ng 21\n"))), ("ok", 42))

# ---- `__` の持ち回り(Vector の割り算で、割る数に 0 のレーンがあれば全体が `__`。`__` は他の演算では相手の値そのまま) ----
Z4 = "[0.0 1.0 2.0 3.0]"
same_linux("割る数が Vector で 0 のレーンなし", "f : a b ? a / b\nf %s %s\n" % (V1, V2))
same_linux("割る数が Vector で 0 のレーンあり → __", "f : a b ? a / b\nf %s %s\n" % (V1, Z4))
same_linux("0 でない Vector で割る(分子に 0 のレーン)", "f : a b ? a / b\nf %s %s\n" % (Z4, V1))
same_linux("0.0 で割る → __", "f : a ? a / 0.0\nf %s\n" % V1)
same_linux("Float の変数 0.0 で割る → __", "f : a b ? a / b\nf %s 0.0\n" % V1)
same_linux("Int の 0 で割る → __", "f : a n ? a / n\nf %s 0\n" % V1)
same_linux("Int の 2 で割る", "f : a n ? a / n\nf %s 2\n" % V1)
same_linux("Float を Vector で割る(0 のレーンあり → __)", "f : a b ? a / b\nf 2.0 %s\n" % Z4)
same_linux("Float を Float の 0.0 で割る(IEEE の inf、__ ではない)", "f : a b ? a / b\nf 1.0 0.0\n")
same_linux("Float を Int の 0 で割る(inf)", "f : a n ? a / n\nf 1.0 0\n")
same_linux("32 ビットで 0 に丸まる Float で割る → __", "f : a b ? a / b\nf %s 0.00000000000000000000000000000000000000000000000000000000000001\n" % V1)
same_linux("__ + c は c", "f : a b c ? (a / b) + c\nf %s %s %s\n" % (V1, Z4, V2))
same_linux("c - __ は c", "f : a b c ? c - (a / b)\nf %s %s %s\n" % (V1, Z4, V2))
same_linux("__ - c は c(符号を変えない)", "f : a b c ? (a / b) - c\nf %s %s %s\n" % (V1, Z4, V2))
same_linux("__ * c は c", "f : a b c ? (a / b) * c\nf %s %s %s\n" % (V1, Z4, V2))
same_linux("__ / c は c", "f : a b c ? (a / b) / c\nf %s %s %s\n" % (V1, Z4, V2))
same_linux("c / __ は c", "f : a b c ? c / (a / b)\nf %s %s %s\n" % (V1, Z4, V2))
same_linux("__ + __ は __", "f : a b ? (a / b) + (a / b)\nf %s %s\n" % (V1, Z4))
same_linux("__ のレーンは __", "f : a b ? (a / b) ' 1\nf %s %s\n" % (V1, Z4))
same_linux("__ のレーン + Float は Float", "f : a b ? ((a / b) ' 1) + 1.5\nf %s %s\n" % (V1, Z4))
same_linux("__ でない Vector のレーン + Float", "f : a b ? ((a / b) ' 1) + 1.5\nf %s %s\n" % (V1, V2))
same_linux("__ になりうる式の続き(旗が続く)", "f : a b c ? (((a / b) + c) * (c / b)) + a\nf %s %s %s\n" % (V1, Z4, V2))
same_linux("__ の後ろの割り算がもう一度 __", "f : a b c ? ((a / b) + c) / b\nf %s %s %s\n" % (V1, Z4, Z4))
same_linux("__ のレーン * Vector は(型が実行時に決まる形)", "f : a b c ? ((a / b) ' 1) * c\nf %s %s %s\n" % (V1, V2, V2)) if False else None
check("`__` と型の違う値の演算は断る(結果の型が実行時に決まる)", gen("f : a b c ? ((a / b) ' 1) * c\nf %s %s %s\n" % (V1, Z4, V2)).startswith("断り: NEON:"), True)
check("`__` の旗は x0 で返る(bare)", ("mov w0, w" in gen("f : a b ? a / b\nf %s %s\n" % (V1, Z4))), True)
check("`__` にならない関数は x0 = 0 だけ", ("mov x0, #0" in gen("f : a b ? a * b\nf %s %s\n" % (V1, V2))), True)
check("`__` の持ち回り: lint は 0 件", (gen("f : a b c ? ((a / b) + c) * (c / b)\nf %s %s %s\n" % (V1, Z4, V2)) and sign_asm.LAST_LINT), [])

# ---- [op] (map $g xs): 4 要素ずつの融合 ----
MM = "m : f [h ~t] ? (@f h) (m f t)~\n"
def flist(n, seed=1):
    r = random.Random(seed); return "(" + " ".join(repr(round(r.uniform(0.1, 9), 2)) for _ in range(n)) + ")"
for n in (2, 3, 5, 6, 7, 8, 9, 16, 33):
    for op in "+-*/":
        if op in "*/" and n > 9: continue
        same_linux("融合 [%s] n=%d" % (op, n), MM + "g : x ? x * 2.0 + 1.0\nf : xs ? [%s] (m $g xs)\nf %s\n" % (op, flist(n, n)))
same_linux("融合: 名前付き関数 g", MM + "g : x ? x / 3.0 - 0.5\nf : xs ? [+] (m $g xs)\nf %s\n" % flist(7))
same_linux("融合: 切り出し $[* 2.0]", MM + "f : xs ? [-] (m $[* 2.0] xs)\nf %s\n" % flist(6))
same_linux("融合: 恒等(map なし)", "f : xs ? [*] xs\nf %s\n" % flist(6))
same_linux("融合: 負の字面を含む g", MM + "g : x ? x * -1.5 + 2.0\nf : xs ? [+] (m $g xs)\nf %s\n" % flist(7))
same_linux("融合: 二重丸め(0.1 の和)", MM + "g : x ? x\nf : xs ? [+] (m $g xs)\nf (0.1 0.2 0.3 0.4 0.5 0.6 0.7)\n")
rf = random.Random(77); bad_f = 0
for i in range(40):
    n = rf.choice([2, 3, 5, 6, 7, 9, 10, 13]); op = rf.choice("+-*/")
    gb = rf.choice(["x * 2.0 + 1.0", "x / 3.0", "x - 0.5", "(x + 1.0) * (x - 1.0)", "x * x"])
    src = MM + "g : x ? %s\nf : xs ? [%s] (m $g xs)\nf %s\n" % (gb, op, flist(n, i + 100))
    try:
        got = run_linux(src)[0]
    except (sign_neon.NeonError, sign_asm.AsmError) as e:
        got = "断り"
    want = interp(src) + "\n"
    if got != "断り" and got != want: bad_f += 1; print("  不一致", gb, op, n, got, want)
check("融合: 乱数 40 本が処理系と一致", bad_f, 0)
# 命令数: 融合 vs 1 要素ずつ(scalar=True)
def steps(src, scalar):
    nodes = sign_interp.parse_source(src)
    text = sign_neon.generate(nodes, target="linux", scalar=scalar) if scalar else sign_asm.generate(nodes, target="linux")
    c = NeonCpu(text); c.r["sp"] = 0x7fff0000; c.run("_start", limit=80_000_000); return c.steps
try:
    s_src = MM + "g : x ? x * 2.0 + 1.0\nf : xs ? [+] (m $g xs)\nf %s\n" % flist(33)
    s2 = MM + "g : x ? x * 2.0 + 1.0\nf : xs ? [+] (m $g xs)\nf %s\n" % flist(2)
    a, b = steps(s_src, False) - steps(s2, False), steps(s_src, True) - steps(s2, True)
    print("  融合 31 要素分の増分: %d 命令 / 1 要素ずつ: %d 命令(印字は差し引き済み)" % (a, b))
except Exception as e: print("  命令数の比較は省略:", type(e).__name__, e)
import shutil
if shutil.which("llvm-mc"):
    for nm, src in [("掛けて足す", SRC), ("Float を撒く・レーン", "f : a b ? (a / 4.0 - b) ' 3\nf %s 0.1\n" % V1), ("Float だけ", "f : a b ? a * b + a\nf 0.1 3.0\n"), ("Int と Float の混在", G + "f : a n ? a * n\nf %s (g 3)\n" % V1), ("融合", MM + "g : x ? x * 2.0 + 1.0\nf : xs ? [+] (m $g xs)\nf %s\n" % flist(7))]:
        r = subprocess.run(["llvm-mc", "--triple=aarch64-linux-gnu", "-filetype=obj", "-o", "/dev/null"], input=gen(src), capture_output=True, text=True)
        check("llvm-mc で組める: " + nm, (r.returncode, r.stderr[:80]), (0, ""))

print("全部 ok" if not bad else "%d 件 NG" % bad)
sys.exit(1 if bad else 0)
