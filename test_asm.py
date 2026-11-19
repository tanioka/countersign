"""test_asm.py — sign_asm.py が出した AArch64 の命令列を、小さなエミュレータで実行して、処理系の答えと突き合わせる。

- エミュレータは、出した『文字』を読んで動かす(機械語ではない)。使う命令だけを持つ。
- 組めるかは clang(--target=aarch64-linux-gnu)のアセンブラで確かめる(clang が無ければ飛ばす)。
- 処理系の答えは `sign.py --check-int`(Int の溢れを罠にする仕様どおりの動き)。
"""
import os, re, struct, subprocess, sys, tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import sign_asm, sign_interp
_GEN_ALL = []                                  # 生成した全アセンブリ(最後に llvm-mc で組めるか確かめる)
_gen0 = sign_asm.generate
def _gen_rec(nodes, target="bare", source=None, charset="ascii", real_dev=False, fps=60, real_db=False, display=(64, 32), par=None, par_spec=False):
    _t = _gen0(nodes, target, source, charset, real_dev, fps, real_db, display, par, par_spec); _GEN_ALL.append(_t); return _t
sign_asm.generate = _gen_rec

M64 = (1 << 64) - 1
fails = 0
def check(name, got, want):
    global fails
    if got == want: print("ok ", name)
    else: fails += 1; print("NG ", name, "\n    got ", got, "\n    want", want)


# ---------------- エミュレータ ----------------
class Trap(Exception): pass

def s64(x): x &= M64; return x - (1 << 64) if x >> 63 else x

class Cpu:
    def __init__(self, text):
        self.prog, self.labels, self.locals = [], {}, []
        self.mem, self.data = {}, {}
        in_data, dptr, fix = False, 0x200000, []
        for raw in text.splitlines():
            line = raw.split("//")[0].strip()
            if line.startswith(".section") and ("rodata" in line or "bss" in line): in_data = True; continue
            if line == ".text": in_data = False; continue                    # 2 つの出力をつなげた物(Int の道 + NEON の道)では .text に戻る
            if in_data:
                if line.startswith(".balign"):
                    _al = int(line.split()[1]); dptr = (dptr + _al - 1) & ~(_al - 1)
                elif line.startswith(".word"):                     # 4 バイト(utf32 の文字)
                    for v in line.split(None, 1)[1].split(","):
                        for i in range(4): self.mem[dptr + i] = (int(v, 0) >> (8 * i)) & 0xFF
                        dptr += 4
                elif line.startswith((".float", ".double")):                       # NEON Sign(sign_neon.py)の字面
                    _fmt = "<f" if line.startswith(".float") else "<d"
                    for v in line.split(None, 1)[1].split(","):
                        for b in struct.pack(_fmt, float(v)): self.mem[dptr] = b; dptr += 1
                elif line.startswith((".skip", ".zero")): dptr += int(line.split()[1], 0)       # .bss(--real-dev の影レジスタ)
                elif line.startswith(".byte"):
                    for v in line.split(None, 1)[1].split(","): self.mem[dptr] = int(v, 0); dptr += 1
                elif line.startswith(".quad"):
                    tok = line.split()[1]
                    if re.fullmatch(r"-?(0x[0-9a-fA-F]+|\d+)", tok):
                        for i in range(8): self.mem[dptr + i] = (int(tok, 0) >> (8 * i)) & 0xFF
                    else: fix.append((dptr, tok))                  # 別のラベルの番地(入れ子の記述子の表)。あとで埋める
                    dptr += 8
                elif line.endswith(":"): self.data[line[:-1]] = dptr
                continue
            if not line or line.startswith("."  ) and not line.endswith(":"): continue
            if line.endswith(":"):
                if line[:-1].isdigit(): self.locals.append((line[:-1], len(self.prog)))
                else: self.labels[line[:-1]] = len(self.prog)
                continue
            self.prog.append(line)
        for a, tok in fix:
            add = 0
            if "+" in tok: tok, _a = tok.rsplit("+", 1); add = int(_a, 0)           # `ラベル+1`(入れ子のスカラー要素: ptr の bit0)
            for i in range(8): self.mem[a + i] = ((self.data[tok] + add) >> (8 * i)) & 0xFF
        self.r = {("x%d" % i): 0 for i in range(31)}
        self.r["sp"] = 0x7FFF0000
        self.nzcv = [0, 0, 0, 0]
        self.out = b""
        self.exit = None
        self.steps = 0

    def reg(self, name, w=False):
        if name in ("xzr", "wzr"): return 0
        if name[0] == "w": return self.r["x" + name[1:]] & 0xFFFFFFFF
        return self.r[name]

    def setreg(self, name, v):
        if name in ("xzr", "wzr"): return
        if name[0] == "w": self.r["x" + name[1:]] = v & 0xFFFFFFFF
        else: self.r[name] = v & M64

    def val(self, tok):                      # レジスタか #即値(asr 付きも)
        tok = tok.strip()
        m = re.fullmatch(r"(\w+),\s*asr\s*#(\d+)", tok)
        if m: return (s64(self.reg(m.group(1))) >> int(m.group(2))) & M64
        m = re.fullmatch(r"(\w+),\s*lsl\s*#(\d+)", tok)
        if m: return (self.reg(m.group(1)) << int(m.group(2))) & M64
        if tok.startswith("#"): return int(tok[1:], 0) & M64
        if tok.startswith(":lo12:"): return self.data[tok[6:]] & 0xFFF
        return self.reg(tok)

    def addflags(self, a, b, sub=False):
        if sub: b2 = (~b) & M64; carry_in = 1
        else: b2, carry_in = b, 0
        full = a + b2 + carry_in
        res = full & M64
        n = res >> 63; z = int(res == 0); c = int(full >> 64)
        v = int(((a >> 63) == (b2 >> 63)) and ((a >> 63) != (res >> 63)))
        self.nzcv = [n, z, c, v]
        return res

    def cond(self, c):
        n, z, cc, v = self.nzcv
        t = {"eq": z, "ne": not z, "cs": cc, "hs": cc, "cc": not cc, "lo": not cc, "mi": n, "pl": not n,
             "vs": v, "vc": not v, "hi": cc and not z, "ls": (not cc) or z, "ge": n == v, "lt": n != v,
             "gt": (not z) and n == v, "le": z or n != v, "al": 1}
        return bool(t[c])

    def memaddr(self, s):
        m = re.fullmatch(r"\[(\w+),\s*([xw]\d+)(?:,\s*lsl\s*#(\d+))?\]", s.strip())
        if m: return (self.reg(m.group(1)) + (self.reg(m.group(2)) << int(m.group(3) or 0))) & M64
        m = re.fullmatch(r"\[(\w+)(?:,\s*#(-?\w+))?\]", s.strip())
        return (self.reg(m.group(1)) + (int(m.group(2), 0) if m.group(2) else 0)) & M64

    def syscall(self, n): return -38

    def store(self, a, v, n=8):
        for i in range(n): self.mem[a + i] = (v >> (8 * i)) & 0xFF

    def load(self, a, n=8):
        return sum(self.mem.get(a + i, 0) << (8 * i) for i in range(n))

    def target(self, tok, pc):
        m = re.fullmatch(r"(\d+)([bf])", tok)
        if not m: return self.labels[tok]
        if m.group(2) == "b": return max(i for n, i in self.locals if n == m.group(1) and i <= pc - 1)
        return min(i for n, i in self.locals if n == m.group(1) and i >= pc)

    fp_enabled = False
    def fp_op(self, op, args): return False

    epoch = [0]                              # スレッドを切り替えた回数(排他の書き込みの成否に使う)
    CODE_TAG = 0x500000000000                # 関数の番地(adr・blr 用。命令の番号にこの印を足した値)

    def run(self, entry, limit=2_000_000, pc0=None):
        if pc0 is None:
            pc = self.labels[entry]
            self.r["x30"] = -1
        else: pc = pc0                         # 子スレッド(clone の直後から始める)
        hook = getattr(self, "tick_hook", None)               # 取り替え(スレッドの強制切り替え。疑似カーネルが付ける)
        while True:
            self.steps += 1
            if self.steps > limit: raise RuntimeError("命令数の上限")
            if hook is not None and self.steps % self.tick_every == 0: hook(self)
            if pc == -1 or pc >= len(self.prog): return
            line = self.prog[pc]; pc += 1
            op, _, rest = line.partition(" ")
            args = [a.strip() for a in re.split(r",\s*(?![^\[]*\])", rest)] if rest else []
            if self.fp_enabled and self.fp_op(op, args): continue                # 浮動小数・NEON の命令(test_neon.py の NeonCpu が受ける)
            if re.match(r"b\.\w+$", op):
                if self.cond(op[2:]): pc = self.target(args[0], pc)
            elif op == "b": pc = self.target(args[0], pc)
            elif op == "bl" and args[0] not in self.labels and hasattr(self, "extern_" + args[0]): self.r["x0"] = getattr(self, "extern_" + args[0])() & M64      # 外の関数(試験が与える。x0..x5 が引数、戻りは x0)
            elif op == "bl": self.r["x30"] = pc; pc = self.target(args[0], pc)
            elif op == "ret":
                pc = self.r["x30"]
                if pc == M64 or pc == -1: return
            elif op == "wfi": raise Trap()
            elif op == "svc":
                n = self.r["x8"]; self.pc = pc
                if n == 64 and self.r["x0"] in (1, 2):
                    self.out += bytes(self.mem.get(self.r["x1"] + i, 0) for i in range(self.r["x2"])); self.r["x0"] = self.r["x2"]      # 戻りは書いたバイト数(本物の write と同じ)
                elif n == 93: self.exit = self.r["x0"]; return
                elif n == 94:                                           # exit_group: 全スレッドを終える
                    self.exit = self.r["x0"]
                    if hasattr(self, "exit_group"): self.exit_group()
                    return
                else: self.r["x0"] = self.syscall(n) & M64                  # 他のシステムコールは疑似カーネル(fake_kernel.py。既定は ENOSYS)
            elif op == "adrp": self.setreg(args[0], self.data[args[1]] & ~0xFFF)
            elif op in ("mov", "movz", "movn", "movk"): self.mov(op, args)
            elif op in ("add", "sub", "adds", "subs"):
                a = self.reg(args[1]) if args[1] != "sp" else self.r["sp"]
                b = self.val(args[2] if len(args) < 4 else args[2] + "," + args[3])
                res = self.addflags(a, b, op.startswith("sub")) if op.endswith("s") else ((a + b) if op.startswith("add") else (a - b)) & M64
                if args[0] == "sp": self.r["sp"] = res
                else: self.setreg(args[0], res)
            elif op == "eor": self.setreg(args[0], self.reg(args[1]) ^ self.val(args[2]))
            elif op == "tbnz":
                if (self.reg(args[0]) >> int(args[1][1:])) & 1: pc = self.target(args[2], pc)
            elif op == "lsr":
                n = int(args[2][1:], 0) if args[2].startswith("#") else self.reg(args[2]) & 63
                self.setreg(args[0], self.reg(args[1]) >> n)
            elif op == "lsl":
                n = int(args[2][1:], 0) if args[2].startswith("#") else self.reg(args[2]) & 63
                self.setreg(args[0], (self.reg(args[1]) << n) & M64)
            elif op == "asr":
                n = int(args[2][1:], 0) if args[2].startswith("#") else self.reg(args[2]) & 63
                v = self.reg(args[1]); v = v - (1 << 64) if v >> 63 else v
                self.setreg(args[0], (v >> n) & M64)
            elif op == "orr": self.setreg(args[0], self.reg(args[1]) | self.val(args[2]))
            elif op == "and": self.setreg(args[0], self.reg(args[1]) & self.val(args[2]))
            elif op == "neg": self.setreg(args[0], (-self.reg(args[1])) & M64)
            elif op == "cneg":
                v = self.reg(args[1]); self.setreg(args[0], (-v) & M64 if self.cond(args[2]) else v)
            elif op == "mul": self.setreg(args[0], (self.reg(args[1]) * self.reg(args[2])) & M64)
            elif op == "smulh": self.setreg(args[0], ((s64(self.reg(args[1])) * s64(self.reg(args[2]))) >> 64) & M64)
            elif op == "sdiv":
                a, b = s64(self.reg(args[1])), s64(self.reg(args[2]))
                q = 0 if b == 0 else abs(a) // abs(b) * (1 if (a < 0) == (b < 0) else -1)
                self.setreg(args[0], q & M64)
            elif op == "udiv":
                b = self.reg(args[2]); self.setreg(args[0], 0 if b == 0 else self.reg(args[1]) // b)
            elif op == "msub": self.setreg(args[0], (self.reg(args[3]) - self.reg(args[1]) * self.reg(args[2])) & M64)
            elif op == "cmp":
                self.addflags(self.reg(args[0]), self.val(args[1] if len(args) < 3 else args[1] + "," + args[2]), True)
            elif op == "ccmp":
                if self.cond(args[3]): self.addflags(self.reg(args[0]), self.val(args[1]), True)
                else: f = int(args[2][1:], 0); self.nzcv = [(f >> 3) & 1, (f >> 2) & 1, (f >> 1) & 1, f & 1]
            elif op == "csel": self.setreg(args[0], self.reg(args[1]) if self.cond(args[3]) else self.reg(args[2]))
            elif op == "cbz":
                if not self.reg(args[0]): pc = self.target(args[1], pc)
            elif op == "cbnz":
                if self.reg(args[0]): pc = self.target(args[1], pc)
            elif op == "tbz":
                if not (self.reg(args[0]) >> int(args[1][1:])) & 1: pc = self.target(args[2], pc)
            elif op == "stp":
                m = re.fullmatch(r"\[sp,\s*#(-?\d+)\]!", args[2])
                if m:                                                   # 前置更新(フレームの確保)
                    self.r["sp"] = (self.r["sp"] + int(m.group(1))) & M64
                    self.store(self.r["sp"], self.reg(args[0])); self.store(self.r["sp"] + 8, self.reg(args[1]))
                else:                                                   # オフセット指定 [reg, #n]
                    a = self.memaddr(args[2]); self.store(a, self.reg(args[0])); self.store(a + 8, self.reg(args[1]))
            elif op == "ldp":
                if len(args) == 4:                                      # 後置更新(フレームの解放)
                    sp = self.r["sp"]
                    self.setreg(args[0], self.load(sp)); self.setreg(args[1], self.load(sp + 8))
                    self.r["sp"] = (sp + int(args[3][1:])) & M64
                else:
                    a = self.memaddr(args[2]); self.setreg(args[0], self.load(a)); self.setreg(args[1], self.load(a + 8))
            elif op == "str" and args[0].startswith("w"): self.store(self.memaddr(args[1]), self.reg(args[0]) & 0xFFFFFFFF, 4)
            elif op == "ldr" and args[0].startswith("w"): self.setreg(args[0], self.load(self.memaddr(args[1]), 4))
            elif op == "strh": self.store(self.memaddr(args[1]), self.reg(args[0]) & 0xFFFF, 2)
            elif op == "ldrh": self.setreg(args[0], self.load(self.memaddr(args[1]), 2))
            elif op == "str": self.store(self.memaddr(args[1]), self.reg(args[0]))
            elif op == "ldr": self.setreg(args[0], self.load(self.memaddr(args[1])))
            elif op == "ldrb": self.setreg(args[0], self.load(self.memaddr(args[1]), 1))
            elif op == "strb": self.store(self.memaddr(args[1]), self.reg(args[0]) & 0xFF, 1)
            elif op == "blr": self.r["x30"] = pc; pc = self.reg(args[0]) - self.CODE_TAG
            elif op == "br": pc = self.reg(args[0]) - self.CODE_TAG
            elif op == "adr": self.setreg(args[0], self.labels[args[1]] + self.CODE_TAG)
            elif op in ("ldar", "ldaxr", "ldxr"):                      # 排他・取得の読み。排他の読みは、そのときの切り替えの回数を覚える
                a = self.memaddr(args[1]); self.setreg(args[0], self.load(a, 4 if args[0].startswith("w") else 8))
                if op != "ldar": self.excl = Cpu.epoch[0]
            elif op == "stlr": self.store(self.memaddr(args[1]), self.reg(args[0]) & (0xFFFFFFFF if args[0].startswith("w") else M64), 4 if args[0].startswith("w") else 8)
            elif op in ("stlxr", "stxr"):                              # 排他の書き込み: 読んでから切り替えが起きていれば失敗(戻り 1)
                if getattr(self, "excl", None) == Cpu.epoch[0]:
                    self.store(self.memaddr(args[2]), self.reg(args[1]) & (0xFFFFFFFF if args[1].startswith("w") else M64), 4 if args[1].startswith("w") else 8); self.setreg(args[0], 0)
                else: self.setreg(args[0], 1)
                self.excl = None
            elif op == "yield":
                if hook is not None: hook(self)
            elif op in ("dmb", "dsb", "isb", "nop"): pass
            elif op == "mrs":
                self.setreg(args[0], getattr(self, "tpidr", 0) if args[1] == "tpidr_el0" else self.steps)       # cntvct_el0 は実行した命令の数
            elif op == "msr": self.tpidr = self.reg(args[1])
            else: raise RuntimeError("エミュレータに無い命令: " + line)

    def mov(self, op, args):
        d = args[0]
        if op == "mov":
            if args[1] == "sp": self.setreg(d, self.r["sp"]); return
            if d == "x29" and args[1] == "sp": self.r["x29"] = self.r["sp"]; return
            self.setreg(d, self.val(args[1])); return
        sh = 0
        if len(args) > 2: sh = int(args[2].split("#")[1])
        imm = int(args[1][1:], 0)
        if op == "movz": self.setreg(d, imm << sh)
        elif op == "movn": self.setreg(d, ~(imm << sh))
        else: self.setreg(d, (self.reg(d) & ~(0xFFFF << sh)) | (imm << sh))


def run_asm(text, entry="_.main", linux=False):
    cpu = Cpu(text)
    try:
        cpu.run("_start" if linux else entry)
    except Trap:
        return ("trap", None)
    if linux: return ("exit", cpu.out.decode(), cpu.exit)
    return ("ok", "__" if cpu.r["x0"] == 0x8000000000000000 else s64(cpu.r["x0"]))


# ---------------- 処理系の答え ----------------
def interp(src):
    d = tempfile.mkdtemp(); p = os.path.join(d, "t.sn"); open(p, "w", encoding="utf-8").write(src)
    r = subprocess.run([sys.executable, os.path.join(HERE, "sign.py"), p, "--check-int"], capture_output=True, text=True, timeout=60)
    if r.returncode != 0 or "罠" in r.stderr + r.stdout: return ("trap", None)
    last = r.stdout.strip().splitlines()[-1]
    return ("ok", "__" if last == "__" else int(last))


def asm_of(src, target="bare"):
    return sign_asm.generate(sign_interp.parse_source(src), target)


MAX, MIN1 = 9223372036854775807, -9223372036854775807
CASES = [
    ("字面だけ", "42\n"),
    ("負の字面", "-7\n"),
    ("足し算", "1 + 2\n"),
    ("引き算", "10 - 25\n"),
    ("掛け算と優先順位", "1 + 2 * 3\n"),
    ("符号反転", "g : x ? -x\ng 4\n"),
    ("関数", "sq : n ? n * n\nsq 12\n"),
    ("入れ子の呼び出し", "sq : n ? n * n\nadd3 : a b c ? a + b * c - 1\nadd3 (sq 3) 4 5\n"),
    ("呼び出しの引数に呼び出し", "inc : x ? x + 1\ndbl : x ? x * 2\ninc (dbl (inc (dbl 5)))\n"),
    ("関数から関数", "sq : n ? n * n\nq4 : n ? sq (sq n)\nq4 3\n"),
    ("引数 8 個", "s8 : a b c d e f g h ? a + b + c + d + e + f + g + h\ns8 1 2 3 4 5 6 7 8\n"),
    ("引数の順序", "f : a b ? a - b\nf 10 3\n"),
    ("深い式", "1 + (2 * (3 + (4 * (5 + 6))))\n"),
    ("割り算(字面)", "h : a ? a / 2\nh 9\n"),
    ("割り算(負)", "h : a ? a / 3\nh (0 - 7)\n"),
    ("割る数が負", "h : a ? a / -3\nh 7\n"),
    ("余り", "h : a ? a % 4\nh 13\n"),
    ("余り(負)", "h : a ? a % 4\nh (0 - 13)\n"),
    ("レジスタと同じ綴りの関数名", "x0 : n ? n + 1\nw1 : n ? x0 n * 2\nq4 : n ? w1 n\nsp : n ? q4 n\nsp 5\n"),
    ("命令と同じ綴りの関数名", "add : a b ? a + b\nmov : a ? add a 1\nret : a ? mov a * 2\nb : a ? ret a\nb 4\n"),
    ("fib", "fib : n ?\n\tn < 2 : n\n\t(fib (n - 1)) + (fib (n - 2))\nfib 15\n"),
    ("階乗", "fact : n ?\n\tn <= 1 : 1\n\tn * (fact (n - 1))\nfact 20\n"),
    ("階乗の溢れは罠", "fact : n ?\n\tn <= 1 : 1\n\tn * (fact (n - 1))\nfact 21\n"),
    ("末尾再帰(和)", "sum : n acc ?\n\tn = 0 : acc\n\tsum (n - 1) (acc + n)\nsum 5000 0\n"),
    ("末尾再帰(引き算のユークリッド)", "gcd : a b ?\n\ta = b : a\n\ta > b : gcd (a - b) b\n\tgcd a (b - a)\ngcd 1071 462\n"),
    ("末尾再帰の溢れ", "p : n acc ?\n\tn = 0 : acc\n\tp (n - 1) (acc * 3)\np 50 1\n"),
    ("複数の行", "f : n ?\n\tn = 0 : 100\n\tn > 5 : 200\n\tn < 0 : 300\n\t400\nf 3\n"),
    ("複数の行(0)", "f : n ?\n\tn = 0 : 100\n\tn > 5 : 200\n\tn < 0 : 300\n\t400\nf 0\n"),
    ("複数の行(大)", "f : n ?\n\tn = 0 : 100\n\tn > 5 : 200\n\tn < 0 : 300\n\t400\nf 9\n"),
    ("複数の行(負)", "f : n ?\n\tn = 0 : 100\n\tn > 5 : 200\n\tn < 0 : 300\n\t400\nf (0 - 9)\n"),
    ("!=", "f : a b ?\n\ta != b : 1\n\t0\nf 3 3\n"),
    ("!=(違う)", "f : a b ?\n\ta != b : 1\n\t0\nf 3 4\n"),
    (">=", "f : a b ?\n\ta >= b : 1\n\t0\nf 3 3\n"),
    ("負の比較", "f : a b ?\n\ta < b : a\n\tb\nf (0 - 3) (0 - 9)\n"),
    ("大きな数の比較", "f : a b ?\n\ta > b : 1\n\t0\nf 9223372036854775807 (0 - 9223372036854775807)\n"),
    ("連なった比較", "f : n ?\n\t0 < n < 10 : 1\n\t0\nf 5\n"),
    ("連なった比較(外)", "f : n ?\n\t0 < n < 10 : 1\n\t0\nf 15\n"),
    ("連なった比較(式)", "f : n ?\n\t(n - 1) < (n + 1) <= (n * 2) : 1\n\t0\nf 5\n"),
    ("連なった比較: 外れたら後ろの項は評価しない(溢れる項でも止まらない)", "f : n ?\n\t100 < n < (9223372036854775807 + n) : 1\n\t0\nf 5\n"),
    ("連なった比較: 後ろの項が評価されて溢れる", "f : n ?\n\t1 < n < (9223372036854775807 + n) : 1\n\t0\nf 5\n"),
    ("入れ子の分岐", "f : a b ?\n\ta < b :\n\t\ta < 0 : 1\n\t\t2\n\t3\nf 1 5\n"),
    ("条件に呼び出し", "sq : n ? n * n\nf : n ?\n\t(sq n) > 50 : 1\n\t0\nf 8\n"),
    ("分岐の値に呼び出し", "sq : n ? n * n\nf : n ?\n\tn > 0 : sq n\n\t0 - (sq n)\nf (0 - 4)\n"),
    ("相互に呼ぶ", "ev : n ?\n\tn = 0 : 1\n\tod (n - 1)\nod : n ?\n\tn = 0 : 0\n\tev (n - 1)\nev 10\n"),
    ("Collatz の歩数", "c : n s ?\n\tn = 1 : s\n\t(n - (n / 2) * 2) = 0 : c (n / 2) (s + 1)\n\tc (3 * n + 1) (s + 1)\nc 27 0\n"),
    ('`__`', '__\n'),
    ('__ + 3', '__ + 3\n'),
    ('3 + __', '3 + __\n'),
    ('__ - 5', '__ - 5\n'),
    ('5 - __', '5 - __\n'),
    ('__ * 4', '__ * 4\n'),
    ('__ / 2', '__ / 2\n'),
    ('6 / __', '6 / __\n'),
    ('-__', '-__\n'),
    ('__ + __', '__ + __\n'),
    ('比較の値(成り立つ)', '3 < 5\n'),
    ('比較の値(外れ)', '5 < 3\n'),
    ('連なった比較の値', '3 < 5 < 9\n'),
    ('四つの連なり', '1 < 2 < 3 < 4\n'),
    ('連なり(外れ)', '3 < 2 < 4\n'),
    ('__ との比較', '__ < 5\n'),
    ('__ との比較(右)', '5 < __\n'),
    ('= の値', '3 = 3\n'),
    ('= の連なり', '5 = 5 = 5\n'),
    ('__ = __', '__ = __\n'),
    ('| 左が値', '3 | 4\n'),
    ('| 左が偽', '(5 < 3) | 4\n'),
    ('| 両方偽', '(5 < 3) | (6 < 4)\n'),
    ('| の連なり', '(5 < 3) | 7 | 8\n'),
    ('| は右を評価しない', '3 | (9223372036854775807 + 1)\n'),
    ('| 右を評価して溢れる', '(5 / 0) | (9223372036854775807 + 1)\n'),
    ('& 左が値', '3 & 4\n'),
    ('& 左が偽', '(5 < 3) & 4\n'),
    ('& 真', '(3 < 5) & 4\n'),
    ('& の連なり', '1 & 2 & 3\n'),
    ('& は右を評価しない', '(5 < 3) & (9223372036854775807 + 1)\n'),
    ('0 で割る', '5 / 0\n'),
    ('0 で割った商に足す', '(5 / 0) + 2\n'),
    ('0 の余り', '7 % 0\n'),
    ('0 から __ を引く', '0 - (5 / 0)\n'),
    ('0 - 0 で割る', '7 / (0 - 0)\n'),
    ('負の商', '(0 - 7) / 2\n'),
    ('負の余り', '(0 - 7) % 4\n'),
    ('__ の余り', '__ % 3\n'),
    ('既定の行が無い(外れ)', 'f : n ?\n\tn < 2 : n\n\tn > 5 : 1\nf 3\n'),
    ('既定の行が無い(当たり)', 'f : n ?\n\tn < 2 : n\n\tn > 5 : 1\nf 1\n'),
    ('変数で割る', 'd : a b ? a / b\nd 17 5\n'),
    ('変数で割る(0)', 'd : a b ? a / b\nd 17 0\n'),
    ('変数の余り', 'd : a b ? a % b\nd 17 5\n'),
    ('変数の余り(0)', 'd : a b ? a % b\nd 17 0\n'),
    ('引数が __ なら呼び全体が __', 'g : a b ? a + b\ng (5 / 0) 3\n'),
    ('右の引数が __', 'g : a b ? a + b\ng 3 (5 / 0)\n'),
    ('__ を直に渡す', 'g : a b ? a + b\ng __ 3\n'),
    ('本体が引数を使わなくても __', 'g : a ? 7\ng (5 < 3)\n'),
    ('引数の評価は全部済む(溢れる)', 'g : a b ? a + b\ng (5 / 0) (9223372036854775807 + 1)\n'),
    ('真の比較を渡す', 'k : a ? a * 2\nk (3 < 5)\n'),
    ('__ を返す関数の結果に足す', 'h : a ? a < 3\n(h 5) + 5\n'),
    ('__ を返す関数(値)', 'h : a ? a < 3\n(h 1) + 5\n'),
    ('再帰の外れは __', 'f : n ?\n\tn = 0 : 5\nf 1\n'),
    ('末尾呼び出しの引数が __', 'g : n acc ?\n\tn = 0 : acc\n\tg (n - 1) (n < 3)\ng 5 7\n'),
    ('末尾呼び出し(__ にならない)', 'g : n acc ?\n\tn = 0 : acc\n\tg (n - 1) (acc + n)\ng 10 0\n'),
    ('条件が仮引数', 'f : a ?\n\ta : 1\n\t0\nf 4\n'),
    ('条件が括りの比較', 'f : n ?\n\t(n < 3) : 1\n\t0\nf 1\n'),
    ('条件が |(当たり)', 'f : n ?\n\t(n < 3) | (n > 8) : 1\n\t0\nf 9\n'),
    ('条件が |(外れ)', 'f : n ?\n\t(n < 3) | (n > 8) : 1\n\t0\nf 5\n'),
    ('条件が &', 'f : n ?\n\t(n > 3) & (n < 8) : 1\n\t0\nf 5\n'),
    ('条件が & (外れ)', 'f : n ?\n\t(n > 3) & (n < 8) : 1\n\t0\nf 9\n'),
    ('__ の定数', 'a : __\na + 3\n'),
    ('__ の定数(そのまま)', 'a : __\na\n'),
    ('0 の商は __ なので足しても残る', 'p : x ? (x / 0)\n(p 3) + 1\n'),
    ('__ を返す関数との比較', 'q : a ? a / 0\nf : n ?\n\t(q n) < 3 : 1\n\t0\nf 1\n'),
    ('比較の値を返す関数', 'lt : a b ? a < b\nlt 2 9\n'),
    ('比較の値を返す関数(外れ)', 'lt : a b ? a < b\nlt 9 2\n'),
    ('比較の値の連なり(式)', 'f : n ? (n - 1) < n < (n + 1)\nf 5\n'),
    ('負の数の比較の値', 'f : a b ? a < b\nf (0 - 9) (0 - 3)\n'),
    ('min', 'min : a b ? (a < b) | b\nmin 4 9\n'),
    ('min(逆)', 'min : a b ? (a < b) | b\nmin 9 4\n'),
    ('max', 'max : a b ? (a > b) | b\nmax 4 9\n'),
    ('abs', 'abs : a ? (a < 0) & (0 - a) | a\nabs (0 - 6)\n'),
    ("定数の名前", "k : 5\nk * k + 1\n"),
    ("大きな字面", "9223372036854775807\n"),
    ("大きな負の字面", "-9223372036854775807\n"),
    ("INT64_MAX - 1", "9223372036854775807 - 1\n"),
    ("大きな和(溢れない)", "4611686018427387904 + 4611686018427387903\n"),
    ("和の溢れは罠", "9223372036854775807 + 1\n"),
    ("和が INT64_MIN に着くのも罠", "-9223372036854775807 - 1\n"),
    ("負の側の溢れ", "(0 - 9223372036854775807) + (0 - 2)\n"),
    ("積の溢れは罠", "3037000500 * 3037000500\n"),
    ("積が溢れない境界", "3037000499 * 3037000499\n"),
    ("積が INT64_MIN に着くのも罠", "-4611686018427387904 * 2\n"),
    ("負 × 負", "(0 - 123456789) * (0 - 987654321)\n"),
    ("関数の中の溢れ", "f : a b ? a * b\nf 4611686018427387904 2\n"),
    ("引数を渡して溢れ", "f : a b ? a + b\nf 9223372036854775807 1\n"),
    ("0 を掛ける", "f : a ? a * 0\nf 9223372036854775807\n"),
    ("符号反転は溢れない", "g : x ? -x\ng 9223372036854775807\n"),
    # ---- == / !== と、`__` を含む != ----
    ("== 等しい", "5 == 5\n"), ("== 等しくない", "5 == 6\n"), ("== 右が __", "5 == __\n"), ("== 左が __", "__ == 5\n"),
    ("!= 右が __", "5 != __\n"), ("!= 左が __", "__ != 5\n"), ("!= 両方 __", "__ != __\n"),
    ("!== 右が __", "5 !== __\n"), ("!== 左が __", "__ !== 5\n"), ("!== 違う", "5 !== 6\n"), ("!== 同じ", "5 !== 5\n"),
    ("!= 割り算が __", "(5 / 0) != 3\n"), ("!= 両方割り算が __", "(5 / 0) != (7 / 0)\n"),
    ("== を条件に", "f : a b ?\n\ta == b : 1\n\t0\nf 3 3\n"),
    ("!== を条件に", "f : a b ?\n\ta !== b : 1\n\t0\nf 3 3\n"),
    ("!= の連なり", "1 < 2 != 3\n"), ("!= の連なり 外れ", "1 < 2 != 2\n"),
    ("__ の != を条件に", "u : __\nf : a ?\n\tu != a : 7\n\t0\nf 4\n"),
    ("二重の ==", "(3 == 3) == 3\n"),
    # ---- 第 4 段: リスト(Int の要素。読むだけ) ----
    ("添字 0", "l : 10 20 30\nl ' 0\n"),
    ("添字 末尾", "l : 10 20 30\nl ' 2\n"),
    ("負の添字 -1", "l : 10 20 30\nl ' (0 - 1)\n"),
    ("負の添字 -長さ", "l : 10 20 30\nl ' (0 - 3)\n"),
    ("負の添字 範囲の外", "l : 10 20 30\nl ' (0 - 4)\n"),
    ("範囲の外(正)", "l : 10 20 30\nl ' 3\n"),
    ("巨大な添字", "l : 10 20 30\nl ' 9223372036854775807\n"),
    ("巨大な負の添字", "l : 10 20 30\nl ' (0 - 9223372036854775807)\n"),
    ("添字が __", "l : 10 20 30\nl ' __\n"),
    ("長さ", "l : 10 20 30 40\n||l||\n"),
    ("長さ × 2", "l : 10 20 30 40\n||l|| * 2\n"),
    ("負の要素", "l : -5 7 -9\n(l ' 0) + (l ' 2)\n"),
    ("別名", "l : 1 2 3\nm : l\nm ' 1\n"),
    ("字面を直接", "f : xs i ? xs ' i\nf (7 8 9) 1\n"),
    ("関数にリストを渡す", "g : xs i ? xs ' i\nl : 4 5 6\ng l 2\n"),
    ("関数の長さ", "n : xs ? ||xs||\nl : 4 5 6\nn l\n"),
    ("2 つのリスト", "h : a b i ? (a ' i) + (b ' i)\nx : 1 2 3\ny : 10 20 30\nh x y 2\n"),
    ("リストを受け渡す", "g : xs i ? xs ' i\nw : xs i ? g xs i\nl : 4 5 6\nw l 1\n"),
    ("リストの合計(末尾再帰)", "sum : xs i acc ?\n\ti >= ||xs|| : acc\n\tsum xs (i + 1) (acc + (xs ' i))\nl : 1 2 3 4 5 6 7 8 9 10\nsum l 0 0\n"),
    ("範囲の外は __ で続く", "l : 10 20 30\n(l ' 5) | 99\n"),
    ("引数に __ の添字", "g : xs i ? xs ' i\nl : 4 5 6\ng l (l ' 9)\n"),
    ("リスト定数を関数の中で", "l : 3 1 4 1 5\nf : i ? l ' i\nf 4\n"),
    ("同じ中身は畳む", "a : 1 2 3\nb : 1 2 3\n(a ' 0) + (b ' 2)\n"),
]

for name, src in CASES:
    try: text = asm_of(src)
    except sign_asm.AsmError as e:
        check("出せるはず: " + name, "断り: %s" % e, "出力"); continue
    check(name, run_asm(text), interp(src))

# ---- 名指しで断る形 ----
REFUSE = [
    ("値域の外の字面", "9223372036854775808\n", "値域"),
    ("引数が足りない", "f : a b ? a + b\nf 1\n", "部分適用"),
    ("引数が多い", "f : a ? a + 1\nf 1 2\n", "余った"),
    ("関数を値に", "f : a ? a + 1\nf\n", "値として"),
    ("文字と数の比べ", "s : `abc`\n(s ' 0) == 97\n", "同士"),
    ("文字列の比べ", "s : `abc`\ns == s\n", "同士"),
    ("関数の値の適用", "f : a ? a\n(f) 3\n", None),
    ("文字列のエスケープ", "s : `a\\nb`\n||s||\n", "エスケープ"),
    ("日本語の文字列", "s : `日本`\n||s||\n", "ASCII"),
    ("文字列を返す関数", "f : s ? s\nf `abc`\n||(f `abc`)||\n", "返す"),
    ("文字列に足す", "s : `abc`\ns + 1\n", "値として"),
    ("未定義の名前", "zzz + 1\n", "識別子"),
    ("リストを足す", "l : 1 2 3\nl + 1\n", "リスト"),
    ("仮引数のスライスの展開(外れると __)", "f : xs ys ? (xs ' [0 ~ 1])~ ys~\nf (1 2 3) (4 5)\n", "範囲の外になりうる"),
    ("定数の外れるスライスの展開", "xs : 1 2 3\nys : 4 5\n(xs ' [0 ~ 5])~ ys~\n", "範囲の外になりうる"),
    ("終端の無い規則", "f : n ? [n ~+ 1]\n(f 5) ' 2\n", "終端の無い"),
    ("端が __ になりうる規則", "f : n ? [1 ~ 10 / n]\nf 2\n", "`__` になりうる"),
    ("規則の展開", "mk : n ? [1 ~ n]\nf : r ? 0 r~ 9\nf (mk 3)\n", "規則の展開"),
    ("規則のスライス", "mk : n ? [1 ~ n]\n(mk 6) ' [1 ~ 2]\n", "スライス"),
    ("規則を返す分岐に既定の行が無い", "h : a n ?\n\ta > 0 : [1 ~ n]\nh 1 4\n", "既定の行"),
    ("規則とリストの混在", "mk : n ? [1 ~ n]\nf : r ? ||r||\n(f (mk 3)) + (f (1 2 3))\n", "種類の違う"),
    ("規則の足し算", "mk : n ? [1 ~ n]\n(mk 3) + 1\n", "値として"),
    ("逆順のスライス", "xs : 1 2 3 4 5\nxs ' [3 ~ 1]\n", "逆順"),
    ("実行時の端のスライス", "f : xs a b ? xs ' [a ~ b]\nf (1 2 3) 0 1\n", "端が定数"),
    ("負の端のスライス", "xs : 1 2 3 4 5\nxs ' [(0 - 2) ~ (0 - 1)]\n", "負"),
    ("大きすぎる範囲", "[0 ~ 100000]\n", "大きすぎ"),
    ("器の引数を変える自己呼び出し", "g : xs ?\n\t||xs|| > 3 : xs~ 1\n\tg (xs ' [1 ~ 2])\ng (1 2 3 4 5)\n", "見積もり"),
    ("ループと置き場の呼びが同居", "f : a ? a (a * 2)\nlen2 : a acc ?\n\ta <= 0 : acc\n\tlen2 (a - 1) (acc + ||f a||)\nlen2 3 0\n", "ループ"),
    ("入れ子: 展開とリストの混在", "f : xs ? (1 2) xs~\nf (1 2)\n", "揃っていません"),
    ("入れ子: 深さの揃わない字面", "m : [1 [2 [3 4]]]\nm\n", "深さが揃っていません"),
    ("入れ子: 2 段と 3 段が同じ組に", "a : [[1 2] [3 4]]\nb : [[[1 2] [3 4]] [[5 6] [7 8]]]\n||a|| + ||b||\n", "深さの違う"),
    ("節 文字列の畳みは断る", "f : s ? [+] s\nf `ab`\n", "種類の違う物"),
    ("入れ子: 混ざる入れ子の要素を返す", "f : m i ? m ' i\nf [1 [2 3]] 0\n", "混ざる入れ子の使い方"),
    ("入れ子: 混ざる入れ子の要素を引数へ", "m : [1 [2 3]]\nh : xs ? ||xs||\nh (m ' 1)\n", "混ざる入れ子の使い方"),
    ("入れ子: 混ざる入れ子の要素を Int として足す", "m : [1 [2 3]]\n(m ' 0) + 1\n", "値として"),
    ("入れ子: 混ざる入れ子の展開(仮引数)", "f : m ? 0 m~\nf [1 [2 3]]\n", "展開 `m~`(仮引数・呼びの結果)"),
    ("入れ子: 混ざる入れ子がある組での、仮引数の入れ子の展開", "m : [1 [2 3]]\nf : m ? 0 m~\nf [[1 2] [3 4]]\n", "結果の種類が静的に決まらない"),
    ("入れ子: 文字列とリストが混ざる入れ子の取り出し", "m : [`ab` , [1 2]]\nm ' 0\n", "文字列とリストが混ざる"),
    ("入れ子: 文字列の入れ子と Int の入れ子が同じ組に", "m : [`ab` , `cd`]\nn : [[1 2] [3 4]]\n||m|| + ||n||\n", "同じ組に"),
    ("入れ子: 外れうるスライスの要素", "f : xs ? xs (xs ' [5 ~ 6])\nf (1 2)\n", "範囲の外になりうる"),
    ("入れ子: `__` を返しうる組み立ての結果を要素に", "mk : a ?\n\ta > 0 : a a\nf : a ? (mk a) (1 2)\nf 3\n", "`__` を返しうる"),
    ("入れ子: 要素に置く関数の引数が __ になりうる", "mk : a b ? a b\nf : a ? (mk a (1 / a)) (1 2)\nf 2\n", "引数が"),
    ("入れ子: 入れ子のスライスの展開", "m : (1 2) (3 4) (5 6)\nf : a ? a (m ' [0 ~ 1])~\nf 0\n", "範囲の外になりうる"),
    ("食う: 始まりが定数でない", "f : xs n ? xs ' n~\nf (1 2 3) 1\n", "定数"),
    ("食う: 1 つの枝で 2 回", "f : xs ?\n\t||xs|| = 0 : __\n\t(f (xs ' 1~))~ (f (xs ' 2~))~ 0\nf (1 2 3)\n", "2 回"),
    ("食う: 器を撒きながら食う(二次)", "f : xs ?\n\t||xs|| = 0 : __\n\txs~ (f (xs ' 1~))~\nf (1 2 3)\n", "二次"),
    ("食う: 食う引数が 2 つ", "f : xs ys ?\n\t||xs|| = 0 : __\n\t0 (f (xs ' 1~) (ys ' 1~))~\nf (1 2) (3 4)\n", "収束"),
    ("食う: 入れ子の要素に(__ を返しうる)", "dup : xs ?\n\t||xs|| = 0 : __\n\t(xs ' 0) (xs ' 0) (dup (xs ' 1~))~\nf : xs ? (dup xs) (1 2)\nf (4 5)\n", "__"),
    ("累積: 食わずに伸ばす", "f : xs acc n ?\n\tn = 0 : acc\n\tf xs (acc~ n) (n - 1)\nf (1 2) (3 3) 4\n", "食って"),
    ("累積: 前へ足す", "f : xs acc ?\n\t||xs|| = 1 : acc~ (xs ' 0)\n\tf (xs ' 1~) ((xs ' 0) acc~)\nf (1 2 3) (5 5)\n", "累積を後ろへ"),
    ("累積: 伸ばしながら器も撒く", "f : xs acc ?\n\t||xs|| = 1 : acc\n\tf (xs ' 1~) (acc~ xs~)\nf (1 2 3) (5 5)\n", "累積を後ろへ"),
    ("食う: 末尾の切り出しの展開", "f : xs ? 0 (xs ' 1~)~\nf (1 2 3)\n", "末尾の切り出し"),
    ("食う: 食わない再帰", "f : xs n ?\n\tn = 0 : __\n\t(xs ' 0) (f xs (n - 1))~\nf (1 2 3) 3\n", None),
    ("食う: 尽きうる先頭を要素に", "f : xs ?\n\t(xs ' 1~) (xs ' 0)\nf (1 2 3)\n", None),
    ("相互再帰: 食わずに呼ぶ辺がある", "a : xs ?\n\t||xs|| = 1 : (xs ' 0) 1\n\t(xs ' 0) (b xs)~\nb : xs ?\n\t||xs|| = 1 : (xs ' 0) 2\n\t(xs ' 0) (a (xs ' 1~))~\na (1 2 3)\n", "収束"),
    ("累積・輪: 文字列の累積に数を足す", "f : s acc ?\n\t||s|| = 1 : acc\n\tf (s ' 1~) (acc 0)\nf `abc` `x`\n", "足せる"),
    ("段16b: 入れ子を食いながら全体も撒く(二次)", "g : m ?\n\t||m|| = 1 : (m ' 0)~ 99\n\tm~ 0 (g (m ' 1~))~\ng ((1 2) (3 4) (5 6 7))\n", "二次"),
    ("段18: 同じ器を 2 つの位置へ渡す輪", "a : xs ys ?\n\t||xs|| = 1 : (xs ' 0) 100\n\t(xs ' 0) (b (xs ' 1~) (xs ' 1~))~\nb : us vs ?\n\t||us|| = 1 : (us ' 0) 200\n\t(us ' 0) 0 (a us (us ' 1~))~\na (1 2 3) (4 5 6 7)\n", None),
    ("段21: 輪を回るたびに別の輪を呼ぶ(二次)", "p : xs ?\n\t||xs|| < 3 : (xs ' 0) 5\n\t(xs ' 0) (c xs)~ (q (xs ' 1~))~\nq : xs ?\n\t||xs|| < 3 : (xs ' 0) 9\n\t(xs ' 0) 1 (p (xs ' 1~))~\nc : xs ?\n\t||xs|| = 1 : (xs ' 0) 300\n\t(xs ' 0) 0 (d (xs ' 1~))~\nd : xs ?\n\t||xs|| = 1 : (xs ' 0) 400\n\t(xs ' 0) 0 0 0 (c (xs ' 1~))~\np (1 2 3 4 5 6 7 8)\n", "二次"),
    ('段29: 伸びる器に頼る新しい器は出せない', "f : xs ys ?\n\t||xs|| = 1 : ys~ (xs ' 0)\n\tf (xs ' 1~) ((xs ' 0) ys~)\nf (4 5 6) (1 2)\n", "器の引数を変えています"),
    ('段33: 内側頼みの位置の器に頼る新しい器は出さない(伸びる)', "a : m ys ?\n\t||m|| < 3 : ys~ 1\n\tb (m ' 2~) (ys~ (m ' 0)~)\nb : m ys ?\n\t||m|| < 3 : ys~ 2\n\ta (m ' 2~) ((m ' 1)~ 8)\na ((1 2) (3 3) (4 5 6) (7 7) (8 9) (1 1)) (5 5)\n", "収束しません"),
    ('段23: 入れ子で 1 個だけ残りうる', "f : m ? (m ' 0) (m ' 5) (m ' 1)\nf ((1 2) (3 4) (5 6))\n", '2 個未満'),
    ('段23: 入れ子で 1 個だけ残りうる(2 つ)', "f : m ? (m ' 0) (m ' 5)\nf ((1 2) (3 4) (5 6))\n", '2 個未満'),
    ('段23: 文字 2 個が消えうる', "f : s ? (s ' 0) (s ' 5) (s ' 1)\nf `abc`\n", '文字 2 個以上'),
    ('段23: 文字 2 個の並置で 1 つ消えうる', "f : s ? (s ' 0) (s ' 5)\nf `abc`\n", '文字 2 個以上'),
    ('段24: 入れ子の内側で消えうる(2 個未満)', "f : xs ? (xs ' 0 xs ' 5) (xs ' 1 xs ' 0)\nf (1 2 3)\n", "2 個以上"),
    ('段26: 範囲外で __ になりうる関数の結果は展開できない', "pick : xs ?\n\t||xs|| > 2 : xs\nf : xs ? (pick xs)~ 9\nf (4 5 6)\n", "見積もれません"),
    ('段26: 末尾を返す(尽きると __)関数の結果は展開できない', "rest : xs ? xs ' 1~\nf : xs ? (rest xs)~ 9\nf (4 5 6)\n", "見積もれません"),
    ("入れ子: 展開だけの値", "m : (1 2) (3 4)\nm~\n", None),
    ("入れ子: 外れうる添字の取り出しを要素に", "m : (1 2) (3 4 5)\nf : i ? (m ' i) (1 2)\nf 1\n", "範囲の外になりうる"),
    ("入れ子: 要素が __ になりうる", "f : a ? (a (1 / a)) (a a)\nf 2\n", "`__` になりうる"),
    ("入れ子: 入れ子を足す", "m : (1 2) (3 4 5)\nm + 1\n", "値として"),
    ("連結: リストと数の並置", "f : s xs ? xs s 0\nf `ab` (1 2)\n", "文字列の連結"),
    ("連結: 文字だけの並置", "s : `ab`\n(s ' 0) (s ' 1)\n", "文字列の連結"),
    ("連結: 全部が消えうる", "f : s i ? (s ' i) (s ' i) \nf `ab` 5\n", "文字列の連結"),
    ("連結: 展開", "f : s ? s~ s\nf `ab`\n", "文字列の連結"),
    ("連結: リストとの並置", "f : s xs ? s xs\nf `ab` (1 2)\n", "文字列の連結"),
    ("連結: 引数を変える再帰", "f : s n ?\n\tn = 0 : s\n\tf (s `-`) (n - 1)\nf `a` 3\n", "食って"),
    ("枝の種類が違う", "f : a ?\n\ta > 0 : (1 2)\n\t5\nf 1\n", "揃って"),
    ("Int とリストが同じ仮引数", "f : a ? a\nl : 1 2\nf l + f 3\n", None),
]
REFUSE += [
    ('段34: 累積をそのまま内側の要素に置いて返す(作業領域が消える)', "f : xs ys ?\n\t||xs|| = 1 : ys (xs ' 0 7)\n\tf (xs ' 1~) (ys~ (xs ' 0))\nf (4 5 6) (1 2)\n", "作業領域"),
    ('段35: 輪の片方だけが累積を伸ばす', "a : xs ys ?\n\t||xs|| < 3 : (ys~ (xs ' 0)) (xs ' 0 7)\n\tb (xs ' 2~) (ys~ (xs ' 0))\nb : xs ys ?\n\t||xs|| < 3 : (ys~ (xs ' 0)) (xs ' 0 8)\n\ta (xs ' 2~) ys\na (4 5 6 7 8 9 1 2 3 4) (1 2)\n", "収束しません"),
    ('段34: 内側の要素が再帰の入れ子結果を展開する(二次)', "g : xs ?\n\t||xs|| = 1 : (xs ' 0 1) (xs ' 0 2)\n\t((g (xs ' 1~))~ (xs ' 0)) (9 9)\ng (4 5 6 7)\n", "収束しません"),
]

REFUSE += [
    ('段40: 条件が足りず範囲内と言えない取り出しは断る', "a : xs ys ?\n\t||xs|| < 3 : ys~ 1\n\ta (xs ' 2~) (ys~ (xs ' 3))\na (4 5 6 7 8 9 1 2 3 4) (1 2)\n", "__"),
]
REFUSE += [
    ('段41: 比べた長さの差だけでは範囲内と言えない取り出しは断る', "a : xs ys ?\n\t||xs|| <= ||ys|| : ys~ 1\n\ta (xs ' 1~) (ys~ (xs ' 2))\na (4 5 6 7 8 9 1 2 3 4) (1 2)\n", "__"),
]
REFUSE += [
    ('段42: 片側の条件だけでは範囲内と言えない要素の添字は断る', "a : xs ys ?\n\t||xs|| < 3 : ys~ 1\n\t(xs ' 0) < ||xs|| : a (xs ' 1~) (ys~ (xs ' (xs ' 0)))\n\ta (xs ' 1~) (ys~ 9)\na (4 5 6 7 8 9 1 2 3 0) (1 2)\n", "__"),
]
REFUSE += [
    ('段43: n が器の長さと一緒に減らない(等式が保たれない)なら範囲内と言えず断る', "a : xs ys n ?\n\tn < 3 : ys~ 1\n\ta (xs ' 1~) (ys~ (xs ' (n - 2))) (n - 2)\na (4 5 6 7 8 9 1 2 3 4) (1 2) 10\n", "__"),
]
os.environ["SIGN_ESTIMATE"] = "0"          # 断りの試験は『証明できるものだけ通す』モード(既定の見積もりモードでは、回る回数が証明できない形も見積もりで通る)
for name, src, key in REFUSE:
    try:
        asm_of(src); got = "出てしまった"
    except sign_asm.AsmError as e:
        got = "断り" if key is None or key in str(e) else "断り(理由が違う): %s" % e
    except Exception as e:
        got = "例外 %s: %s" % (type(e).__name__, e)
    check("断る: " + name, got, "断り")
os.environ.pop("SIGN_ESTIMATE", None)

# ---- 第 5 段: 文字列(ASCII・1 バイト。Linux の足場で印字まで) ----
def interp_out(src):
    d = tempfile.mkdtemp(); p = os.path.join(d, "t.sn"); open(p, "w", encoding="utf-8").write(src)
    r = subprocess.run([sys.executable, os.path.join(HERE, "sign.py"), p], capture_output=True, text=True, timeout=60)
    return r.stdout

STR_CASES = [
    ("文字列を印字", "s : `hello`\ns\n"),
    ("別名", "s : `hello`\nt : s\nt\n"),
    ("空白を含む", "s : `hello world`\ns\n"),
    ("長さ", "s : `hello`\n||s||\n"),
    ("文字 先頭", "s : `hello`\ns ' 0\n"),
    ("文字 末尾", "s : `hello`\ns ' 4\n"),
    ("文字 負", "s : `hello`\ns ' (0 - 1)\n"),
    ("文字 負の端", "s : `hello`\ns ' (0 - 5)\n"),
    ("文字 範囲外", "s : `hello`\ns ' 5\n"),
    ("文字 負の範囲外", "s : `hello`\ns ' (0 - 6)\n"),
    ("文字 巨大", "s : `hello`\ns ' 9223372036854775807\n"),
    ("文字 __ の添字", "s : `hello`\ns ' __\n"),
    ("引数の文字列の長さ", "n : s i ? ||s|| + i\nn `abcd` 10\n"),
    ("定数を渡す", "s : `abc`\nn : t ? ||t|| * 2\nn s\n"),
    ("文字列を受け渡す", "n : t ? ||t||\nw : t ? n t\nw `abcde`\n"),
    ("文字の取り出しを関数の中で", "f : t i ? t ' i\nf `hello` 1\n"),
    # ---- 第 7 段: 組み立てずに返す(リスト・文字列・文字。x0/x1 の {ptr, len}) ----
    ("リストを印字", "l : 10 20 30\nl\n"),
    ("負の要素の印字", "l : -5 0 7\nl\n"),
    ("定数のリストを返す", "l : 10 20 30\nf : a ? l\nf 1\n"),
    ("引数のリストをそのまま返す", "g : xs ? xs\ng (4 5 6)\n"),
    ("枝で選んで返す 1", "pick : a xs ys ?\n\ta > 0 : xs\n\tys\npick 1 (1 2 3) (4 5 6)\n"),
    ("枝で選んで返す 2", "pick : a xs ys ?\n\ta > 0 : xs\n\tys\npick 0 (1 2 3) (4 5 6)\n"),
    ("既定の行が無いと __", "f : a ?\n\ta > 3 : (7 8)\nf 1\n"),
    ("既定の行が無くて成り立つ", "f : a ?\n\ta > 3 : (7 8)\nf 4\n"),
    ("返したリストの要素", "l : 10 20 30\nf : a ? l\n(f 1) ' 2\n"),
    ("返したリストの長さ", "l : 10 20 30\nf : a ? l\n||f 1||\n"),
    ("返したリストが __ の長さ", "f : a ?\n\ta > 3 : (7 8)\n||f 1||\n"),
    ("返したリストが __ の要素", "f : a ?\n\ta > 3 : (7 8)\n(f 1) ' 0\n"),
    ("返したリストを渡す", "n : xs ? ||xs||\npick : a xs ys ?\n\ta > 0 : xs\n\tys\nn (pick 1 (1 2) (3 4 5))\n"),
    ("返したリストを関数へ(要素)", "g : xs i ? xs ' i\nl : 5 6 7\nf : a ? l\ng (f 1) 2\n"),
    ("返したリストが __ なら呼び全体が __", "h : xs ? ||xs||\nf : a ?\n\ta > 3 : (7 8)\nh (f 1)\n"),
    ("再帰の末尾でリストを返す", "go : xs i ?\n\ti >= 5 : xs\n\tgo xs (i + 1)\ngo (4 5 6) 0\n"),
    ("文字列を返す", "p : `pos`\nn : `neg`\nf : a ?\n\ta > 0 : p\n\tn\nf 1\n"),
    ("文字列を返す 2", "p : `pos`\nn : `neg`\nf : a ?\n\ta > 0 : p\n\tn\nf 0\n"),
    ("文字列を引数のまま返す", "g : s ? s\ng `abc`\n"),
    ("返した文字列の長さ", "g : s ? s\n||g `abcd`||\n"),
    ("返した文字列の文字", "g : s ? s\n(g `abcd`) ' 2\n"),
    ("文字を返す", "f : s i ? s ' i\nf `hello` 1\n"),
    ("文字を返す 範囲外", "f : s i ? s ' i\nf `hello` 9\n"),
    ("文字の字面を枝で返す", "f : a ?\n\ta > 0 : \\y\n\t\\n\nf 1\n"),
    ("文字の字面を枝で返す 2", "f : a ?\n\ta > 0 : \\y\n\t\\n\nf 0\n"),
    ("返した文字を比べる", "f : s i ? s ' i\n(f `hello` 1) == \\e\n"),
    ("返した文字を条件に", "f : s i ? s ' i\nm : s ?\n\t(f s 0) == \\h : 1\n\t0\nm `hello`\n"),
    ("文字を返す枝で __", "f : s i ?\n\ti > 2 : s ' i\nf `hello` 1\n"),
    # ---- 第 7 段 b: 要素を組み立てて返す(x8 = 置き場、x15 = 入る個数。呼ぶ側が sub sp で取る) ----
    ("組み立てて返す", "f : a ? a * 2 a + 1\nf 5\n"),
    ("組み立てて返す 3 個", "f : a ? a a (a + 1)\nf 2\n"),
    ("組み立ての要素 負", "f : a ? (0 - a) a\nf 7\n"),
    ("組み立てた要素を取り出す", "f : a ? a * 2 a + 1\n(f 5) ' 1\n"),
    ("組み立てた長さ", "f : a ? a a (a + 1)\n||f 2||\n"),
    ("組み立てて足す", "f : a ? a * 2 a + 1\n((f 5) ' 0) + ((f 6) ' 1)\n"),
    ("同じ関数で 2 回置き場を取る", "f : a ? a a (a + 1)\nh : a ? ||f a|| + ((f a) ' 2)\nh 4\n"),
    ("枝で組み立てる", "f : a ?\n\ta > 0 : a (a * 2)\n\t(0 - a) 0\nf 3\n"),
    ("枝で組み立てる 2", "f : a ?\n\ta > 0 : a (a * 2)\n\t(0 - a) 0\nf (0 - 3)\n"),
    ("枝で組み立てるか、定数か", "l : 9 8 7\nf : a ?\n\ta > 0 : a (a * 2)\n\tl\nf 0\n"),
    ("既定の行が無い組み立て", "f : a ?\n\ta > 0 : a (a * 2)\nf 0\n"),
    ("組み立てを下へ渡す(そのまま返す)", "f : a ? a (a * 2)\ng : a ? f (a + 1)\ng 4\n"),
    ("二段に渡す", "f : a ? a (a * 2)\ng : a ? f (a + 1)\nk : a ? g (a + 1)\nk 4\n"),
    ("再帰で最後に組み立てる", "f : a ?\n\ta <= 0 : 1 2\n\tf (a - 1)\nf 5\n"),
    ("組み立てた器を関数へ渡す", "n : xs ? ||xs||\nf : a ? a a a\nn (f 1)\n"),
    ("組み立てた器を関数の要素へ", "g : xs i ? xs ' i\nf : a ? a * 2 a * 3\ng (f 5) 1\n"),
    ("文字列とリストの引数", "h : t l ? ||t|| + (l ' 1)\nh `abc` (5 6 7)\n"),
    ("文字列の長さで再帰", "cnt : t i ?\n\ti >= ||t|| : i\n\tcnt t (i + 1)\ncnt `abcdef` 0\n"),
    ("文字の字面", "\\a\n"),
    ("1 字の文字列", "s : `a`\ns\n"),
    ("文字 == 等しい", "s : `hello`\n(s ' 0) == \\h\n"),
    ("文字 == 違う", "s : `hello`\n(s ' 0) == \\i\n"),
    ("文字 == 範囲外", "s : `hello`\n(s ' 9) == \\h\n"),
    ("文字 == 右が範囲外", "s : `hello`\n\\h == (s ' 9)\n"),
    ("文字 != 範囲外", "s : `hello`\n(s ' 9) != \\h\n"),
    ("文字 != 左が範囲外", "s : `hello`\n\\h != (s ' 9)\n"),
    ("文字 != 両方範囲外", "s : `hello`\n(s ' 9) != (s ' 8)\n"),
    ("文字 !== 違う", "\\h !== \\i\n"), ("文字 !== 同じ", "\\h !== \\h\n"),
    ("文字 <", "\\h < \\i\n"), ("文字 < 外れ", "\\i < \\h\n"), ("文字 <=", "\\h <= \\h\n"),
    ("文字 >", "\\i > \\h\n"), ("文字 >=", "\\h >= \\i\n"), ("文字 =", "\\h = \\h\n"),
    ("文字 連なり", "\\h < \\i < \\j\n"), ("文字 連なり 外れ", "\\h < \\i < \\i\n"),
    ("文字 二重 ==", "s : `hello`\n((s ' 0) == \\h) == \\h\n"),
    ("文字 範囲外の <", "s : `hello`\n(s ' 9) < \\z\n"),
    ("文字 2 つの添字", "s : `hello`\n(s ' 1) < (s ' 2)\n"),
    ("文字を数える", "cnt : t i acc ?\n\ti >= ||t|| : acc\n\t(t ' i) == \\l : cnt t (i + 1) (acc + 1)\n\tcnt t (i + 1) acc\ncnt `hello world` 0 0\n"),
    ("文字の範囲で数える", "cnt : t i acc ?\n\ti >= ||t|| : acc\n\t(t ' i) >= \\a < \\m : cnt t (i + 1) (acc + 1)\n\tcnt t (i + 1) acc\ncnt `hello world` 0 0\n"),
    ("文字の != を数える", "cnt : t i acc ?\n\ti >= ||t|| : acc\n\t(t ' i) != \\l : cnt t (i + 1) (acc + 1)\n\tcnt t (i + 1) acc\ncnt `hello` 0 0\n"),
    ("文字列が空に近い端", "cnt : t i acc ?\n\ti >= ||t|| : acc\n\t(t ' (0 - 1)) == \\o : cnt t (i + 1) (acc + 1)\n\tcnt t (i + 1) acc\ncnt `hello` 0 0\n"),
]
# ---- 第 8 段: 範囲・スライス・連結(上界 = 定数 + Σ 係数 × ||器||) ----
STR_CASES += [
 ("範囲", "[1 ~ 5]\n"), ("範囲 逆", "[5 ~ 1]\n"), ("範囲 刻み", "[1 ~+ 2 ~ 9]\n"), ("範囲 負の刻み", "[9 ~+ (0 - 2) ~ 1]\n"), ("範囲 1 個", "[3 ~ 3]\n"),
 ("範囲の長さ", "||[1 ~ 5]||\n"), ("範囲の要素", "[1 ~ 5] ' 2\n"), ("範囲 負の端", "[(0 - 2) ~ 2]\n"),
 ("範囲を関数へ", "g : xs i ? xs ' i\ng [10 ~ 20] 4\n"),
 ("スライス", "xs : 1 2 3 4 5\nxs ' [1 ~ 3]\n"), ("スライス 全部", "xs : 1 2 3 4 5\nxs ' [0 ~ 4]\n"), ("スライス 1 個", "xs : 1 2 3 4 5\nxs ' [2 ~ 2]\n"),
 ("スライス 外", "xs : 1 2 3 4 5\nxs ' [0 ~ 5]\n"), ("スライスの長さ", "xs : 1 2 3 4 5\n||xs ' [1 ~ 3]||\n"), ("スライスの要素", "xs : 1 2 3 4 5\n(xs ' [1 ~ 3]) ' 2\n"),
 ("スライスを関数へ", "n : ys ? ||ys||\nxs : 1 2 3 4 5\nn (xs ' [1 ~ 3])\n"), ("仮引数のスライス", "f : xs ? xs ' [1 ~ 2]\nf (1 2 3 4)\n"),
 ("仮引数のスライス 外", "f : xs ? xs ' [1 ~ 2]\nf (1 2)\n"), ("スライスの重ね", "xs : 1 2 3 4 5\n(xs ' [1 ~ 4]) ' [1 ~ 2]\n"),
 ("文字列のスライス", "s : `hello`\ns ' [1 ~ 3]\n"), ("文字列のスライス 外", "s : `hello`\ns ' [1 ~ 9]\n"),
 ("連結 2 つ", "xs : 1 2 3\nys : 4 5\nxs~ ys~\n"), ("連結 先頭に足す", "xs : 1 2 3\n9 xs~\n"), ("連結 後ろに足す", "xs : 1 2 3\nxs~ 9\n"),
 ("連結 両側", "xs : 1 2 3\n0 xs~ 9\n"), ("連結 範囲", "xs : 1 2 3\n[1 ~ 3]~ xs~\n"), ("連結 範囲と字面", "xs : 1 2 3\nxs~ [7 ~ 9]~\n"),
 ("連結 同じのを 2 回", "xs : 1 2 3\nxs~ xs~\n"),
 ("連結の関数", "f : xs ys ? xs~ ys~\nf (1 2) (3 4 5)\n"),
 ("連結の長さ", "f : xs ys ? xs~ ys~\n||f (1 2) (3 4 5)||\n"),
 ("連結の要素", "f : xs ys ? xs~ ys~\n(f (1 2) (3 4 5)) ' 3\n"),
 ("連結 片方に要素", "f : xs ? 0 xs~\nf (1 2)\n"), ("連結 両側に要素", "f : xs ? 0 xs~ 9\nf (1 2 3)\n"),
 ("連結 式の要素", "f : xs a ? (a * 2) xs~ (a + 1)\nf (1 2) 5\n"),
 ("連結 2 回呼ぶ", "f : xs ys ? xs~ ys~\nh : a b ? ||f a b|| + ((f a b) ' 0)\nh (7 8) (1 2 3)\n"),
 ("連結を下へ渡す", "f : xs ys ? xs~ ys~\ng : xs ys ? f xs ys\ng (1 2) (3 4 5)\n"),
 ("連結を二段で渡す", "f : xs ys ? xs~ ys~\ng : xs ys ? f xs ys\nk : xs ys ? g ys xs\nk (1 2) (3 4 5)\n"),
 ("連結 枝で選ぶ", "f : a xs ys ?\n\ta > 0 : xs~ ys~\n\tys~ xs~\nf 1 (1 2) (3 4 5)\n"),
 ("連結 枝で選ぶ 2", "f : a xs ys ?\n\ta > 0 : xs~ ys~\n\tys~ xs~\nf 0 (1 2) (3 4 5)\n"),
 ("連結 枝で素通し", "f : a xs ys ?\n\ta > 0 : xs~ ys~\n\txs\nf 0 (1 2) (3 4 5)\n"),
 ("連結 定数のスライスを展開", "xs : 1 2 3\nys : 4 5\n(xs ' [0 ~ 1])~ ys~\n"),
 ("連結 空に近い", "f : xs ys ? xs~ ys~\n||f (1 2) (3 4)||\n"),
 ("連結 受け取って足す", "f : xs ys ? xs~ ys~\ns : zs i acc ?\n\ti >= ||zs|| : acc\n\ts zs (i + 1) (acc + (zs ' i))\ns (f (1 2) (3 4 5)) 0 0\n"),
 ("連結 3 つの器", "f : a b c ? a~ b~ c~\nf (1 0) (2 3) (4 5 6)\n"),
 ("連結 3 つの器 長さ", "f : a b c ? a~ b~ c~\n||f (1 2) (3 4) (5 6)||\n"),
 ("使わない関数は出さない(種類が決まらない)", "f : xs ys ? 0 xs~ ys~ 9\nh : a b ? ||f a b||\nxs : 1 2 3\nys : [10 ~ 12]\nf xs ys\n"),
 ("連結 係数 2", "f : xs ? xs~ xs~\n||f (1 2 3)||\n"),
 ("連結 係数 2 の中身", "f : xs ? xs~ xs~\nf (1 2 3)\n"),
 ("連結 係数 3", "f : xs ? xs~ xs~ xs~\nf (1 2)\n"),
 ("連結 下へ係数", "f : xs ? xs~ xs~\ng : ys ? f ys\ng (4 5 6)\n"),
 ("連結 下へ定数の引数", "f : xs ? xs~ 0\ng : a ? f (1 2 3)\ng 1\n"),
 ("連結 再帰で素通し", "f : xs i ?\n\ti >= 3 : xs~ 9\n\tf xs (i + 1)\nf (1 2) 0\n"),
]

STR_CASES += [
 # ---- 第 9 段: 規則 {start, step, end} の値渡し(実行時の端の範囲) ----
 ("規則 作って印字", "f : n ? [1 ~ n]\nf 4\n"),
 ("規則 1 個", "f : n ? [1 ~ n]\nf 1\n"),
 ("規則 端が逆", "f : n ? [1 ~ n]\nf 0\n"),
 ("規則 負へ", "f : n ? [1 ~ n]\nf (0 - 2)\n"),
 ("規則 降順", "f : a b ? [a ~ b]\nf 5 2\n"),
 ("規則 刻み", "f : a s b ? [a ~+ s ~ b]\nf 1 2 9\n"),
 ("規則 刻みで割り切れない", "f : a s b ? [a ~+ s ~ b]\nf 1 4 10\n"),
 ("規則 負の刻み", "f : a s b ? [a ~+ s ~ b]\nf 9 (0 - 2) 1\n"),
 ("規則 負の刻みで割り切れない", "f : a s b ? [a ~+ s ~ b]\nf 10 (0 - 4) 1\n"),
 ("規則 刻みの向きが逆", "f : a s b ? [a ~+ s ~ b]\nf 1 (0 - 2) 9\n"),
 ("規則 刻みの向きが逆で差が小さい", "f : a s b ? [a ~+ s ~ b]\nf 1 (0 - 3) 2\n"),
 ("規則 同じ端", "f : a s b ? [a ~+ s ~ b]\nf 5 2 5\n"),
 ("規則 同じ端で負の刻み", "f : a s b ? [a ~+ s ~ b]\nf 5 (0 - 2) 5\n"),
 ("規則 の個数", "f : a s b ? ||[a ~+ s ~ b]||\nf 1 2 10\n"),
 ("規則 の個数 逆向き", "f : a s b ? ||[a ~+ s ~ b]||\nf 1 (0 - 2) 10\n"),
 ("規則 の個数 割り切れない", "f : a s b ? ||[a ~+ s ~ b]||\nf 0 3 10\n"),
 ("規則 の要素", "f : n i ? [1 ~ n] ' i\nf 5 3\n"),
 ("規則 の要素 先頭", "f : n i ? [1 ~ n] ' i\nf 5 0\n"),
 ("規則 の要素 末尾", "f : n i ? [1 ~ n] ' i\nf 5 4\n"),
 ("規則 の要素 負", "f : n i ? [1 ~ n] ' i\nf 5 (0 - 1)\n"),
 ("規則 の要素 負の端", "f : n i ? [1 ~ n] ' i\nf 5 (0 - 5)\n"),
 ("規則 の要素 負の外", "f : n i ? [1 ~ n] ' i\nf 5 (0 - 6)\n"),
 ("規則 の要素 外", "f : n i ? [1 ~ n] ' i\nf 5 5\n"),
 ("規則 の要素 巨大な添字", "f : n i ? [1 ~ n] ' i\nf 5 9223372036854775807\n"),
 ("規則 の要素 刻みつき", "f : a s b i ? [a ~+ s ~ b] ' i\nf 10 (0 - 3) 0 2\n"),
 ("規則 の要素 __ の添字", "f : n i ? [1 ~ n] ' i\nf 5 (n ' 0)\n") if False else ("規則 の要素 空の規則", "f : a s b i ? [a ~+ s ~ b] ' i\nf 1 (0 - 2) 9 0\n"),
 ("規則を返す関数の結果を引く", "mk : n ? [1 ~ n]\n(mk 5) ' 2\n"),
 ("規則を返す関数の個数", "mk : n ? [1 ~ n]\n||mk 5||\n"),
 ("規則を返して印字", "mk : n ? [2 ~+ 3 ~ n]\nmk 20\n"),
 ("規則を渡す(字面の範囲)", "mk : n ? [1 ~ n]\nlen : r ? ||r||\n(len (mk 5)) + (len [1 ~ 7])\n"),
 ("規則を渡して引く", "mk : n ? [2 ~+ 3 ~ n]\nat : r i ? r ' i\nat (mk 20) 3\n"),
 ("規則を下へ渡す", "mk : n ? [1 ~ n]\nlen : r ? ||r||\nw : r ? len r\nw (mk 6)\n"),
 ("規則を返す関数を下へ渡す", "mk : n ? [1 ~ n]\nk : n ? mk (n + 1)\nk 4\n"),
 ("規則を枝で選ぶ", "h : a n ?\n\ta > 0 : [1 ~ n]\n\t[n ~ 1]\nh 1 4\n"),
 ("規則を枝で選ぶ 2", "h : a n ?\n\ta > 0 : [1 ~ n]\n\t[n ~ 1]\nh 0 4\n"),
 ("規則を枝で選ぶ 字面の範囲", "h : a n ?\n\ta > 0 : [1 ~ n]\n\t[5 ~ 1]\nh 0 4\n"),
 ("規則を足し込み(末尾再帰)", "mk : n ? [1 ~ n]\nsum : r i acc ?\n\ti >= ||r|| : acc\n\tsum r (i + 1) (acc + (r ' i))\nsum (mk 100) 0 0\n"),
 ("規則を足し込み 刻み", "mk : n ? [0 ~+ 7 ~ n]\nsum : r i acc ?\n\ti >= ||r|| : acc\n\tsum r (i + 1) (acc + (r ' i))\nsum (mk 100) 0 0\n"),
 ("規則の端が式", "f : a b ? [a + 1 ~ b * 2]\nf 3 4\n"),
 ("規則の端が呼び", "g : x ? x * 3\nf : a ? [(g a) ~ (g (a + 1))]\nf 2\n"),
 ("規則の個数を端に", "f : n ? [1 ~ ||[1 ~ n]|| + 1]\nf 3\n"),
 ("規則と器の混在引数", "f : r xs ? ||r|| + ||xs||\nmk : n ? [1 ~ n]\nf (mk 4) (7 8 9)\n"),
 ("規則 2 つ", "f : r q ? (r ' 1) + (q ' 1)\nmk : n ? [1 ~ n]\nf (mk 4) [10 ~ 20]\n"),
 ("規則 引数 8 本に収まる", "f : r q a b ? ||r|| + ||q|| + a + b\nmk : n ? [1 ~ n]\nf (mk 4) (mk 5) 6 7\n"),
]

# ---- 第 10 段: 入れ子の器(List(List(Int)))。記述子 {ptr, len} の表と arena ----
STR_CASES += [
    ("入れ子 字面", "m : (1 2) (3 4 5)\nm\n"),
    ("入れ子 字面 3 つ", "m : (1 2) (3 4 5) (6 7)\nm\n"),
    ("入れ子 字面 別名", "m : (1 2) (3 4 5)\nn : m\nn\n"),
    ("入れ子 名前付きのリストを並べる", "a : 1 2\nb : 3 4 5\na b\n"),
    ("入れ子 範囲の字面", "[1 ~ 3] [7 ~ 9]\n"),
    ("入れ子 降順の範囲", "[3 ~ 1] [7 ~ 9]\n"),
    ("入れ子 同じ内側が重なる", "(1 2) (1 2) (1 2)\n"),
    ("入れ子 1 要素の内側(スライス)", "xs : 1 2 3\n(xs ' [1 ~ 1]) (4 5)\n"),
    ("入れ子 長さ", "m : (1 2) (3 4 5)\n||m||\n"),
    ("入れ子 内側の長さ", "m : (1 2) (3 4 5)\n||m ' 1||\n"),
    ("入れ子 取り出し 先頭", "m : (1 2) (3 4 5)\nm ' 0\n"),
    ("入れ子 取り出し 負", "m : (1 2) (3 4 5)\nm ' (0 - 1)\n"),
    ("入れ子 取り出し 負の端", "m : (1 2) (3 4 5)\nm ' (0 - 2)\n"),
    ("入れ子 取り出し 範囲外", "m : (1 2) (3 4 5)\nm ' 5\n"),
    ("入れ子 取り出し 負の範囲外", "m : (1 2) (3 4 5)\nm ' (0 - 3)\n"),
    ("入れ子 要素の要素", "m : (1 2) (3 4 5)\n(m ' 1) ' 2\n"),
    ("入れ子 要素の要素 負", "m : (1 2) (3 4 5)\n(m ' 1) ' (0 - 1)\n"),
    ("入れ子 要素の要素 外", "m : (1 2) (3 4 5)\n(m ' 1) ' 3\n"),
    ("入れ子 内側が外れ", "m : (1 2) (3 4 5)\n(m ' 9) ' 0\n"),
    ("入れ子 スライス", "m : (1 2) (3 4 5) (6 7)\nm ' [1 ~ 2]\n"),
    ("入れ子 スライスして取り出す", "m : (1 2) (3 4 5) (6 7)\n(m ' [1 ~ 2]) ' 1\n"),
    ("入れ子 スライスの外", "m : (1 2) (3 4 5)\nm ' [1 ~ 4]\n"),
    ("入れ子 引数の長さ", "len2 : m ? ||m||\nlen2 ((1 2) (3 4 5))\n"),
    ("入れ子 引数から取り出す", "get : m i ? m ' i\nget ((1 2) (3 4 5)) 1\n"),
    ("入れ子 引数から取り出す(外)", "get : m i ? m ' i\nget ((1 2) (3 4 5)) 7\n"),
    ("入れ子 引数から要素の要素", "g : m i j ? (m ' i) ' j\ng ((1 2) (3 4 5)) 1 2\n"),
    ("入れ子 名前を渡す", "m : (1 2) (3 4 5)\nlen2 : m ? ||m||\nlen2 m\n"),
    ("入れ子 末尾再帰で内側の長さの和", "sum : m i acc ?\n\ti = ||m|| : acc\n\tsum m (i + 1) (acc + ||m ' i||)\nsum ((1 2) (3 4 5) (6 7)) 0 0\n"),
    ("入れ子 そのまま返す", "id2 : m ? m\nid2 ((1 2) (3 4 5))\n"),
    ("入れ子 そのまま返す→取り出す", "id2 : m ? m\n(id2 ((1 2) (3 4 5))) ' 1\n"),
    ("入れ子 内側を返す", "first : m ? m ' 0\nfirst ((1 2) (3 4 5))\n"),
    ("入れ子 内側を渡す", "f : xs ? ||xs||\nm : (1 2) (3 4 5)\nf (m ' 1)\n"),
    ("入れ子 内側が __ なら呼び全体が __", "f : xs ? ||xs||\nm : (1 2) (3 4 5)\nf (m ' 7)\n"),
    ("入れ子 外れるスライスを渡すと呼び全体が __", "f : xs ? ||xs||\nys : 1 2 3\nf (ys ' [5 ~ 6])\n"),
    ("入れ子 引数が呼びの結果", "mk : a ? (a a) (a 1)\ng : m ? (m ' 1) ' 1\ng (mk 5)\n"),
    # ---- 混ざる入れ子(ptr の下位ビットの印。DESIGN_NESTED.md §4)----
    ("混在 字面", "m : [1 [2 3]]\nm\n"),
    ("混在 字面 リストが先", "m : [[1 2] 3]\nm\n"),
    ("混在 字面 1 要素の括り [3] はスカラー", "m : [[1 2] [3]]\nm\n"),
    ("混在 字面 4 要素", "m : [1 [2 3] 4 [5 6 7]]\nm\n"),
    ("混在 字面 負と定数", "k : 7\nm : [-1 [k 3]]\nm\n"),
    ("混在 長さ", "m : [1 [2 3]]\n||m||\n"),
    ("混在 取り出し スカラー", "m : [1 [2 3]]\nm ' 0\n"),
    ("混在 取り出し リスト", "m : [1 [2 3]]\nm ' 1\n"),
    ("混在 取り出し 負", "m : [1 [2 3]]\nm ' -1\n"),
    ("混在 取り出し 範囲外", "m : [1 [2 3]]\nm ' 5\n"),
    ("混在 要素の要素(スカラーは長さ 1 のリスト)", "m : [1 [2 3]]\nm ' 0 ' 0\n"),
    ("混在 要素の長さ スカラー", "m : [1 [2 3]]\n||m ' 0||\n"),
    ("混在 要素の長さ リスト", "m : [1 [2 3]]\n||m ' 1||\n"),
    ("混在 引数から要素の要素", "f : m i j ? m ' i ' j\nf [1 [2 3] 4] 1 1\n"),
    ("混在 引数の長さ", "f : m ? ||m||\nf [1 [2 3] 4]\n"),
    ("混在 そのまま返す", "g : m ? m\ng [1 [2 3]]\n"),
    ("混在 スライス", "m : [1 [2 3] 4]\nm ' [0 ~ 1]\n"),
    ("混在 返値で組む", "f : a ? [a [a a]]\nf 5\n"),
    ("混在 返値で組む 先頭がリスト", "f : a ? [[a a] a]\nf 3\n"),
    ("混在 返値で組む 3 要素", "f : a b ? [[a b] a [b b b]]\nf 1 2\n"),
    ("混在 返値 取り出し スカラー", "f : a ? [a [a a]]\n(f 5) ' 0\n"),
    ("混在 返値 取り出し リスト", "f : a ? [a [a a]]\n(f 5) ' 1\n"),
    ("混在 返値 長さ", "f : a ? [a [a a]]\n||f 5||\n"),
    ("混在 リストの並置(xs 7)", "f : xs ? xs 7\nf (1 2)\n"),
    ("混在 リストの並置(7 xs)", "f : xs ? 7 xs\nf (1 2)\n"),
    ("混在 合計", "f : m ? (m ' 0 ' 0) + (m ' 1 ' 0) + (m ' 1 ' 1)\nf [1 [2 3]]\n"),
    ("混在 名前のリストと", "xs : [1 2]\nf : a ? [a xs]\nf 9\n"),
    ("混在 展開 字面の名前(後ろ)", "m : [1 [2 3]]\n0 m~\n"),
    ("混在 展開 字面の名前(前後)", "m : [1 [2 3]]\n7 m~ 9\n"),
    ("混在 展開 字面の名前(2 回)", "m : [1 [2 3]]\nm~ m~\n"),
    ("混在 展開 字面の名前(3 要素)", "m : [1 [2 3] 4]\n0 m~\n"),
    ("混在 展開 字面の名前(リストが先)", "m : [[1 2] 3]\n0 m~\n"),
    ("混在 展開 字面の名前(括り [3])", "m : [[1 2] [3]]\n0 m~\n"),
    ("混在 展開 引数へ(2 つ)", "g : a b ? a + ||b||\nm : [1 [2 3]]\ng m~\n"),
    ("混在 展開 引数へ(3 つ)", "g : a b c ? a + ||b|| + c\nm : [1 [2 3] 4]\ng m~\n"),
    ("混在 展開 関数の中", "m : [1 [2 3]]\nf : a ? a m~\nf 9\n"),
    ("混在 展開 取り出し", "m : [1 [2 3]]\n(0 m~) ' 2\n"),
    ("混在 展開 長さ", "m : [1 [2 3]]\n||[0 m~]||\n"),
    ("別名 関数", "inc : x ? x + 1\np : inc\np 3\n"),
    ("別名 演算子", "add : [+]\nadd 2 3\n"),
    ("別名 2 段", "inc : x ? x + 1\np : inc\nq : p\nq 3\n"),
    ("別名 を関数へ渡す", "inc : x ? x + 1\np : inc\napp : f x ? @f x\napp $p 3\n"),
    ("範囲の畳み 和", "[+] [1 ~ 5]\n"),
    ("範囲の畳み 積", "[*] [1 ~ 5]\n"),
    ("範囲の畳み 降り 差", "[-] [5 ~ 1]\n"),
    ("範囲の畳み 昇り 差", "[-] [1 ~ 5]\n"),
    ("範囲の畳み 大きい方 `>` は __", "[>] [1 ~ 5]\n"),
    ("範囲の畳み 小さい方 `<`", "[<] [1 ~ 5]\n"),
    ("範囲の畳み 要素 1 個", "[+] [7 ~ 7]\n"),
    ("範囲の畳み 負の端", "[+] [-3 ~ 3]\n"),
    ("範囲の畳み 降りの負の端", "[+] [3 ~ -3]\n"),
    ("範囲の畳み 割り", "[/] [100 ~ 1]\n"),
    ("範囲の畳み 0 で割ると __", "[/] [5 ~ 0]\n"),
    ("範囲の畳み 式の中", "1 + ([+] [1 ~ 4])\n"),
    ("範囲の畳み 表に広げない大きさ(4096 個を超える)", "[+] [1 ~ 20000]\n"),
    ("範囲の畳み 段付きは従来の道", "[+] [0 ~+ 2 ~ 10]\n"),
    ("節 畳み 2 個", "[+] 2 3\n"),
    ("節 畳み 3 個(左から)", "[-] 10 3 2\n"),
    ("節 畳み 掛け算", "[*] 2 3 4\n"),
    ("節 畳み 割り算", "[/] 100 5 2\n"),
    ("節 畳み 負数", "[+] -1 2\n"),
    ("節 右", "[- 2] 5\n"),
    ("節 左", "[2 -] 5\n"),
    ("節 式の一部", "[+ 2] 3 + 1\n"),
    ("節 関数の中", "f : a b ? [+] a b 1\nf 4 5\n"),
    ("別名 節 右", "inc : [+ 1]\ninc 5\n"),
    ("別名 節 左", "neg : [0 -]\nneg 5\n"),
    ("節 比較の畳み(真)", "[>] 3 2\n"),
    ("節 比較の畳み(偽は __)", "[>] 2 3\n"),
    ("節 比較の畳み 3 個", "[>] 5 3 1\n"),
    ("節 比較の畳み 3 個(偽)", "[>] 5 3 9\n"),
    ("節 = の畳み", "[=] 3 3\n"),
    ("節 比較 右(真)", "[> 2] 3\n"),
    ("節 比較 右(偽)", "[> 2] 1\n"),
    ("節 比較 左", "[2 >] 1\n"),
    ("節 >= 右", "[>= 2] 3\n"),
    ("節 != 右", "[!= 2] 3\n"),
    ("節 比較 関数の中(偽)", "f : a b ? [>] a b\nf 3 5\n"),
    ("別名 比較の節", "gt : [>]\ngt 4 2\n"),
    ("別名 比較の節(偽)", "gt : [>]\ngt 2 4\n"),
    ("節 畳みの実引数 1 個", "[+] 5\n"),
    ("節 右の実引数 2 個(残りは並べる)", "[+ 2] 3 4\n"),
    ("節 左の実引数 2 個", "[2 -] 5 6\n"),
    ("節 器の畳み + 字面の器", "[+] (1 2 3)\n"),
    ("節 器の畳み + 名前", "xs : [1 2 3]\n[+] xs\n"),
    ("節 器の畳み + 仮引数", "f : l ? [+] l\nf [4 5 6]\n"),
    ("節 器の畳み *", "f : l ? [*] l\nf [2 3 4]\n"),
    ("節 器の畳み - (左から)", "f : l ? [-] l\nf [10 3 2]\n"),
    ("節 器の畳み 1 要素", "f : l ? [+] l\nf [4 5]\n"),
    ("節 器の畳み 0 で割る(__)", "f : l ? [/] l\nf [100 5 0]\n"),
    ("節 器の畳み 比較(真)", "f : l ? [>] l\nf [5 3 1]\n"),
    ("節 器の畳み 比較(偽)", "f : l ? [>] l\nf [5 3 9]\n"),
    ("別名 器の畳み", "sum : [+]\nf : l ? sum l\nf [1 2 3 4]\n"),
    ("節 器の畳み 括って足す", "f : l ? ([+] l) + 1\nf [1 2 3]\n"),
    ("節 器の畳み 2 種", "f : l ? ([+] l) + ([*] l)\nf [1 2 3]\n"),
    ("節 器の畳み 並べる", "f : l ? ([+] l) ([*] l)\nf [2 3]\n"),
    ("節 器の畳み 分岐の中", "f : l ?\n\t||l|| = 0 : 0\n\t[+] l\nf [1 2 3]\n"),
    ("節 器の畳み 長いリスト", "l : 1 2 3 4 5 6 7 8 9 10 11 12\n[+] l\n"),
    ("節 整数の字面 1 個", "[+] 5\n"),
    ("非混在 展開 字面の名前は従来どおり平ら", "m : [[1 2] [3 4]]\n0 m~\n"),
    ("入れ子 呼びの結果を要素に 2 つ", "g : a ? a (a + 1) (a + 2)\nf : a ? [(g a) (g (a + 10))]\nf 1\n"),
    ("入れ子 呼びの結果とスカラー", "g : a ? a (a + 1) (a + 2)\nf : a ? [a (g a)]\nf 1\n"),
    ("入れ子 呼びの結果と字面", "g : a ? a (a + 1) (a + 2)\nf : a ? [(g a) [a a]]\nf 1\n"),
    ("混在 分岐で組む(返す置き場の上を印字が壊さない)", "h : a ?\n\ta > 0 : [a [a a]]\n\t[[a a] a]\nh 3\n"),
    ("混在 分岐で組む 別の枝", "h : a ?\n\ta > 0 : [a [a a]]\n\t[[a a] a]\nh -3\n"),
    ("混在 再帰の底で組む", "f : n ?\n\tn = 0 : [0 [0 0]]\n\t[n [n n]]\nf 3\n"),
    ("混在 要素の合計(長さ)", "f : m ? (m ' 0 ' 0) * 10 + ||m ' 1||\nf [4 [2 3]]\n"),
    ("混在 末尾再帰で長さの和", "sum : m i acc ?\n\ti = ||m|| : acc\n\tsum m (i + 1) (acc + ||m ' i||)\nsum [1 [2 3] 4 [5 6 7]] 0 0\n"),
    ("混在 呼びの結果の要素", "mk : a ? [a [a a]]\ng : m ? (m ' 1) ' 1\ng (mk 5)\n"),
    ("混在 呼びの結果を 2 つ", "mk : a ? [a [a a]]\ng : m n ? ((m ' 1) ' 1) + (n ' 0 ' 0)\ng (mk 5) (mk 8)\n"),
    ("3 段 末尾再帰で長さの和", "sum : m i acc ?\n\ti = ||m|| : acc\n\tsum m (i + 1) (acc + ||m ' i||)\nsum [[[1 2] [3 4]] [[5 6] [7 8] [9 9]]] 0 0\n"),
    ("3 段 字面", "m : [[[1 2] [3 4]] [[5 6] [7 8]]]\nm\n"),
    ("3 段 長さ", "m : [[[1 2] [3 4]] [[5 6] [7 8]]]\n||m||\n"),
    ("3 段 2 段目の長さ", "m : [[[1 2] [3 4]] [[5 6] [7 8]]]\n||m ' 1||\n"),
    ("3 段 取り出し 2 段目", "m : [[[1 2] [3 4]] [[5 6] [7 8]]]\nm ' 1\n"),
    ("3 段 取り出し 3 段目", "m : [[[1 2] [3 4]] [[5 6] [7 8]]]\nm ' 1 ' 0\n"),
    ("3 段 取り出し 要素", "m : [[[1 2] [3 4]] [[5 6] [7 8]]]\nm ' 1 ' 0 ' 1\n"),
    ("3 段 取り出し 負", "m : [[[1 2] [3 4]] [[5 6] [7 8]]]\nm ' -1 ' -1 ' -1\n"),
    ("3 段 範囲外", "m : [[[1 2] [3 4]] [[5 6] [7 8]]]\nm ' 5 ' 0\n"),
    ("3 段 引数から要素", "f : m i j k ? m ' i ' j ' k\nf [[[1 2] [3 4]] [[5 6] [7 8]]] 1 0 1\n"),
    ("3 段 中の段を渡す", "g : m ? ||m||\nf : m ? g (m ' 1)\nf [[[1 2] [3 4]] [[5 6] [7 8]]]\n"),
    ("3 段 そのまま返す", "f : m ? m\nf [[[1 2] [3 4]] [[5 6] [7 8]]]\n"),
    ("4 段 取り出し", "m : [[[[1 2] [3 4]] [[5 6] [7 8]]] [[[1 2] [3 4]] [[5 6] [7 8]]]]\nm ' 1 ' 1 ' 0 ' 1\n"),
    ("3 段 スカラー混在(最下段)", "m : [[1 [2 3]] [4 [5 6]]]\nm\n"),
    ("3 段 スカラー混在 取り出し リスト", "m : [[1 [2 3]] [4 [5 6]]]\nm ' 1 ' 1\n"),
    ("3 段 スカラー混在 取り出し スカラー", "m : [[1 [2 3]] [4 [5 6]]]\nm ' 1 ' 0\n"),
    ("文字列の入れ子 字面の印字", "m : [`ab` , `cd`]\nm\n"),
    ("文字列の入れ子 取り出し", "m : [`ab` , `cd`]\nm ' 1\n"),
    ("文字列の入れ子 文字", "m : [`ab` , `cd`]\nm ' 1 ' 0\n"),
    ("文字列の入れ子 長さ", "m : [`ab` , `cd`]\n||m||\n"),
    ("文字列の入れ子 3 段", "m : [[`ab` , `cd`] , [`ef` , `gh`]]\nm\n"),
    ("文字列の入れ子 3 段 取り出し", "m : [[`ab` , `cd`] , [`ef` , `gh`]]\nm ' 1 ' 0\n"),
    ("文字列とリストの混在 字面の印字", "m : [`ab` , [1 2]]\nm\n"),
    ("文字列とスカラーの混在 字面の印字", "m : [`ab` , 1]\nm\n"),
    ("文字列とリストの混在 長さ", "m : [`ab` , [1 2]]\n||m||\n"),
    ("組み立て 入れ子", "f : a b ? (a b) (b a)\nf 1 2\n"),
    ("組み立て 入れ子 式", "f : a b ? (a + b) (a * b) (a - b)\nf 3 4\n"),
    ("組み立て 入れ子 展開", "f : xs a ? (a xs~) (xs~ a)\nf (1 2 3) 9\n"),
    ("組み立て 入れ子 展開 2 つの器", "f : xs ys ? (xs~ ys~) (ys~ xs~)\nf (1 2) (3 4 5)\n"),
    ("組み立て 入れ子 既存の器と混ぜる", "f : xs a ? xs (a a)\nf (1 2 3) 9\n"),
    ("組み立て 入れ子 器を並べるだけ", "f : xs ys ? xs ys\nf (1 2 3) (4 5)\n"),
    ("組み立て 入れ子 字面と混ぜる", "f : a ? (1 2) (a a)\nf 7\n"),
    ("組み立て 入れ子 スライスを混ぜる", "f : a ? (a a) (xs ' [0 ~ 1])\nxs : 1 2 3\nf 7\n"),
    ("組み立て 入れ子 素通し(末尾呼び出し)", "f : xs a ? (a xs~) (xs~ a)\ng : xs a ? f xs a\ng (1 2 3) 9\n"),
    ("組み立て 入れ子 分岐", "h : n xs ?\n\tn > 0 : (n n) xs\n\txs (n n)\nh 3 (7 8)\n"),
    ("組み立て 入れ子 分岐の別の枝", "h : n xs ?\n\tn > 0 : (n n) xs\n\txs (n n)\nh 0 (7 8)\n"),
    ("組み立て 入れ子 既定の行が無い(外れ)", "h : n xs ?\n\tn > 0 : (n n) xs\nh 0 (7 8)\n"),
    ("組み立て 入れ子 分岐で記述子と内容の最大が別の枝", "h : n xs ?\n\tn > 0 : (n n) (n 1) (n 2) (n 3) (n 4)\n\t(xs~ xs~ xs~) (xs~ xs~)\nh 0 (7 8)\n"),
    ("組み立て 入れ子 分岐で記述子と内容の最大が別の枝(もう一方)", "h : n xs ?\n\tn > 0 : (n n) (n 1) (n 2) (n 3) (n 4)\n\t(xs~ xs~ xs~) (xs~ xs~)\nh 1 (7 8)\n"),
    ("組み立て 入れ子 最上位", "((2 * 3) 4) ((1 + 1) 7)\n"),
    ("組み立て 入れ子 最上位 負", "((0 - 2) 4) (5 (0 - 7))\n"),
    ("組み立て 入れ子 結果の取り出し", "f : a ? (a 1) (a 2)\n(f 1) ' 1\n"),
    ("組み立て 入れ子 結果の長さ", "f : a ? (a 1) (a 2)\n||(f 1) ' 1||\n"),
    ("組み立て 入れ子 結果の要素の要素", "f : a ? (a 1) (a 2)\n((f 5) ' 1) ' 0\n"),
    ("組み立て 入れ子 結果を別の関数へ", "f : a ? (a 1) (a 2 3)\ng : m ? ||m ' 0|| + ||m ' 1||\ng (f 5)\n"),
    ("組み立て 入れ子 結果を二重に渡す", "f : a ? (a 1) (a 2 3)\nid2 : m ? m\nid2 (id2 (f 5))\n"),
    ("組み立て 入れ子 を作る関数を 2 回呼ぶ", "f : a ? (a 1) (a 2 3)\ng : m n ? (m ' 1) ' 1 + ((n ' 1) ' 2)\ng (f 5) (f 8)\n"),
    ("組み立て 入れ子 負の値", "f : a ? (a (0 - a)) ((0 - a) a)\nf 4\n"),
    ("組み立て 入れ子 範囲の展開", "f : a ? (a [1 ~ 3]~) (a a)\nf 4\n"),
    ("組み立て 入れ子 組み立てた器を要素に", "mk : a ? a a\nf : a ? (mk a) (1 2)\nf 3\n"),
    ("組み立て 入れ子 組み立てた器を要素に(展開つき)", "mk : a xs ? (a xs~)\nf : a xs ? (mk a xs) (xs~ a)\nf 3 (1 2)\n"),
    ("組み立て 入れ子 組み立てた器を何度も要素に", "mk : a b ? a b 7\nf : a ? (mk a 1) (mk 2 a) (mk a a)\nf 3\n"),
    ("組み立て 入れ子 組み立てた器を要素に→取り出す", "mk : a b ? a b 7\nf : a ? (mk a 1) (mk 2 a) (mk a a)\n(f 3) ' 1\n"),
    ("組み立て 入れ子 組み立てた器を要素に→下へ渡す", "mk : a b ? a b 7\nf : a ? (mk a 1) (mk 2 a)\ng : a ? f a\ng 5\n"),
    ("組み立て 入れ子 組み立てた器を要素に(分岐)", "mk : a b ? a b 7\nf : a ?\n\ta > 0 : (mk a 1) (mk 2 a)\n\t(1 2) (3 4) (5 6)\nf 0\n"),
    ("展開 入れ子を平らにして組み立て", "f : m ? 0 m~ 9\nf ((1 2) (3 4 5))\n"),
    ("展開 入れ子を平らにして入れ子の中で", "f : m ? (0 m~) (m~ 9)\nf ((1 2) (3 4 5))\n"),
    ("展開 定数の入れ子を平らに", "m : (1 2) (3 4 5)\nf : a ? a m~ a\nf 7\n"),
    ("展開 入れ子 2 つを繋ぐ", "f : m n ? m~ n~\nf ((1 2) (3 4 5)) ((6 7) (8 9))\n"),
    ("展開 入れ子とリストを繋ぐ", "g : m xs ? xs~ m~ xs~\ng ((1 2) (3 4 5)) (9 8)\n"),
    ("展開 平らにした結果を下へ(上界は内側の総和)", "g : m ? 0 m~\nh : m ? g m\nh ((1 2) (3 4 5))\n"),
    ("展開 平らにした結果の長さ", "g : m ? 0 m~\nh : m ? ||g m||\nh ((1 2) (3 4 5))\n"),
    ("展開 平らにした結果を入れ子の要素に", "g : m ? 0 m~\nf : m ? (g m) (m~ 9)\nf ((1 2) (3 4 5))\n"),
    ("展開 内側が長い入れ子", "f : m ? 9 m~\nf ((1 2 3 4 5 6 7 8) (4 5 6))\n"),
    ("連結 字面 2 つ", "`ab` `cde`\n"),
    ("連結 字面と名前", "s : `ab`\n`xy` s `z`\n"),
    ("連結 名前の定義", "s : `ab` `cd`\nt : s `e`\nt\n"),
    ("連結 文字の字面", "s : `ab`\ns \\c\n"),
    ("連結 文字が先", "s : `ab`\n\\c s\n"),
    ("連結 文字の取り出し", "s : `ab`\n(s ' 0) (s ' 1) s\n"),
    ("連結 範囲外の文字は消える", "s : `ab`\n(s ' 5) s\n"),
    ("連結 スライス", "s : `abc`\n(s ' [0 ~ 0]) s\n"),
    ("連結 長さ", "s : `abc`\nt : `de`\n||s t||\n"),
    ("連結 関数が返す", "f : a b ? a b\nf `ab` `cde`\n"),
    ("連結 同じ引数を 2 回", "f : a b ? a b a\ng : s ? ||f s s||\ng `xyz`\n"),
    ("連結 文字と字面と式", "f : a b ? a (b ' 1) `-` b\nf `ab` `cde`\n"),
    ("連結 結果を連結", "f : a b ? a b\ng : a b c ? (f a b) c\ng `ab` `cd` `ef`\n"),
    ("連結 結果を 2 つ連結", "f : a b ? a b\ng : a b c ? (f a b) (f b c)\ng `ab` `cd` `ef`\n"),
    ("連結 素通し", "f : a b ? a b\nh : a b ? f a b\nh `ab` `cd`\n"),
    ("連結 文字を前に(取り出し)", "f : s i ? (s ' i) s\nf `abc` 1\n"),
    ("連結 文字を前に(外れて消える)", "f : s i ? (s ' i) s\nf `abc` 9\n"),
    ("連結 結果の文字", "f : a b ? a b\n(f `ab` `cd`) ' 2\n"),
    ("連結 分岐", "f : a n ?\n\tn > 0 : a `+` a\n\ta\nf `ab` 1\n"),
    ("連結 分岐の別の枝", "f : a n ?\n\tn > 0 : a `+` a\n\ta\nf `ab` 0\n"),
    ("連結 数との並置", "`a` 0\n"),
    ("連結 数が先", "0 `a`\n"),
    ("連結 負の数", "`a` (0 - 12) `b`\n"),
    ("連結 数が続く", "`a` 1 2 `b`\n"),
    ("連結 数の仮引数", "f : s n ? s n\nf `ab` 45\n"),
    ("連結 数の仮引数が先", "f : n s ? n s\nf 7 `ab`\n"),
    ("連結 式の数", "f : s n ? s (n + 1) `x`\nf `ab` 9\n"),
    ("連結 最大の数", "`a` 9223372036854775807 `b`\n"),
    ("連結 最小に近い数", "`a` (0 - 9223372036854775807)\n"),
    ("連結 0", "f : s n ? s n\nf `ab` 0\n"),
    ("連結 __ の数は消える", "`a` (5 / 0) `b`\n"),
    ("連結 __ の数は消える(関数の中)", "f : n ? `a` (n / 0)\nf 3\n"),
    ("連結 比較の値", "`a` (3 < 5)\n"),
    ("連結 比較が外れて消える", "`a` (5 < 3) `b`\n"),
    ("連結 数を 2 回", "f : s n ? s n n\nf `x` (0 - 5)\n"),
    ("連結 定数の数", "n : 42\n`v=` n\n"),
    ("連結 結果に数を足す", "f : s n ? s n\ng : s ? f (f s 1) 22\ng `q`\n"),
    ("連結 数と取り出した文字", "f : s i ? s (s ' i) i\nf `abc` 1\n"),
    ("連結 長さ", "f : s n ? s n `!`\n||f `abc` 100||\n"),
    ("展開 関数の結果", "f : xs ys ? xs~ ys~\ng : xs ys zs ? (f xs ys)~ zs~\ng (1 2) (3 4) (5 6)\n"),
    ("展開 関数の結果を 2 つ", "f : xs ys ? xs~ ys~\ng : xs ys zs ? 0 (f xs ys)~ (f zs xs)~\nh : a b c ? ||g a b c||\nh (1 2) (3 4) (5 6)\n"),
    ("展開 組み立てた器の結果", "mk : a ? a a\nf : a ? (mk a)~ 9\nf 4\n"),
    ("末尾の切り出し", "xs : 1 2 3\nxs ' 1~\n"),
    ("末尾の切り出し 尽きる", "xs : 1 2 3\nxs ' 3~\n"),
    ("末尾の切り出し 2 回", "xs : 1 2 3 4\n(xs ' 1~) ' 1~\n"),
    ("末尾の切り出し 文字列", "s : `abcd`\ns ' 2~\n"),
    ("末尾の切り出し 入れ子", "m : (1 2) (3 4 5) (6 7)\nm ' 1~\n"),
    ("末尾の切り出し 取り出す", "xs : 1 2 3 4\n(xs ' 2~) ' 0\n"),
    ("末尾の切り出し 引数に(尽きると呼び全体が __)", "f : xs ? ||xs||\nys : 1 2 3\nf (ys ' 3~)\n"),
    ("食う 2 個ずつ", "dup : xs ?\n\t||xs|| = 0 : __\n\t(xs ' 0) (xs ' 0) (dup (xs ' 1~))~\ndup (1 2 3)\n"),
    ("食う 1 個", "g : xs ?\n\t||xs|| = 0 : __\n\t(xs ' 0) (xs ' 0) (g (xs ' 1~))~\ng (7 8)\n"),
    ("食う 長い入力", "dup : xs ?\n\t||xs|| = 0 : __\n\t(xs ' 0) (xs ' 0) (dup (xs ' 1~))~\nf : xs ? ||dup xs||\nl : [1 ~ 300]\nf l\n"),
    ("食う 結果を取り出す", "dup : xs ?\n\t||xs|| = 0 : __\n\t(xs ' 0) (xs ' 0) (dup (xs ' 1~))~\n(dup (1 2 3)) ' 3\n"),
    ("食う 逆順(再帰が先)", "rev : xs ?\n\t(rev (xs ' 1~))~ (xs ' 0)\nrev (1 2 3 4)\n"),
    ("食う 別の器(底の定数)", "f : xs ?\n\t(f (xs ' 1~))~ 0\nf (1 2 3)\n"),
    ("食う 他の引数を持ち回る", "dbl : xs a ?\n\t(xs ' 0) a (dbl (xs ' 1~) a)~\ndbl (1 2 3) 9\n"),
    ("食う 2 個ずつ食う", "sq : xs ?\n\t(xs ' 0) * (xs ' 0) (sq (xs ' 2~))~\nsq (1 2 3 4 5)\n"),
    ("食う 間引き(末尾呼び出しと再帰が同居)", "keep : xs ?\n\t||xs|| = 0 : __\n\t(xs ' 0) = 2 : keep (xs ' 1~)\n\t(xs ' 0) (keep (xs ' 1~))~\nkeep (1 2 3 2 4)\n"),
    ("食う 末尾呼び出しだけ(器は変わる)", "sum : xs acc ?\n\t||xs|| = 0 : acc\n\tsum (xs ' 1~) (acc + (xs ' 0))\nsum (1 2 3 4) 0\n"),
    ("食う 下の関数から呼ぶ", "dup : xs ?\n\t||xs|| = 0 : __\n\t(xs ' 0) (xs ' 0) (dup (xs ' 1~))~\nh : xs ? dup xs\nh (4 5 6)\n"),
    ("食う 展開に", "dup : xs ?\n\t||xs|| = 0 : __\n\t(xs ' 0) (xs ' 0) (dup (xs ' 1~))~\nf : xs ? 0 (dup xs)~ 9\nf (4 5)\n"),
    ("食う 文字列", "dash : s ?\n\t||s|| = 0 : __\n\t`-` (s ' 0) (dash (s ' 1~))\ndash `abc`\n"),
    ("食う 文字列 1 文字", "dash : s ?\n\t||s|| = 0 : __\n\t`-` (s ' 0) (dash (s ' 1~))\ndash `a`\n"),
    ("食う 文字列 長さ", "dash : s ?\n\t||s|| = 0 : __\n\t`-` (s ' 0) (dash (s ' 1~))\nf : s ? ||dash s||\nf `hello world`\n"),
    ("食う 文字列 逆順", "rv : s ?\n\t(rv (s ' 1~)) `.` (s ' 0)\nrv `abc`\n"),
    ("食う 文字列 前後に", "dash : s ?\n\t||s|| = 0 : __\n\t`-` (s ' 0) (dash (s ' 1~))\ng : s ? `<` (dash s) `>`\ng `xyz`\n"),
    ("累積: 後ろへ伸ばす", "f : xs acc ?\n\t||xs|| = 1 : acc~ (xs ' 0)\n\tf (xs ' 1~) (acc~ (xs ' 0))\nf (1 2 3) (9 8)\n"),
    ("累積: 底の枝が acc そのもの", "f : xs acc ?\n\t||xs|| = 1 : acc\n\tf (xs ' 1~) (acc~ (xs ' 0))\nf (1 2 3) (9 8)\n"),
    ("累積: 2 つずつ伸ばす", "f : xs acc ?\n\t||xs|| = 1 : acc\n\tf (xs ' 1~) (acc~ (xs ' 0) * 2)\nf (1 2 3 4) (9 8)\n"),
    ("累積: 食うのが 1 個しか無い", "f : xs acc ?\n\t||xs|| = 1 : acc~ (xs ' 0)\n\tf (xs ' 1~) (acc~ (xs ' 0))\nf (4 4) (5 5)\n"),
    ("累積: 他の関数から呼ぶ・要素に足す", "f : xs acc ?\n\t||xs|| = 1 : acc~ (xs ' 0)\n\tf (xs ' 1~) (acc~ (xs ' 0))\nh : ys ? 0 (f ys (5 6))~ 99\nh (1 2 3)\n"),
    ("累積: 長さを測る", "f : xs acc ?\n\t||xs|| = 1 : acc~ (xs ' 0)\n\tf (xs ' 1~) (acc~ (xs ' 0) + 1)\ng : ys ? ||f ys (5 5)||\ng (1 2 3 4 5 6 7 8 9 10 11 12)\n"),
    ("累積: 食う器が複数ある呼びに Int が混じる", "f : xs acc k ?\n\t||xs|| = 1 : acc~ k\n\tf (xs ' 1~) (acc~ (xs ' 0)) (k + 1)\nf (1 2 3) (9 8) 10\n"),
    ('相互再帰: 2 関数の輪', "ev : xs ?\n\t||xs|| = 1 : (xs ' 0) 100\n\t(xs ' 0) (od (xs ' 1~))~\nod : xs ?\n\t||xs|| = 1 : (xs ' 0) 200\n\t(xs ' 0) 0 (ev (xs ' 1~))~\nev (1 2 3 4 5)\n"),
    ('相互再帰: 輪の長さが違う枝', "a : xs ?\n\t||xs|| = 1 : xs ' 0 7\n\t(xs ' 0) (b (xs ' 1~))~\nb : xs ?\n\t||xs|| = 1 : xs ' 0 8\n\t(xs ' 0) (xs ' 0) (a (xs ' 1~))~\na (1 2 3 4)\n"),
    ('相互再帰: 末尾で輪渡り・間引き', "a : xs ?\n\t||xs|| = 1 : (xs ' 0) 100\n\t(xs ' 0) = 0 : b (xs ' 1~)\n\t(xs ' 0) (b (xs ' 1~))~\nb : xs ?\n\t||xs|| = 1 : (xs ' 0) 200\n\t(xs ' 0) = 9 : a (xs ' 1~)\n\t(xs ' 0) (xs ' 0) (a (xs ' 1~))~\na (1 0 3 9 4 0 6 7)\n"),
    ('相互再帰: 3 関数の輪を他の関数から', "a : xs ?\n\t||xs|| = 1 : (xs ' 0) 1\n\t(xs ' 0) (b (xs ' 1~))~\nb : xs ?\n\t||xs|| = 1 : (xs ' 0) 2\n\t(xs ' 0) 0 (c (xs ' 1~))~\nc : xs ?\n\t||xs|| = 1 : (xs ' 0) 3\n\t(xs ' 0) 0 0 (a (xs ' 1~))~\nw : xs ? 5 (a xs)~ 6\nw (1 2 3 4 5 6 7)\n"),
    ('相互再帰: 200 要素の輪', "ev : xs ?\n\t||xs|| = 1 : (xs ' 0) 100\n\t(xs ' 0) (od (xs ' 1~))~\nod : xs ?\n\t||xs|| = 1 : (xs ' 0) 200\n\t(xs ' 0) 0 (ev (xs ' 1~))~\nl : 1 2 3 4 5 1 2 3 4 5 1 2 3 4 5 1 2 3 4 5 1 2 3 4 5 1 2 3 4 5 1 2 3 4 5 1 2 3 4 5 1 2 3 4 5 1 2 3 4 5 1 2 3 4 5 1 2 3 4 5 1 2 3 4 5 1 2 3 4 5 1 2 3 4 5 1 2 3 4 5 1 2 3 4 5 1 2 3 4 5 1 2 3 4 5 1 2 3 4 5 1 2 3 4 5 1 2 3 4 5 1 2 3 4 5 1 2 3 4 5 1 2 3 4 5 1 2 3 4 5 1 2 3 4 5 1 2 3 4 5 1 2 3 4 5 1 2 3 4 5 1 2 3 4 5 1 2 3 4 5 1 2 3 4 5 1 2 3 4 5 1 2 3 4 5 1 2 3 4 5 1 2 3 4 5 1 2 3 4 5 1 2 3 4 5 1 2 3 4 5\nf : ys ? ||ev ys||\nf l\n"),
    ('累積・輪: 文字列の累積 後ろへ', "f : s acc ?\n\t||s|| = 1 : acc (s ' 0)\n\tf (s ' 1~) (acc (s ' 0) `-`)\nf `abc` `<`\n"),
    ('累積・輪: 文字列の累積 字面を 2 つ・包む', "f : s acc ?\n\t||s|| = 1 : acc\n\tf (s ' 1~) (acc (s ' 0) `ab`)\ng : s ? `[` (f s `<`) `]`\ng `wxyz`\n"),
    ('累積・輪: 文字列の累積 200 文字', "f : s acc ?\n\t||s|| = 1 : acc (s ' 0)\n\tf (s ' 1~) (acc (s ' 0))\nh : s ? ||f s `>`||\nh `abcdefghijklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxyzabcdefghijklmnopqr`\n"),
    ('累積・輪: 文字列の輪', "ev : s ?\n\t||s|| = 1 : (s ' 0) `!`\n\t(s ' 0) (od (s ' 1~))\nod : s ?\n\t||s|| = 1 : (s ' 0) `?`\n\t(s ' 0) `.` (ev (s ' 1~))\nev `abcde`\n"),
    ('累積・輪: 食うと累積の同居 リスト', "f : xs acc ?\n\t||xs|| = 1 : acc~ (xs ' 0)\n\t(xs ' 0) (f (xs ' 1~) (acc~ (xs ' 0)))~\nf (1 2 3) (9 8)\n"),
    ('累積・輪: 食うと累積の同居 文字列', "f : s acc ?\n\t||s|| = 1 : acc (s ' 0)\n\t(s ' 0) (f (s ' 1~) (acc `+`))\nf `abcd` `<`\n"),
    ('累積・輪: 食うと累積の同居 展開の前後', "f : xs acc ?\n\t||xs|| = 1 : acc~ (xs ' 0)\n\t(xs ' 0) (f (xs ' 1~) (acc~ 0))~ 5\ng : ys ? 7 (f ys (3 3))~\ng (1 2 3 4 5 6)\n"),
    ('累積・輪: 食うと累積の同居 枝ごとに伸びる量が違う・末尾と混在', "f : xs acc ?\n\t||xs|| = 1 : acc~ (xs ' 0)\n\t(xs ' 0) = 3 : f (xs ' 1~) (acc~ 100 200)\n\t(xs ' 0) (f (xs ' 1~) (acc~ 0))~\nf (1 2 3 4 5 6) (3 3)\n"),
    ('段16b: 食う 作業領域が積み上がらない・累積', "f : xs acc ?\n\t||xs|| = 1 : acc~ (xs ' 0)\n\t(xs ' 0) (f (xs ' 1~) (acc~ 0))~\nl : 0 1 2 3 4 5 6 7 8 0 1 2 3 4 5 6 7 8 0 1 2 3 4 5 6 7 8 0 1 2 3 4 5 6 7 8 0 1 2 3 4 5 6 7 8 0 1 2 3 4 5 6 7 8 0 1 2 3 4 5 6 7 8 0 1 2 3 4 5 6 7 8 0 1 2 3 4 5 6 7 8 0 1 2 3 4 5 6 7 8 0 1 2 3 4 5 6 7 8 0 1 2 3 4 5 6 7 8 0 1 2 3 4 5 6 7 8 0 1 2 3 4 5 6 7 8 0 1 2 3 4 5 6 7 8 0 1 2 3 4 5 6 7 8 0 1 2 3 4 5\ng : ys ? ||f ys (3 3)||\ng l\n"),
    ('段16b: 器が 2 つの輪 (片方ずつ食う)', "a : xs ys ?\n\t||xs|| = 1 : (xs ' 0) (ys ' 0) 100\n\t(xs ' 0) (b (xs ' 1~) ys)~\nb : xs ys ?\n\t||ys|| = 1 : (ys ' 0) 200\n\t(ys ' 0) 0 (a xs (ys ' 1~))~\na (1 2 3) (4 5 6 7)\n"),
    ('段16b: 器が 2 つの輪 (両方使う)', "a : xs ys ?\n\t||xs|| = 1 : xs~ ys~ 100\n\t(xs ' 0) (b (xs ' 1~) (ys ' 1~))~\nb : xs ys ?\n\t||ys|| = 1 : xs~ 200\n\t(ys ' 0) (xs ' 0) (a (xs ' 1~) ys)~\na (1 2 3) (4 5 6 7)\n"),
    ('段16b: 器が 2 つの文字列の輪', "a : s t ?\n\t||s|| = 1 : s t `!`\n\t(s ' 0) (b (s ' 1~) t)\nb : s t ?\n\t||t|| = 1 : t `?`\n\t(t ' 0) `.` (a s (t ' 1~))\na `abc` `xyz`\n"),
    ('段16b: 入れ子を食う', "g : m ?\n\t||m|| = 1 : (m ' 0)~ 99\n\t(m ' 0)~ 0 (g (m ' 1~))~\ng ((1 2) (3 4) (5 6 7))\n"),
    ('段16b: 入れ子を 2 個ずつ食う', "g : m ?\n\t||m|| = 1 : (m ' 0)~ 99\n\t||m|| = 2 : (m ' 0)~ (m ' 1)~ 98\n\t(m ' 0)~ (m ' 1)~ 0 (g (m ' 2~))~\ng ((1 2) (3 4) (5 6 7) (8 8) (9 9 9))\n"),
    ('段16b: 入れ子を食う 他の関数から', "g : m ?\n\t||m|| = 1 : (m ' 0)~ 99\n\t(m ' 0)~ 0 (g (m ' 1~))~\nh : n ? 5 (g n)~ 6\nh ((1 2) (3 4) (5 6 7))\n"),
    ('段16b: 入れ子を食う 120 個', "g : m ?\n\t||m|| = 1 : (m ' 0)~ 99\n\t(m ' 0)~ 0 (g (m ' 1~))~\nl : (0 1) (0 1 2) (0 1 2 3) (0 1 2 3 4) (0 1) (0 1 2) (0 1 2 3) (0 1 2 3 4) (0 1) (0 1 2) (0 1 2 3) (0 1 2 3 4) (0 1) (0 1 2) (0 1 2 3) (0 1 2 3 4) (0 1) (0 1 2) (0 1 2 3) (0 1 2 3 4) (0 1) (0 1 2) (0 1 2 3) (0 1 2 3 4) (0 1) (0 1 2) (0 1 2 3) (0 1 2 3 4) (0 1) (0 1 2) (0 1 2 3) (0 1 2 3 4) (0 1) (0 1 2) (0 1 2 3) (0 1 2 3 4) (0 1) (0 1 2) (0 1 2 3) (0 1 2 3 4) (0 1) (0 1 2) (0 1 2 3) (0 1 2 3 4) (0 1) (0 1 2) (0 1 2 3) (0 1 2 3 4) (0 1) (0 1 2) (0 1 2 3) (0 1 2 3 4) (0 1) (0 1 2) (0 1 2 3) (0 1 2 3 4) (0 1) (0 1 2) (0 1 2 3) (0 1 2 3 4) (0 1) (0 1 2) (0 1 2 3) (0 1 2 3 4) (0 1) (0 1 2) (0 1 2 3) (0 1 2 3 4) (0 1) (0 1 2) (0 1 2 3) (0 1 2 3 4) (0 1) (0 1 2) (0 1 2 3) (0 1 2 3 4) (0 1) (0 1 2) (0 1 2 3) (0 1 2 3 4) (0 1) (0 1 2) (0 1 2 3) (0 1 2 3 4) (0 1) (0 1 2) (0 1 2 3) (0 1 2 3 4) (0 1) (0 1 2) (0 1 2 3) (0 1 2 3 4) (0 1) (0 1 2) (0 1 2 3) (0 1 2 3 4) (0 1) (0 1 2) (0 1 2 3) (0 1 2 3 4) (0 1) (0 1 2) (0 1 2 3) (0 1 2 3 4) (0 1) (0 1 2) (0 1 2 3) (0 1 2 3 4) (0 1) (0 1 2) (0 1 2 3) (0 1 2 3 4) (0 1) (0 1 2) (0 1 2 3) (0 1 2 3 4) (0 1) (0 1 2) (0 1 2 3) (0 1 2 3 4)\nh : n ? ||g n||\nh l\n"),
    ('段18: 入れ子を食って文字列を返す', "j : m ?\n\t||m|| = 1 : `[` (m ' 0 ' 0) `]`\n\t`[` (m ' 0 ' 0) `]` (j (m ' 1~))\nj ((1 2) (3 4) (5 6 7))\n"),
    ('段18: 入れ子の内側の先頭の取り出しが __ にならない', "j : m ?\n\t||m|| = 1 : (m ' 0 ' 0) 7\n\t(m ' 0 ' 0) 0 (j (m ' 1~))~\nj ((1 2) (3 4) (5 6 7))\n"),
    ('段18: 入れ子の尻尾をそのまま返す', "h : m ? m ' 1~\nh ((1 2) (3 4) (5 6 7))\n"),
    ('段18: 尻尾を渡しながら返す', "k : m n ?\n\tn = 0 : m\n\tk (m ' 1~) (n - 1)\nk ((1 2) (3 4) (5 6 7)) 2\n"),
    ('段18: 入れ子の輪 (L を返す)', "a : m ?\n\t||m|| = 1 : (m ' 0)~ 100\n\t(m ' 0)~ 0 (b (m ' 1~))~\nb : m ?\n\t||m|| = 1 : (m ' 0)~ 200\n\t(m ' 0)~ 1 1 (a (m ' 1~))~\na ((1 2) (3 4) (5 6 7) (8 8))\n"),
    ('段18: 入れ子の輪 (文字列を返す)', "a : m ?\n\t||m|| = 1 : `[` (m ' 0 ' 0) `]`\n\t`<` (m ' 0 ' 0) (b (m ' 1~))\nb : m ?\n\t||m|| = 1 : `{` (m ' 0 ' 0) `}`\n\t`-` (m ' 0 ' 0) (a (m ' 1~))\na ((1 2) (3 4) (5 6 7) (8 8))\n"),
    ('段18: 位置がずれる輪 (L・L)', "a : xs ys ?\n\t||xs|| = 1 : (xs ' 0) (ys ' 0) 100\n\t(xs ' 0) (b ys (xs ' 1~))~\nb : us vs ?\n\t||us|| = 1 : (us ' 0) 200\n\t(us ' 0) 0 (a vs (us ' 1~))~\na (1 2 3) (4 5 6 7)\n"),
    ('段18: 位置がずれる輪 (N と L)', "a : m n ?\n\t||m|| = 1 : (m ' 0)~ n~ 100\n\t(m ' 0)~ (b n (m ' 1~))~\nb : n m ?\n\t||m|| = 1 : n~ (m ' 0)~ 200\n\t(m ' 0)~ (a (m ' 1~) n)~\na ((1 2) (3 4) (5 6 7)) (9 9)\n"),
    ('段18: 位置がずれる輪 (文字列)', "a : s t ?\n\t||s|| = 1 : s t `!`\n\t(s ' 0) (b t (s ' 1~))\nb : x y ?\n\t||x|| = 1 : x `?`\n\t(x ' 0) `.` (a (x ' 1~) y)\na `abc` `xyz`\n"),
    ('段19: 器の数が変わる輪 (定数の器を渡して戻る)', "a : xs ys ?\n\t||xs|| = 1 : (xs ' 0) ys~ 100\n\t(xs ' 0) (b (xs ' 1~))~\nb : us ?\n\t||us|| < 6 : (us ' 0) 200\n\t(us ' 0) 0 (a (us ' 5~) (7 7 7))~\na (1 2 3 4 5 6 7 8 9 10 11 12 13) (5 5)\n"),
    ('段19: 辺ごとに食う数・足す数が違う輪', "a : xs ?\n\t||xs|| < 3 : (xs ' 0) 100\n\t(xs ' 0) 1 (b (xs ' 2~))~\nb : xs ?\n\t||xs|| < 2 : (xs ' 0) 200\n\t(xs ' 0) (xs ' 0) 4 4 4 4 4 (a (xs ' 1~))~\na (1 2 3 4 5 6 7 8 9 10 11 12 13)\n"),
    ('段20: 平均が分数の輪を入れ子に', "a : m ?\n\t||m|| = 1 : m~ 100\n\t(m ' 0)~ 0 (b (m ' 1~))~\nb : m ?\n\t||m|| = 1 : m~ 200\n\t(m ' 0)~ 1 (a (m ' 1~))~\na ((1 2) (3 4) (5 6 7) (8 8))\n"),
    ('段20: 平均が分数の輪 300 要素', "ev : xs ?\n\t||xs|| = 1 : (xs ' 0) 100\n\t(xs ' 0) (od (xs ' 1~))~\nod : xs ?\n\t||xs|| = 1 : (xs ' 0) 200\n\t(xs ' 0) 0 (ev (xs ' 1~))~\nl : 1 2 3 4 5 1 2 3 4 5 1 2 3 4 5 1 2 3 4 5 1 2 3 4 5 1 2 3 4 5 1 2 3 4 5 1 2 3 4 5 1 2 3 4 5 1 2 3 4 5 1 2 3 4 5 1 2 3 4 5 1 2 3 4 5 1 2 3 4 5 1 2 3 4 5 1 2 3 4 5 1 2 3 4 5 1 2 3 4 5 1 2 3 4 5 1 2 3 4 5 1 2 3 4 5 1 2 3 4 5 1 2 3 4 5 1 2 3 4 5 1 2 3 4 5 1 2 3 4 5 1 2 3 4 5 1 2 3 4 5 1 2 3 4 5 1 2 3 4 5 1 2 3 4 5 1 2 3 4 5 1 2 3 4 5 1 2 3 4 5 1 2 3 4 5 1 2 3 4 5 1 2 3 4 5 1 2 3 4 5 1 2 3 4 5 1 2 3 4 5\nf : ys ? ||ev ys||\nf l\n"),
    ('段21: `__` を返す底の枝がある輪', "ev : xs ?\n\t||xs|| = 1 : __\n\t(xs ' 0) (od (xs ' 1~))~\nod : xs ?\n\t||xs|| = 1 : (xs ' 0) 7\n\t(xs ' 0) 0 (ev (xs ' 1~))~\nev (1 2 3 4 5)\n"),
    ('段21: 途中の枝が `__` を返す輪', "ev : xs ?\n\t||xs|| = 1 : (xs ' 0) 100\n\t(xs ' 0) = 3 : __\n\t(xs ' 0) (od (xs ' 1~))~\nod : xs ?\n\t||xs|| = 1 : (xs ' 0) 7\n\t(xs ' 0) 0 (ev (xs ' 1~))~\nev (1 2 3 4 5)\n"),
    ('段21: 食い尽くした尻尾で相手の呼びが消える輪', "ev : xs ?\n\t||xs|| = 0 : 5 5\n\t(xs ' 0) (od (xs ' 1~))~\nod : xs ?\n\t||xs|| = 0 : 6 6\n\t(xs ' 0) 0 (ev (xs ' 1~))~\nev (1 2 3)\n"),
    ('段21: 輪が鎖でつながる(a→b→輪)', "a : xs ?\n\t||xs|| = 1 : (xs ' 0) 100\n\t(xs ' 0) (b (xs ' 1~))~\nb : xs ?\n\t||xs|| = 1 : (xs ' 0) 200\n\t(xs ' 0) 1 1 1 1 1 (c (xs ' 2~))~\nc : xs ?\n\t||xs|| < 3 : (xs ' 0) 300\n\t(xs ' 0) 0 (d (xs ' 1~))~\nd : xs ?\n\t||xs|| < 3 : (xs ' 0) 400\n\t(xs ' 0) 0 0 0 (c (xs ' 1~))~\na (1 2 3 4 5 6 7 8 9 10 11 12 13 14)\n"),
    ('段21: 輪から別の輪を底で呼ぶ', "p : xs ?\n\t||xs|| < 3 : (xs ' 0) (c xs)~\n\t(xs ' 0) (q (xs ' 1~))~\nq : xs ?\n\t||xs|| < 3 : (xs ' 0) 9 (c xs)~\n\t(xs ' 0) 1 1 (p (xs ' 1~))~\nc : xs ?\n\t||xs|| = 1 : (xs ' 0) 300\n\t(xs ' 0) 0 (d (xs ' 1~))~\nd : xs ?\n\t||xs|| = 1 : (xs ' 0) 400\n\t(xs ' 0) 0 0 0 (c (xs ' 1~))~\np (1 2 3 4 5 6 7 8)\n"),
    ('段21: 輪から別の輪を定数の器で呼ぶ・ラベルの取り違え', "p : xs ?\n\t||xs|| < 3 : (xs ' 0) 5\n\t(xs ' 0) (c (3 4 5 6))~ (q (xs ' 1~))~\nq : xs ?\n\t||xs|| < 3 : (xs ' 0) 9\n\t(xs ' 0) 1 (p (xs ' 1~))~\nc : xs ?\n\t||xs|| = 1 : (xs ' 0) 300\n\t(xs ' 0) 0 (d (xs ' 1~))~\nd : xs ?\n\t||xs|| = 1 : (xs ' 0) 400\n\t(xs ' 0) 0 0 0 (c (xs ' 1~))~\np (1 2 3 4 5 6 7 8)\n"),
    ('段21: 文字列の輪の `__` と字面', "ev : s ?\n\t||s|| = 1 : __\n\t`-` (s ' 0) (od (s ' 1~))\nod : s ?\n\t||s|| = 1 : `+`\n\t`.` (s ' 0) (ev (s ' 1~))\nev `abcde`\n"),
    ('段22: `__` になりうる要素を残りと並べる', "f : xs ?\n\t(xs ' 0) (xs ' 5) (xs ' 1) 9\nf (1 2 3)\n"),
    ('段22: 輪の途中で要素が `__` になる', "ev : xs ?\n\t||xs|| < 2 : (xs ' 0) (xs ' 1)\n\t(xs ' 0) (xs ' 2) (od (xs ' 1~))~\nod : xs ?\n\t||xs|| < 2 : (xs ' 0) (xs ' 1) (xs ' 7)\n\t(xs ' 1) (xs ' 3) 0 (ev (xs ' 1~))~\nw : xs ? 0 (ev xs)~ 0\nw (1 2 3 4 5 6)\n"),
    ('段22: 1 個だけ残りうる関数の結果を展開で使う', "f : xs ? (xs ' 7) (xs ' 0)\ng : xs ? 0 (f xs)~ 5\ng (1 2)\n"),
    ('段22: 入れ子を返す輪 (尻尾をたどって返す)', "a : m ?\n\t||m|| < 3 : m\n\tb (m ' 1~)\nb : m ?\n\t||m|| < 3 : (m ' 0) (7 7)\n\ta (m ' 2~)\na ((1 2) (3 4) (5 6) (7 8) (9 9) (1 1) (2 2))\n"),
    ('段22: 入れ子を返す輪 (底で内側と字面を並べる)', "a : m ?\n\t||m|| < 3 : (m ' 0) (1 2 3)\n\tb (m ' 1~)\nb : m ?\n\t||m|| < 3 : (m ' 0) (7 7)\n\ta (m ' 2~)\na ((1 2) (3 4) (5 6) (7 8) (9 9) (1 1) (2 2))\n"),
    ('段22: 入れ子を返す輪 (器が 2 つ)', "a : m n ?\n\t||m|| < 3 : (m ' 0) (n ' 0 n ' 0)\n\tb (m ' 1~) n\nb : m n ?\n\t||m|| < 3 : (m ' 0) (7 7)\n\ta (m ' 2~) n\na ((1 2) (3 4) (5 6) (7 8) (9 9) (1 1) (2 2)) (4 4)\n"),
    ('段23: 入れ子の要素が範囲の外(定数 2 個以上は残る)', "f : m ? (m ' 0) (m ' 5) (m ' -1) (m ' 1) (m ' 9)\nf ((1 2) (3 4) (5 6))\n"),
    ('段23: 入れ子の要素が範囲の外 (2 つ)', "f : m ? (m ' 0) (m ' 5) (m ' -1) (m ' 1) (m ' 9)\nf ((1 2) (3 4))\n"),
    ('段23: 入れ子の要素が範囲の外 長さを測る', "f : m ? (m ' 0) (m ' 5) (m ' -1) (m ' 1) (m ' 9)\ng : m ? ||f m||\ng ((1 2) (3 4) (5 6))\n"),
    ('段23: 文字だけの並置(消える文字あり)', "f : s ? (s ' 0) (s ' 5) (s ' -1) (s ' 1) (s ' 9)\nf `abc`\n"),
    ('段23: 文字だけの並置の輪', "ev : s ?\n\t||s|| < 2 : (s ' 0) (s ' -1)\n\t(s ' 0) (s ' 4) (od (s ' 1~))\nod : s ?\n\t||s|| < 2 : (s ' 0) (s ' -1)\n\t(s ' -1) (s ' 3) (ev (s ' 1~))\nev `abcdefgh`\n"),
    ('段23: 素通しを挟まない(1 個残りうる結果を使わない)', "f : xs ? 3 (xs ' 7) (xs ' 0)\nid : ys ? ys\nid (f (1 2))\n"),
    ('段24: 入れ子の内側の要素が範囲の外', "f : xs ? (xs ' 0 xs ' 5 xs ' 1 9) (xs ' 2 xs ' 8 xs ' 0 xs ' -1)\nf (1 2 3)\n"),
    ('段24: 入れ子の内側の要素が範囲の外 長さを測る', "f : xs ? (xs ' 0 xs ' 5 xs ' 1 9) (xs ' 0 xs ' 7 xs ' -1) (7 7)\ng : ys ? ||f ys||\ng (4 5)\n"),
    ('段25: 入れ子の内側に (a b)~ を展開', "f : xs ? (1 2) (((xs ' 0) (xs ' 1))~ 9)\nf (4 5 6)\n"),
    ('段25: 入れ子の内側に (a b)~ を 2 つ', "f : xs ? (1 2) (((xs ' 0) 7)~ ((xs ' 1) 8)~)\nf (4 5 6)\n"),
    ('段25: 入れ子の内側の (a b)~ に範囲外が混ざる', "f : xs ? (1 2) (((xs ' 0) (xs ' 7))~ ((xs ' 1) (xs ' 9))~ 3)\nf (4 5 6)\n"),
    ('段25: L の組み立てに (a b)~ と入れ子の (a (b c)~)~', "f : xs ? ((xs ' 0) (xs ' 5))~ 9 ((xs ' 1) ((xs ' 2) 3)~)~\nf (4 5 6)\n"),
    ('段25: 文字列の連結の Int 項', "g : n ? n * n\nf : n ? `<` (g n) `>` (g n)\nf 3\n"),
    ('段26: 素通しの関数の結果を展開', "id : xs ? xs\nf : xs ? (id xs)~ 9\nf (4 5 6)\n"),
    ('段26: 素通しの関数に字面の定数端スライス', "id : xs ? xs\nf : xs ? (id (xs ' 1~))~ 9\nf (4 5 6)\n"),
    ('段26: 素通しの関数の第 2 引数を返す', "snd : xs ys ? ys\nf : xs ys ? (snd xs ys)~ (xs ' 0)\nf (1 2) (3 4 5)\n"),
    ('段26: 素通しを 2 段重ねる', "a : xs ? xs\nb : xs ? (a xs)\nf : xs ? (b xs)~ 9\nf (4 5 6)\n"),
    ('段26: 条件で字面か引数を返す関数の展開', "pick : xs ?\n\t||xs|| > 2 : xs\n\t(7 8)\nf : xs ? (pick xs)~ (pick (xs ' 1~))~ ||xs||\nf (4 5 6 7)\n"),
    ('段26: 条件の関数の展開を入れ子の内側で', "pick : xs ?\n\t||xs|| > 2 : xs\n\t(7 8)\nf : xs ? ((pick xs)~ 1) ((pick xs)~ 2 (pick xs)~)\nf (4 5 6)\n"),
    ('段26: 展開の結果を別の組み立てが展開', "id : xs ? xs\ng : xs ? (id xs)~ (id xs)~ 0\nf : xs ? (g xs)~ ||g xs||\nf (4 5)\n"),
    ('段26: 最上位で素通しの関数の結果を展開', "id : xs ? xs\n(id (1 2 3))~ 4\n"),
    ('段27: 組み立てた並びを引数に渡す', "len : xs ? ||xs||\nf : n ? 5 (len (n n n))\nf 3\n"),
    ('段27: 組み立てを引数に直接(旧: 断り)', "n : xs ? ||xs||\ng : a ? n (a a)\ng 1\n"),
    ('段27: 入れ子の組み立てを引数に直接(旧: 断り)', "n : m ? ||m||\ng : a ? n ((a a) (a a))\ng 1\n"),
    ('段27: 引数の並びに展開と要素', "sum : xs ?\n\t||xs|| = 1 : xs ' 0\n\t(xs ' 0) + (sum (xs ' 1~))\nf : xs ? sum ((xs ' 0) xs~ 100)\nf (4 5 6)\n"),
    ('段27: 引数の並びを器を返す関数に渡す', "id : xs ? xs\nf : xs ? (id ((xs ' 0) 7 8))~ 9\nf (4 5 6)\n"),
    ('段27: 引数の並びが仮引数を使わない', "len : xs ? ||xs||\nf : n ? n + (len (1 2 3))\nf 4\n"),
    ('段27: 引数の並びが 2 つ', "cat : xs ys ? xs~ ys~\nf : a b ? cat (a b) (b a a)\nf 1 2\n"),
    ('段28: 自分への末尾呼びに新しい定数の器', "f : xs ys ?\n\t||xs|| = 1 : ys~ (xs ' 0)\n\tf (xs ' 1~) ((xs ' 0) (ys ' 0))\nf (4 5 6) (1 2)\n"),
    ('段28: 新しい器が 3 つ', "f : xs ys ?\n\t||xs|| = 1 : ys~ (xs ' 0)\n\tf (xs ' 1~) ((xs ' 0) (ys ' 0) (ys ' 1))\nf (4 5 6) (1 2)\n"),
    ('段28: 新しい器と Int の引数', "f : xs ys n ?\n\t||xs|| = 1 : ys~ n\n\tf (xs ' 1~) ((xs ' 0) (ys ' 0)) (n + 1)\nf (4 5 6) (1 2) 0\n"),
    ('段28: 輪を渡る呼びに新しい定数の器', "a : xs ys ?\n\t||xs|| < 4 : ys~ (xs ' 0)\n\tb (xs ' 3~) ((xs ' 0) 9)\nb : xs ys ?\n\t||xs|| < 4 : ys~ 5\n\ta (xs ' 3~) ((xs ' 1) 8)\na (4 5 6 7 8 9 1 2 3 4) (1 2)\n"),
    ('段28: 最上位で 1 個だけ残ると Int(要素 2 つ・範囲外)', "f : xs ? (xs ' 0) (xs ' 5)\nf (4 5 6)\n"),
    ('段28: 最上位で 2 個残る', "f : xs ? (xs ' 0) (xs ' 1)\nf (4 5 6)\n"),
    ('段28: 最上位で全部が消える', "f : xs ? (xs ' 7) (xs ' 8)\nf (1 2)\n"),
    ('段28: 最上位 1 個だけ(a と 1 / a)', "f : a ? a (1 / a)\nf 2\n"),
    ('段28: 最上位 1 個だけ(7 番目と 0 番目)', "f : xs ? (xs ' 7) (xs ' 0)\nf (1 2)\n"),
    ('段28: 旗を関数を挟んで運ぶ', "f : xs ? (xs ' 7) (xs ' 0)\ng : xs ? f xs\ng (1 2)\n"),
    ('段28: 旗を条件の枝で運ぶ(Int になる側)', "g : xs ? (xs ' 1) (xs ' 5)\nh : xs ?\n\t||xs|| > 2 : g xs\n\txs ' 0~\nh (4 5 6)\n"),
    ('段28: 旗を条件の枝で運ぶ(器のまま)', "g : xs ? (xs ' 2) (xs ' 5)\nh : xs ?\n\t||xs|| > 2 : g xs\n\txs ' 0~\nh (4 5)\n"),
    ('段28: 旗 他の枝の器は器のまま', "g : xs ? (xs ' 0) (xs ' 5)\nf : xs ?\n\t||xs|| > 5 : 9 8\n\tg xs\nf (4 5 6)\n"),
    ('段29: 素通しを挟んで旗を運ぶ', "f : xs ? (xs ' 7) (xs ' 0)\nid : ys ? ys\nh : xs ? id (f xs)\nh (1 2)\n"),
    ('段29: 素通しへ直に渡して旗を運ぶ', "f : xs ? (xs ' 7) (xs ' 0)\nid : ys ? ys\nid (f (1 2))\n"),
    ('段29: 素通しを 2 段(器のまま)', "f : xs ? (xs ' 1) (xs ' 0)\nid : ys ? ys\nh : xs ? id (id (f xs))\nh (1 2)\n"),
    ('段29: 素通しを条件の枝で(Int になる側)', "f : xs ? (xs ' 7) (xs ' 0)\nid : ys ? ys\ng : xs ?\n\t||xs|| > 1 : id (f xs)\n\txs ' 0 xs ' 0\ng (1 2)\n"),
    ('段29: 素通しの結果の長さ側(旗は使わない)', "f : xs ? (xs ' 0) (xs ' 5)\nid : ys ? ys\nh : xs ? id (f xs)\nh (1 2)\n"),
    ('段29: 新しい器の大きさが別の器に頼る', "f : xs ys ?\n\t||xs|| = 1 : ys~ (xs ' 0)\n\tf (xs ' 1~) (xs~ 7)\nf (4 5 6) (1 2)\n"),
    ('段29: 新しい器が自分の第 1 要素と別の器', "f : xs ys ?\n\t||xs|| = 1 : ys~ (xs ' 0)\n\tf (xs ' 1~) ((ys ' 0) xs~)\nf (4 5 6) (1 2)\n"),
    ('段29: 新しい器が別の変わらない器に頼る', "f : xs zs ys ?\n\t||xs|| = 1 : ys~ (xs ' 0)\n\tf (xs ' 1~) zs (zs~ (xs ' 0) 9)\nf (4 5 6) (7 8) (1 2)\n"),
    ('段30: 枝で返す引数が変わる関数 旗のある側を返す(Int)', "f : xs ? (xs ' 7) (xs ' 0)\nk : ys zs ?\n\t||zs|| > 3 : zs\n\tys\ng : xs ? k (f xs) xs\ng (1 2)\n"),
    ('段30: 枝で返す引数が変わる関数 旗のない側を返す(器)', "f : xs ? (xs ' 7) (xs ' 0)\nk : ys zs ?\n\t||zs|| > 1 : zs\n\tys\ng : xs ? k (f xs) xs\ng (1 2)\n"),
    ('段30: 枝で返す引数が変わる関数 第 1 引数の枝', "f : xs ? (xs ' 7) (xs ' 0)\nk : ys zs ?\n\t||zs|| > 1 : ys\n\tzs\ng : xs ? k (f xs) xs\ng (1 2)\n"),
    ('段30: 枝で返す引数が変わる関数 両方の引数が旗つき', "f : xs ? (xs ' 7) (xs ' 0)\nh : xs ? (xs ' 5) (xs ' 1)\nk : ys zs ?\n\t||zs|| > 1 : ys\n\tzs\ng : xs ? k (f xs) (h xs)\ng (1 2)\n"),
    ('段30: 枝で返す引数が変わる関数 もう一方の枝', "f : xs ? (xs ' 7) (xs ' 0)\nh : xs ? (xs ' 5) (xs ' 1)\nk : ys zs ?\n\t||zs|| > 5 : ys\n\tzs\ng : xs ? k (f xs) (h xs)\ng (1 2)\n"),
    ('段30: 輪を渡る呼びで新しい器が別の器の長さに頼る', "a : xs ys ?\n\t||ys|| < 4 : xs~ ys~\n\tb (ys ' 3~) ((xs ' 0) xs~ 9)\nb : xs ys ?\n\t||xs|| < 4 : xs~ ys~ 5\n\ta (xs ' 3~) ((ys ' 1) 6)\na (1 2) (4 5 6 7 8 9 1 2 3 4)\n"),
    ('段31: 自分への呼びの新しい器が入れ子の内側に頼る', "f : m ys ?\n\t||m|| = 1 : ys~ (m ' 0)~\n\tf (m ' 1~) ((m ' 0)~ 9)\nf ((1 2) (3 3) (5 6)) (7 8)\n"),
    ('段31: 自分への呼びの新しい器が入れ子の全体に頼る', "f : m ys ?\n\t||m|| = 1 : ys~ (m ' 0)~\n\tf (m ' 1~) (m~ 9)\nf ((1 2) (3 3) (5 6)) (7 8)\n"),
    ('段31: 入れ子を返す関数の自分への呼びの新しい器(定数)', "f : xs ys ?\n\t||xs|| = 1 : ys (xs ' 0 7)\n\tf (xs ' 1~) ((xs ' 0) 9)\nf (4 5 6) (1 2)\n"),
    ('段31: 入れ子を返す関数の新しい器が入れ子の内側に頼る', "f : m ys ?\n\t||m|| = 1 : ys (m ' 0)\n\tf (m ' 1~) ((m ' 0)~ 9)\nf ((1 2) (3 3) (5 6)) (7 8)\n"),
    ('段31: 入れ子を返す関数の新しい器が変わらない器に頼る', "f : xs zs ys ?\n\t||xs|| = 1 : ys zs\n\tf (xs ' 1~) zs (zs~ (xs ' 0))\nf (4 5 6) (7 8) (1 2)\n"),
    ('段31: 入れ子を返す 2 関数が新しい器を渡し合う', "a : xs ys ?\n\t||xs|| < 3 : (xs ' 0 1) ys\n\tb (xs ' 2~) ((xs ' 0) 9)\nb : xs ys ?\n\t||xs|| < 3 : (xs ' 0 3) ys\n\ta (xs ' 2~) ((xs ' 0) 8)\na (4 5 6 7 8 9 1 2 3 4) (1 2)\n"),
    ('段32: 輪を渡る呼びの新しい器が入れ子の内側に頼る', "a : m ys ?\n\t||m|| < 3 : ys~ 1\n\tb (m ' 2~) ((m ' 0)~ 9)\nb : m ys ?\n\t||m|| < 3 : ys~ 2\n\ta (m ' 2~) ((m ' 1)~ 8)\na ((1 2) (3 3) (4 5 6) (7 7) (8 9) (1 1)) (5 5)\n"),
    ('段32: 輪を渡る呼びで入れ子の 1 つの内側をそのまま渡す', "a : m ys ?\n\t||m|| < 3 : ys~ (m ' 0)~\n\tb (m ' 2~) (m ' 1)\nb : m ys ?\n\t||m|| < 3 : ys~ 2\n\ta (m ' 2~) ((m ' 0)~ (m ' 1)~)\na ((1 2) (3 3) (4 5 6) (7 7) (8 9) (1 1)) (5 5)\n"),
    ('段33: 内側頼みの位置の器の末尾を別の関数へ渡す', "a : m ys ?\n\t||m|| < 3 : ys~ 1\n\tb (m ' 2~) ((m ' 0)~ 9)\nb : m ys ?\n\t||m|| < 3 : ys~ 2\n\ta (m ' 2~) (ys ' 1~)\na ((1 2) (3 3) (4 5 6) (7 7) (8 9) (1 1)) (5 5 5)\n"),
    ('段33: 内側頼みの位置の器をそのまま別の関数へ渡す', "a : m ys ?\n\t||m|| < 3 : ys~ 1\n\tb (m ' 2~) ((m ' 0)~ 9)\nb : m ys ?\n\t||m|| < 3 : ys~ 2\n\ta (m ' 2~) ys\na ((1 2) (3 3) (4 5 6) (7 7) (8 9) (1 1)) (5 5 5)\n"),
    ('段33: 内側頼みの位置の器をそのまま渡し合いながら撒く', "a : m ys ?\n\t||m|| < 3 : ys~ 1\n\t(m ' 0)~ (b (m ' 2~) ((m ' 1)~ 9))~\nb : m ys ?\n\t||m|| < 3 : ys~ 2\n\t(m ' 1)~ (a (m ' 2~) ys)~\na ((1 2) (3 3) (4 5 6) (7 7) (8 9) (1 1)) (5 5)\n"),
    ('段33: 輪の新しい器が器の長さと入れ子の内側の総和の両方に頼る', "a : m xs ys ?\n\t||m|| < 4 : ys~ xs~ 1\n\tb (m ' 3~) ((m ' 0)~ xs~ 9)\nb : m ys ?\n\t||m|| < 4 : ys~ 2\n\ta (m ' 3~) (4 4) ((m ' 1)~ 8)\na ((1 2) (3 3) (4 5 6) (7 7) (8 9) (1 1) (2 2) (3 3) (4 4) (5 5) (6 6) (7 7)) (5 5 5) (6 6)\n"),
    ('段33: 自分への呼びの新しい器が両方に頼る', "f : m xs ys ?\n\t||m|| = 1 : ys~ (m ' 0)~\n\tf (m ' 1~) xs ((m ' 0)~ xs~)\nf ((1 2) (3 3 3) (5 6)) (9 9 9) (7 8)\n"),
    ('段32: 輪を渡る呼びで内側頼みの器を撒きながら(通常の再帰)', "a : m ys ?\n\t||m|| < 3 : ys~ 1\n\t(m ' 0)~ (b (m ' 2~) ((m ' 1)~ 9))~\nb : m ys ?\n\t||m|| < 3 : ys~ 2\n\t(m ' 1)~ (a (m ' 2~) ((m ' 0)~ 8))~\na ((1 2) (3 3) (4 5 6) (7 7) (8 9) (1 1)) (5 5)\n"),
    ('段32: 輪を渡る呼びで 1 個ずつ食う', "a : m ys ?\n\t||m|| < 3 : ys~ 1\n\tb (m ' 1~) ((m ' 0)~ 9)\nb : m ys ?\n\t||m|| < 3 : ys~ 2\n\ta (m ' 1~) ((m ' 0)~ 8)\na ((1 2) (3 3) (4 5 6) (7 7) (8 9) (1 1)) (5 5 5)\n"),
    ('段32: 自分への呼びで入れ子の 1 つの内側をそのまま渡す(L)', "f : m ys ?\n\t||m|| = 1 : ys~ (m ' 0)~\n\tf (m ' 1~) (m ' 0)\nf ((1 2) (3 3 3) (5 6)) (7 8)\n"),
    ('段32: 自分への呼びで入れ子の 1 つの内側をそのまま渡す(入れ子を返す)', "f : m ys ?\n\t||m|| = 1 : ys (m ' 0)\n\tf (m ' 1~) (m ' 0)\nf ((1 2) (3 3 3) (5 6)) (7 8)\n"),
    ('段27: __ になりうる関数の展開 残りが 2 個以上(残る)', "pick : xs ?\n\t||xs|| > 2 : xs\nf : xs ? (pick xs)~ 7 8\nf (4 5 6)\n"),
    ('段27: __ になりうる関数の展開 残りが 2 個以上(消える)', "pick : xs ?\n\t||xs|| > 2 : xs\nf : xs ? (pick xs)~ 7 8\nf (4 5)\n"),
    ('段27: 尽きる末尾の展開 残りが 2 個以上', "rest : xs ? xs ' 2~\nf : xs ? (rest xs)~ 1 2\nf (4 5)\n"),
    ('段27: 尽きる末尾の展開 残りが 2 個以上(残る)', "rest : xs ? xs ' 2~\ng : xs ? (rest xs)~ 1 2 (rest (xs ' 1~))~\ng (4 5 6)\n"),
    ('段27: 範囲外になりうるスライスの展開を入れ子の内側で', "f : xs ? (1 2) ((xs ' 5~)~ 7 8)\nf (4 5 6)\n"),
    ('段27: 尽きる末尾の展開を重ねる', "f : xs ? (xs ' 5~)~ 7 (xs ' 1~)~ 8\nf (4 5 6)\n"),
    ("組み立て 入れ子 大きな内側", "f : a ? (a a a a a a a a a a a a) (a a a a a a a a a a a a a a a a a a a a a a a a)\nf 4\n"),
]
STR_CASES += [
    ('段34: 入れ子の展開 `(g xs)~` を L の組み立てで使う(旧: 記述子のまま写していた不具合の修正)', "g : xs ? ((xs ' 0) 1) ((xs ' 0) 2)\nf : xs ? (g xs)~ 1\nf (4 5 6 7)\n"),
    ('段34: 入れ子を返す関数が累積を伸ばして回り、底で内側の要素に写して返す', "f : xs ys ?\n\t||xs|| = 1 : (ys~ (xs ' 0)) (xs ' 0 7)\n\tf (xs ' 1~) (ys~ (xs ' 0))\nf (4 5 6) (1 2)\n"),
    ('段34: 同上・累積が入口より十分長い', "f : xs ys ?\n\t||xs|| = 1 : (ys~ (xs ' 0)) (xs ' 0 7)\n\tf (xs ' 1~) (ys~ (xs ' 0))\nf (4 5 6 7 8 9 1) (1 2 3 4 5 6 7 8 9 10 11 12)\n"),
    ('段34: 入れ子を返す輪で累積を伸ばして渡す', "a : xs ys ?\n\t||xs|| < 3 : (ys~ (xs ' 0)) (xs ' 0 7)\n\tb (xs ' 2~) (ys~ (xs ' 0))\nb : xs ys ?\n\t||xs|| < 3 : (ys~ (xs ' 0)) (xs ' 0 8)\n\ta (xs ' 2~) (ys~ (xs ' 0))\n" + "a (4 5 6 7 8 9 1 2 3 4) (1 2)\n"),
    ('段34: 同上・器が長い', "a : xs ys ?\n\t||xs|| < 3 : (ys~ (xs ' 0)) (xs ' 0 7)\n\tb (xs ' 2~) (ys~ (xs ' 0))\nb : xs ys ?\n\t||xs|| < 3 : (ys~ (xs ' 0)) (xs ' 0 8)\n\ta (xs ' 2~) (ys~ (xs ' 0))\n" + "a (4 5 6 7 8 9 1 2 3 4 5 6 7 8 9 1 2 3 4 5 6 7) (1 2 3 4 5 6 7 8 9 0 1 2 3 4 5)\n"),
    ('段34: 内側頼みの位置ごとに係数が違う輪', "a : m ys zs ?\n\t||m|| < 3 : ys~ zs~ zs~ zs~ 1\n\tb (m ' 2~) ((m ' 0)~ 9) ((m ' 1)~ 8)\nb : m ys zs ?\n\t||m|| < 3 : ys~ ys~ zs~ 2\n\ta (m ' 2~) ((m ' 1)~ 7) ((m ' 0)~ 6)\na ((1 2) (3 3) (4 5 6) (7 7) (8 9) (1 1)) (5 5) (6 6 6)\n"),
]
STR_CASES += [
    ('段36: 輪の相手と累積・食う器の位置が違う', "a : xs ys ?\n\t||xs|| < 3 : (ys~ (xs ' 0)) (xs ' 0 7)\n\tb (ys~ (xs ' 0)) (xs ' 2~)\nb : vs ws ?\n\t||ws|| < 3 : (vs~ (ws ' 0) 5) (ws ' 0 8)\n\ta (ws ' 2~) (vs~ (ws ' 0))\na (4 5 6 7 8 9 1 2 3 4) (1 2)\n"),
    ('段36: 輪・3 引数で位置が違う', "a : xs ys zs ?\n\t||xs|| < 3 : (ys~ (xs ' 0)) (xs ' 0 7) zs\n\tb zs (xs ' 2~) (ys~ (xs ' 0))\nb : us ws vs ?\n\t||ws|| < 3 : (vs~ (ws ' 0) 5) (ws ' 0 8)\n\ta (ws ' 2~) (vs~ (ws ' 0)) us\na (4 5 6 7 8 9 1 2 3 4) (1 2) (3 3)\n"),
    ('段36: 自分への呼びで累積を 2 つ同時に伸ばす', "f : xs ys zs ?\n\t||xs|| = 1 : (ys~ (xs ' 0)) (zs~ (xs ' 0) 5)\n\tf (xs ' 1~) (ys~ (xs ' 0)) (zs~ (xs ' 0) 1)\nf (4 5 6 7 8) (1 2) (9 9)\n"),
    ('段36: 輪で累積を 2 つ同時に伸ばし、位置も入れ替える', "a : xs ys zs ?\n\t||xs|| < 3 : (ys~ (xs ' 0)) (zs~ (xs ' 0) 7)\n\tb (xs ' 2~) (zs~ (xs ' 0)) (ys~ (xs ' 0) 3)\nb : ws us vs ?\n\t||ws|| < 3 : (us~ (ws ' 0)) (vs~ (ws ' 0) 8)\n\ta (ws ' 2~) (vs~ (ws ' 0)) (us~ (ws ' 0) 4)\na (4 5 6 7 8 9 1 2 3 4) (1 2) (3 3)\n"),
]
STR_CASES += [
    ('段37: L の累積を 2 つ同時に伸ばし、両方を返す', "f : xs ys zs ?\n\t||xs|| = 1 : ys~ zs~ (xs ' 0)\n\tf (xs ' 1~) (ys~ (xs ' 0)) (zs~ (xs ' 0) 1)\nf (4 5 6 7 8) (1 2) (9 9)\n"),
    ('段37: 伸ばした累積の片方をそのまま返す', "f : xs ys zs ?\n\t||xs|| = 1 : zs\n\tf (xs ' 1~) (ys~ (xs ' 0)) (zs~ (xs ' 0) 1)\nf (4 5 6 7 8) (1 2) (9 9)\n"),
    ('段37: 累積を 2 つ伸ばして、末尾に足して返す', "f : s a b ?\n\t||s|| = 1 : a~ b~ 0\n\tf (s ' 1~) (a~ (s ' 0)) (b~ (s ' 0) 2)\nf (4 5 6 7 8) (1 2) (9 9)\n"),
    ('段37: 2 つ伸ばして片方を返す', "f : s a b ?\n\t||s|| = 1 : b\n\tf (s ' 1~) (a~ (s ' 0)) (b~ (s ' 0) 2)\nf (4 5 6) (1 2) (9 9)\n"),
    ('段37: 文字列の累積を 2 つ同時に伸ばす', "f : s a b ?\n\t||s|| = 1 : a b `!`\n\tf (s ' 1~) (a `x`) (b `yy`)\nf `abcd` `1` `2`\n"),
    ('段37: 文字列の累積 2 つの片方を返す', "f : s a b ?\n\t||s|| = 1 : b\n\tf (s ' 1~) (a `x`) (b `yy`)\nf `abcd` `1` `2`\n"),
]
STR_CASES += [
    ('段38: L を返す輪で累積を伸ばして渡す(定数の要素)', "a : xs ys ?\n\t||xs|| < 3 : ys~ 1\n\tb (xs ' 2~) (ys~ 7)\nb : xs ys ?\n\t||xs|| < 3 : ys~ 2\n\ta (xs ' 2~) (ys~ 9)\na (4 5 6 7 8 9 1 2 3 4) (1 2)\n"),
    ('段38: 同上・要素が式', "a : xs ys ?\n\t||xs|| < 3 : ys~ (xs ' 0)\n\tb (xs ' 2~) (ys~ (xs ' 0))\nb : xs ys ?\n\t||xs|| < 3 : ys~ (xs ' 0) 8\n\ta (xs ' 2~) (ys~ (xs ' 0) 3)\na (4 5 6 7 8 9 1 2 3 4) (1 2)\n"),
    ('段38: 累積をそのまま返す枝を持つ輪', "a : xs ys ?\n\t||xs|| < 3 : ys\n\tb (xs ' 2~) (ys~ (xs ' 0) 1)\nb : xs ys ?\n\t||xs|| < 3 : ys~ 4\n\ta (xs ' 2~) (ys~ (xs ' 0))\na (4 5 6 7 8 9 1 2 3 4 5 6 7 8 9 1 2 3 4 5 6) (1 2)\n"),
    ('段38: 輪を回りながら撒く枝と累積', "a : xs ys ?\n\t||xs|| < 3 : ys~ (xs ' 0)\n\t(xs ' 0) (b (xs ' 1~) (ys~ (xs ' 0)))~ 5\nb : xs ys ?\n\t||xs|| < 3 : ys~ (xs ' 0) 8\n\t(xs ' 0) (a (xs ' 1~) (ys~ (xs ' 0) 3))~ 6\na (4 5 6 7 8 9 1 2 3 4) (1 2)\n"),
    ('段38: 位置の違う輪(新しい器の道)', "a : xs ys ?\n\t||xs|| < 3 : ys~ 1\n\tb (ys~ (xs ' 0)) (xs ' 2~)\nb : vs ws ?\n\t||ws|| < 3 : vs~ 2\n\ta (ws ' 2~) (vs~ (ws ' 0))\na (4 5 6 7 8 9 1 2 3 4) (1 2)\n"),
]
STR_CASES += [
    ('段39: 文字列を返す輪で累積を伸ばして渡す', "a : s acc ?\n\t||s|| < 3 : acc `!`\n\tb (s ' 2~) (acc `x`)\nb : s acc ?\n\t||s|| < 3 : acc `?` `?`\n\ta (s ' 2~) (acc `yy`)\na `abcdefghij` `01`\n"),
    ('段39: 累積をそのまま返す枝を持つ文字列の輪', "a : s acc ?\n\t||s|| < 3 : acc\n\tb (s ' 2~) (acc `x`)\nb : s acc ?\n\t||s|| < 3 : acc `-`\n\ta (s ' 2~) (acc `yy`)\na `abcdefghijklmnop` `01`\n"),
    ('段39: 文字の要素を足す文字列の輪', "a : s acc ?\n\t||s|| < 3 : acc (s ' 0) `!`\n\tb (s ' 2~) (acc (s ' 0))\nb : s acc ?\n\t||s|| < 3 : `<` acc\n\ta (s ' 2~) (acc (s ' 0) `.`)\na `abcdefghijklmnopqrstuvwxyz` `01`\n"),
]
STR_CASES += [
    ('段40: 条件から範囲内と分かる取り出し(<= と & と複数の枝)', "f : xs ys ?\n\t||xs|| <= 2 : ys~ 1\n\t||xs|| >= 4 & ||ys|| > 0 : f (xs ' 3~) (ys~ (xs ' 3))\n\tf (xs ' 1~) (ys~ (xs ' 2))\nf (4 5 6 7 8 9 1 2 3 4) (1 2)\n"),
    ("段40: 輪で `xs ' 1` を累積に足す(||xs|| < 3 が偽の枝)", "a : xs ys ?\n\t||xs|| < 3 : ys~ 1\n\tb (xs ' 2~) (ys~ (xs ' 1))\nb : xs ys ?\n\t||xs|| < 3 : ys~ 2\n\ta (xs ' 2~) (ys~ (xs ' 2))\na (4 5 6 7 8 9 1 2 3 4) (1 2)\n"),
    ('段40: 位置の違う累積を作業領域を共有して渡す(L)', "a : xs ys ?\n\t||xs|| < 3 : ys~ 1\n\tb (ys~ (xs ' 0)) (xs ' 2~)\nb : vs ws ?\n\t||ws|| < 3 : vs~ 2\n\ta (ws ' 2~) (vs~ (ws ' 0) 4)\na (4 5 6 7 8 9 1 2 3 4 5 6 7 8 9 1 2 3 4 5 6 7 8 9) (1 2)\n"),
    ('段40: 位置の違う累積を共有して渡す(文字列)', "a : s acc ?\n\t||s|| < 3 : acc `!`\n\tb (acc `x`) (s ' 2~)\nb : t bcc ?\n\t||bcc|| < 3 : t `?`\n\ta (bcc ' 2~) (t `yy`)\na `abcdefghijklmnop` `01`\n"),
    ('段40: 内側頼みの位置が 2 つで、どちらにも大きな定数の器が渡る輪(上界の不足の修正)', "a : m ys zs ?\n\t||m|| < 3 : ys~ zs~ 1\n\tb (m ' 2~) ((m ' 0)~ 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9) ((m ' 1)~ 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9)\nb : m ys zs ?\n\t||m|| < 3 : ys~ zs~ 2\n\ta (m ' 2~) ((m ' 1)~ 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9) ((m ' 0)~ 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9)\na ((1 2) (3 3) (4 5 6) (7 7) (8 9) (1 1)) (5 5) (6 6)\n"),
]
STR_CASES += [
    ('段41: 器どうしの長さの比較(||xs|| < ||ys|| + 2)から範囲内と分かる取り出し', "a : xs ys ?\n\t||xs|| < ||ys|| + 2 : ys~ 1\n\t||xs|| >= 4 : a (xs ' 1~) (ys~ (xs ' 3))\n\ta (xs ' 1~) (ys~ (xs ' 0))\na (4 5 6 7 8 9 1 2 3 4) (1 2)\n"),
    ('段41: 係数つきの条件と、||xs|| の式・負の添字の取り出し', "a : xs ys ?\n\t3 * ||xs|| < 7 : ys~ 1\n\ta (xs ' 2~) (ys~ (xs ' (||xs|| - 3)) (xs ' -3))\na (4 5 6 7 8 9 1 2 3 4) (1 2)\n"),
    ('段41: 食う器が枝ごとに違う輪で累積を共有(a・b とも 2 通りの枝)', "a : xs ys acc ?\n\t||xs|| < 2 & ||ys|| < 2 : acc~ 1\n\t||xs|| >= 2 : b (xs ' 1~) ys (acc~ (xs ' 0) 1)\n\tb xs (ys ' 1~) (acc~ (ys ' 0))\nb : xs ys acc ?\n\t||xs|| < 2 & ||ys|| < 2 : acc~ 2\n\t||ys|| >= 2 : a xs (ys ' 1~) (acc~ (ys ' 0) 2)\n\ta (xs ' 1~) ys (acc~ (xs ' 0))\na (4 5) (1 2 3 4 5 6) (3 3)\n"),
    ('段41: 同じ相手への呼びが複数あり伸びが違う(最大を数える修正)', "a : xs ys acc ?\n\t||xs|| < 2 & ||ys|| < 2 : acc~ 1\n\t||xs|| >= 2 : b (xs ' 1~) ys (acc~ (xs ' 0) 1)\n\tb xs (ys ' 1~) (acc~ (ys ' 0))\nb : xs ys acc ?\n\t||xs|| < 2 & ||ys|| < 2 : acc~ 2\n\t||ys|| >= 2 : a xs (ys ' 1~) (acc~ (ys ' 0) 2)\n\ta (xs ' 1~) ys (acc~ (xs ' 0))\na (4 5 6 7 8) (1 2 3) (3 3)\n"),
    ('段41: 枝で食う器が入れ替わる輪', "a : xs ys acc ?\n\t||xs|| < 2 & ||ys|| < 2 : acc~ 1\n\t||xs|| >= 2 : b (xs ' 1~) ys (acc~ (xs ' 0) 1)\n\tb xs (ys ' 1~) (acc~ (ys ' 0))\nb : xs ys acc ?\n\t||xs|| < 2 & ||ys|| < 2 : acc~ 2\n\t||xs|| >= 2 : a (xs ' 1~) ys (acc~ (xs ' 0))\n\ta xs (ys ' 1~) (acc~ (ys ' 0) 2)\na (4 5) (1 2 3 4 5 6) (3 3)\n"),
]
STR_CASES += [
    ('段42: 要素の値が条件で 0 ≤ e < ||xs|| と分かる取り出し', "a : xs ys ?\n\t||xs|| < 3 : ys~ 1\n\t0 <= (xs ' 0) & (xs ' 0) < ||xs|| : a (xs ' 1~) (ys~ (xs ' (xs ' 0)))\n\ta (xs ' 1~) (ys~ 9)\na (4 5 6 7 8 9 1 2 3 0) (1 2)\n"),
    ('段42: 辺の器が複数ある輪(定数の割り当て・循環あり)', "a : m ys zs ?\n\t||m|| < 3 : ys~ zs~ 1\n\t||m ' 0|| > 2 : b (m ' 1~) ((m ' 0)~ 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9) zs\n\tb (m ' 1~) zs ((m ' 0)~ 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9)\nb : m ys zs ?\n\t||m|| < 3 : ys~ zs~ 2\n\t||m ' 0|| > 2 : a (m ' 1~) ys zs\n\ta (m ' 1~) zs ys\na ((1 2) (3 3) (4 5 6) (7 7) (8 9) (1 1) (2 2) (5 6)) (5 5) (6 6)\n"),
]
STR_CASES += [
    ('段43: 長さを運ぶ Int の仮引数 n(n = ||xs||)から範囲内と分かる取り出し', "a : xs ys n ?\n\tn < 3 : ys~ 1\n\ta (xs ' 1~) (ys~ (xs ' (n - 2))) (n - 1)\na (4 5 6 7 8 9 1 2 3 4) (1 2) 10\n"),
    ('段43: 同上・n = ||xs|| - 1', "a : xs ys n ?\n\tn < 3 : ys~ 1\n\ta (xs ' 1~) (ys~ (xs ' (n - 2))) (n - 1)\na (4 5 6 7 8 9 1 2 3 4) (1 2) 9\n"),
]
STR_CASES += [
    ('段43: 呼びの実引数がどれも i = ||s|| - 1 を満たす(関数の外から呼ぶのはその 1 か所だけ)から範囲内', "f : s i ? (s ' i) (s ' i) \nf `ab` 1\n"),
]
STR_CASES += [
    ('段44: 添字が ||xs|| / 2(下限から範囲内)', "f : xs acc ?\n\t||xs|| < 2 : acc~ (xs ' 0)\n\tf (xs ' 1~) (acc~ (xs ' (||xs|| / 2)))\nf (4 5 6 7 8 9 1 2) (0 0)\n"),
    ('段44: 添字が (||xs|| - 1) / 2', "f : xs ?\n\t||xs|| < 1 : 0\n\t(xs ' ((||xs|| - 1) / 2)) + (f (xs ' 1~))\nf (4 5 6 7 8 9 1 2)\n"),
    ('段44: 添字が (||xs|| + 1) / 2(下限 3)', "f : xs acc ?\n\t||xs|| < 3 : acc\n\tf (xs ' 1~) (acc~ (xs ' ((||xs|| + 1) / 2)))\nf (4 5 6 7 8 9 1 2) (0 0)\n"),
]
REFUSE += [
    ('段44: (||xs|| + 1) / 2 は下限 1 では範囲外になりうるので断る', "f : xs acc ?\n\t||xs|| < 1 : acc\n\tf (xs ' 1~) (acc~ (xs ' ((||xs|| + 1) / 2)))\nf (4 5 6) (0 0)\n", '累積に足す要素'),
]
STR_CASES += [
    ('段45: 添字が (2 * ||xs|| + 1) / 3(係数 ≤ 割る数)', "f : xs acc ?\n\t||xs|| < 3 : acc\n\tf (xs ' 1~) (acc~ (xs ' ((2 * ||xs|| + 1) / 3)))\nf (4 5 6 7 8 9 1 2) (0 0)\n"),
]
REFUSE += [
    ('段45: (3 * ||xs|| + 1) / 2 は L が大きいと範囲外なので断る', "f : xs acc ?\n\t||xs|| < 3 : acc\n\tf (xs ' 1~) (acc~ (xs ' ((3 * ||xs|| + 1) / 2)))\nf (4 5 6 7 8 9 1 2) (0 0)\n", '累積に足す要素'),
]
STR_CASES += [
    ('段46: 添字が i % ||xs||(余りは常に範囲内)', "f : xs i ?\n\ti > 6 : 0\n\t(xs ' (i % ||xs||)) + (f xs (i + 1))\nf (4 5 6) 0\n"),
    ('段46: 同・累積の要素', "f : xs i acc ?\n\ti > 9 : acc\n\tf (xs ' 1~) (i + 1) (acc~ (xs ' (i % ||xs||)))\nf (4 5 6 7 8 9 1 2 3 4 5 6) 0 (0 0)\n"),
]
STR_CASES += [
    ('段47: カウンタ i は全部の呼びで 0 以上(+1 で進む)から範囲内', "f : xs ys i acc ?\n\t||ys|| < 2 | i >= ||xs|| : acc\n\tf xs (ys ' 1~) (i + 1) (acc~ (xs ' i))\nf (4 5 6) (1 2 3 4 5 6) 0 (0 0)\n"),
    ('段47: 輪を通る 0 以上(i + 1 と j * 2)', "f : xs ys i acc ?\n\t||ys|| < 2 | i >= ||xs|| : acc\n\tg xs (ys ' 1~) (i + 1) (acc~ (xs ' i))\ng : xs ys j acc ?\n\t||ys|| < 2 : acc\n\tf xs (ys ' 1~) (j * 2) (acc~ (xs ' 0))\nf (4 5 6 7 8 9) (1 2 3 4 5 6 7) 0 (0 0)\n"),
    ('段47: 要素の % ||xs|| の添字', "f : xs ys acc ?\n\t||ys|| < 2 : acc\n\tf xs (ys ' 1~) (acc~ (xs ' ((ys ' 0) % ||xs||)))\nf (4 5 6) (7 -8 2 9 1) (0 0)\n"),
    ('段47: 要素 + 要素 の % ||xs||', "f : xs ys acc ?\n\t||ys|| < 2 : acc\n\tf xs (ys ' 1~) (acc~ (xs ' (((ys ' 0) + (ys ' 1)) % ||xs||)))\nf (4 5 6) (7 -8 2 9 1) (0 0)\n"),
]
REFUSE += [
    ('段47: i - 1 は負になりうるので範囲内と言えず断る', "f : xs ys i acc ?\n\t||ys|| < 2 | i >= ||xs|| : acc\n\tf xs (ys ' 1~) (i - 1) (acc~ (xs ' i))\nf (4 5 6) (1 2 3 4 5 6) 0 (0 0)\n", '累積に足す要素'),
]
STR_CASES += [
    ('段48: 条件 i < 1 の偽から i ≥ 1 と分かり、i - 1 は 0 以上(呼びも添字も)', "f : xs ys i acc ?\n\t||ys|| < 2 | i < 1 | i - 1 >= ||xs|| : acc\n\tf xs (ys ' 1~) (i - 1) (acc~ (xs ' (i - 1)))\nf (4 5 6) (1 2 3 4 5) 3 (0 0)\n"),
]
REFUSE += [
    ('段48: i < 0 の偽だけでは i - 1 が負になりうるので断る', "f : xs ys i acc ?\n\t||ys|| < 2 | i < 0 | i - 1 >= ||xs|| : acc\n\tf xs (ys ' 1~) (i - 1) (acc~ (xs ' (i - 1)))\nf (4 5 6) (1 2 3 4 5) 3 (0 0)\n", '累積に足す要素'),
]
STR_CASES += [
    ('段49: 累積を渡すだけの辺がある輪', "f : xs ys i acc ?\n\t||ys|| < 2 | i >= ||xs|| : acc\n\tg xs (ys ' 1~) (i + 1) (acc~ (xs ' i))\ng : xs ys j acc ?\n\tf xs (ys ' 1~) (j * 2) acc\nf (4 5 6 7 8 9) (1 2 3 4 5 6 7) 0 (0 0)\n"),
    ('段49: 渡すだけの辺がある輪(累積を伸ばす辺は別の位置)', "f : xs ys i acc ?\n\t||ys|| < 2 | i >= ||xs|| : acc\n\tg xs (ys ' 1~) (i + 1) (acc~ (xs ' i))\ng : xs ys j acc ?\n\t||ys|| < 2 : acc\n\tf xs (ys ' 1~) (j * 2) (acc~ (xs ' 0))\nf (4 5 6 7 8 9) (1 2 3 4 5 6 7) 0 (0 0)\n"),
    ('段49: カウンタだけで回る(終了条件 i >= ||xs||)', "f : xs i acc ?\n\ti >= ||xs|| : acc\n\tf xs (i + 1) (acc~ (xs ' i))\nf (4 5 6) 0 (0 0)\n"),
    ('段49: 歩幅 2 のカウンタ', "f : xs i acc ?\n\ti >= ||xs|| : acc\n\tf xs (i + 2) (acc~ (xs ' i))\nf (4 5 6 7 8) 1 (0 0)\n"),
    ('段49: 条件 i + 1 < 4 の偽から i ≥ 3 と分かる', "f : xs ys i acc ?\n\t||ys|| < 2 | i + 1 < 4 | i - 3 >= ||xs|| : acc\n\tf xs (ys ' 1~) (i - 1) (acc~ (xs ' (i - 3)))\nf (4 5 6 7 8) (1 2 3 4 5) 7 (0 0)\n"),
]
REFUSE += [
    ('段49: 負から始まるカウンタは回る回数が測れず断る', "f : xs i acc ?\n\ti >= ||xs|| : acc\n\tf xs (i + 1) (acc~ (xs ' i))\nf (4 5 6) -1 (0 0)\n", '累積に足す要素'),
]
STR_CASES += [
    ('段50: i ≥ j と分かれば i - j は 0 以上(Int どうしの比較)', "f : xs ys i j acc ?\n\t||ys|| < 2 | i < j | i - j >= ||xs|| : acc\n\tf xs (ys ' 1~) (i - 1) j (acc~ (xs ' (i - j)))\nf (4 5 6 7 8) (1 2 3 4 5) 6 3 (0 0)\n"),
    ('段50: j も一緒に動く', "f : xs ys i j acc ?\n\t||ys|| < 2 | i < j | i - j >= ||xs|| : acc\n\tf xs (ys ' 1~) (i - 1) (j - 1) (acc~ (xs ' (i - j)))\nf (4 5 6 7 8) (1 2 3 4 5) 6 3 (0 0)\n"),
    ('段50: 文字列の累積を渡すだけの辺', "a : s t acc ?\n\t||t|| < 2 : acc\n\tb s (t ' 1~) (acc `x`)\nb : s t acc ?\n\t||t|| < 2 : acc `!`\n\ta s (t ' 1~) acc\na `ab` `zzzzzz` `qq`\n"),
    ('段50: 文字列の累積・伸びる辺が別の位置', "a : s t acc ?\n\t||t|| < 2 : acc\n\tb s (t ' 1~) acc\nb : s t acc ?\n\t||t|| < 2 : acc `!`\n\ta s (t ' 2~) (acc `xy` `z`)\na `ab` `zzzzzzz` `qq`\n"),
]
REFUSE += [
    ('段50: i ≥ j - 9 では i - j が範囲外になりうるので断る', "f : xs ys i j acc ?\n\t||ys|| < 2 | i < j - 9 | i - j >= ||xs|| : acc\n\tf xs (ys ' 1~) (i - 1) j (acc~ (xs ' (i - j)))\nf (4 5 6 7 8) (1 2 3 4 5) 0 3 (0 0)\n", '累積に足す要素'),
    ('段50: 下限が負(i ≥ -3)でも 0 以上とは言わない(merge の不具合の回帰)', "f : xs ys i acc ?\n\t||ys|| < 2 | i < -3 | i >= ||xs|| : acc\n\tf xs (ys ' 1~) (i - 1) (acc~ (xs ' i))\nf (4 5 6 7 8) (1 2 3 4 5) 1 (0 0)\n", '累積に足す要素'),
    ('段50: i ≥ j - 1 では i - j が -1 になりうるので断る', "f : xs ys i j acc ?\n\t||ys|| < 2 | i < j - 1 | i - j >= ||xs|| : acc\n\tf xs (ys ' 1~) (i - 1) j (acc~ (xs ' (i - j)))\nf (4 5 6 7 8) (1 2 3 4 5) 6 3 (0 0)\n", '累積に足す要素'),
]
STR_CASES += [
    ('段51: 0 ≤ i ≤ 2 と ||xs|| ≥ 3 から範囲内(区間)', "f : xs ys i acc ?\n\t||ys|| < 2 | ||xs|| < 3 | i < 0 | i > 2 : acc\n\tf xs (ys ' 1~) (i + 1) (acc~ (xs ' i))\nf (4 5 6 7) (1 2 3 4 5) 0 (0 0)\n"),
    ('段51: 上限の計算(% と / と *)', "f : xs ys i acc ?\n\t||ys|| < 2 | ||xs|| < 3 : acc\n\tf xs (ys ' 1~) (i + 1) (acc~ (xs ' ((i * i) % 3 + (i / 2) % 1)))\nf (4 5 6 7) (1 2 3 4 5) 0 (0 0)\n"),
]
REFUSE += [
    ('段51: 上限 3 は長さの下限 3 に収まらないので断る', "f : xs ys i acc ?\n\t||ys|| < 2 | ||xs|| < 3 | i < 0 | i > 3 : acc\n\tf xs (ys ' 1~) (i + 1) (acc~ (xs ' i))\nf (4 5 6 7) (1 2 3 4 5) 0 (0 0)\n", '累積に足す要素'),
]
STR_CASES += [
    ('段52: 末尾から数える添字 i - ||xs||(0 ≤ i < ||xs||)', "f : xs ys i acc ?\n\t||ys|| < 2 | i >= ||xs|| : acc\n\tf xs (ys ' 1~) (i + 1) (acc~ (xs ' (i - ||xs||)))\nf (4 5 6 7) (1 2 3 4 5 6 7) 0 (0 0)\n"),
]
REFUSE += [
    ('段52: i = ||xs|| も含む条件は保守的に断る', "f : xs ys i acc ?\n\t||ys|| < 2 | i > ||xs|| : acc\n\tf xs (ys ' 1~) (i + 1) (acc~ (xs ' (i - ||xs||)))\nf (4 5 6 7) (1 2 3 4 5 6 7) 0 (0 0)\n", '累積に足す要素'),
    ('段52: i - 1 - ||xs|| は i = 0 で範囲外になるので断る', "f : xs ys i acc ?\n\t||ys|| < 2 | i >= ||xs|| : acc\n\tf xs (ys ' 1~) (i + 1) (acc~ (xs ' (i - 1 - ||xs||)))\nf (4 5 6 7) (1 2 3 4 5 6 7) 0 (0 0)\n", '累積に足す要素'),
]
STR_CASES += [
    ('段53: 文字列の添字(範囲内)', "f : s ys i acc ?\n\t||ys|| < 2 | i >= ||s|| : acc\n\tf s (ys ' 1~) (i + 1) (acc (s ' i))\nf `abcd` (1 2 3 4 5 6 7) 0 `x`\n"),
    ('段53: 文字列の添字(範囲外の文字は並びから消える)', "f : s ys i acc ?\n\t||ys|| < 2 | i >= ||s|| : acc\n\tf s (ys ' 1~) (i + 1) (acc (s ' (i + 1)))\nf `abcd` (1 2 3 4 5 6 7) 0 `x`\n"),
]
STR_CASES += [
    ('段54: 輪で累積ごとに伸ばす辺と渡すだけの辺が混ざる', "f0 : s ys acc acc2 ?\n\t||ys|| < 3 : acc~ 9\n\tf1 s (ys ' 1~) acc (acc2~ 9 (s ' 0))\nf1 : s ys acc acc2 ?\n\t||ys|| < 1 : acc~ (acc2 ' 0)\n\tf0 s (ys ' 2~) (acc~ 8) (acc2~ 9 4 (s ' 0))\nf0 (3 2) (8 5 8 7 5) (7 9 6) (9 8 1)\n"),
    ('段54: 文字列の累積を、伸ばす辺 1 つと渡すだけの辺 2 つの輪で', "f0 : s ys acc ?\n\t||ys|| < 1 : acc `!`\n\tf1 s (ys ' 2~) acc\nf1 : s ys acc ?\n\t||ys|| < 1 : acc\n\tf2 s (ys ' 2~) (acc `x` `xx`)\nf2 : s ys acc ?\n\t||ys|| < 1 : acc\n\tf0 s (ys ' 1~) acc\nf0 `ab` `zzzz` `q`\n"),
    ("段54: 入れ子の要素の先頭 (m ' i) ' 0", "f : m ys i acc ?\n\t||ys|| < 2 | i >= ||m|| : acc\n\tf m (ys ' 1~) (i + 1) (acc~ ((m ' i) ' 0))\nf ((1 2) (3 4) (5 6)) (1 2 3 4 5 6 7) 0 (0 0)\n"),
]
STR_CASES += [
    ("段55: 内側の長さの下限 ||m ' i|| ≥ 2 から (m ' i) ' 1 が範囲内", "f : m ys i acc ?\n\t||ys|| < 2 | i >= ||m|| | ||m ' i|| < 2 : acc\n\tf m (ys ' 1~) (i + 1) (acc~ ((m ' i) ' 1))\nf ((1 2) (3 4) (5 6)) (1 2 3 4 5 6 7) 0 (0 0)\n"),
]
REFUSE += [
    ("段55: 内側の長さの下限が足りない (m ' i) ' 1 は断る", "f : m ys i acc ?\n\t||ys|| < 2 | i >= ||m|| : acc\n\tf m (ys ' 1~) (i + 1) (acc~ ((m ' i) ' 1))\nf ((1 2) (3 4) (5 6)) (1 2 3 4 5 6 7) 0 (0 0)\n", '累積に足す要素'),
    ("段55: 下限 2 では (m ' i) ' 2 は範囲外になりうるので断る", "f : m ys i acc ?\n\t||ys|| < 2 | i >= ||m|| | ||m ' i|| < 2 : acc\n\tf m (ys ' 1~) (i + 1) (acc~ ((m ' i) ' 2))\nf ((1 2) (3 4) (5 6)) (1 2 3 4 5 6 7) 0 (0 0)\n", '累積に足す要素'),
]
STR_CASES += [
    ('段56: 輪を通るカウンタ(片方の辺は ys を食い、もう片方は i を進める)', "f0 : s ys i acc ?\n\t||ys|| < 2 | i >= ||s|| : acc\n\tf1 s ys (i + 1) (acc~ (s ' i))\nf1 : s ys i acc ?\n\t||ys|| < 2 | i >= ||s|| : acc~ 9\n\tf0 s (ys ' 1~) i (acc~ (ys ' 0))\nf0 (4 5 6 7) (1 2 3 4 5 6 7) 0 (0 0)\n"),
    ('段56: 輪を通るカウンタ(どの辺も i を進めるだけ)', "f0 : s i acc ?\n\ti >= ||s|| : acc\n\tf1 s (i + 1) (acc~ (s ' i))\nf1 : s i acc ?\n\ti >= ||s|| : acc~ 9\n\tf0 s (i + 2) (acc~ (s ' i) 8)\nf0 (4 5 6 7 3 2) 0 (0 0)\n"),
]
REFUSE += [
    ('段56: カウンタを 0 に戻す辺があると回る回数が ||x|| で押さえられず断る', "f0 : s i acc ?\n\ti >= ||s|| : acc\n\tf1 s (i + 1) (acc~ (s ' i))\nf1 : s i acc ?\n\ti >= ||s|| : acc~ 9\n\tf0 s 0 (acc~ (s ' i) 8)\nf0 (4 5 6 7 3 2) 0 (0 0)\n", '収束しません'),
]
STR_CASES += [
    ('段57: 証明器だけが受理する添字(乱数から 0)', "f : xs ys i j acc ?\n\t||ys|| < 2 | (i - j) > -3 | (i + -2) <= j : acc\n\tf xs (ys ' 1~) (i * 2) (j - 1) (acc~ (xs ' (i - 0)))\nf (9 2 1 3 1) (1 2 3 4 5 6 7 8) 5 2 (0 0)\n"),
    ('段57: 証明器だけが受理する添字(乱数から 1)', "f : xs ys i j acc ?\n\t||ys|| < 2 | (i % 5) > ||xs|| - 1 | (i % 5) < 0 : acc\n\tf xs (ys ' 1~) (i - 1) (j + 1) (acc~ (xs ' ((i % 5) - ||xs||)))\nf (2 9 1 4) (1 2 3 4 5 6 7 8) 2 -1 (0 0)\n"),
    ('段57: 証明器だけが受理する添字(乱数から 2)', "f : xs ys i j acc ?\n\t||ys|| < 2 | j < 0 | j > ||xs|| : acc\n\tf xs (ys ' 1~) (i + 2) (j + 1) (acc~ (xs ' (j - ||xs||)))\nf (5 1 9 3 7 6) (1 2 3 4 5 6 7 8) 2 4 (0 0)\n"),
    ('段57: 証明器だけが受理する添字(乱数から 3)', "f : xs ys i j acc ?\n\t||ys|| < 2 | i < 0 | i >= ||xs|| + 1 : acc\n\tf xs (ys ' 1~) (i + 1) (j + 1) (acc~ (xs ' (i - ||xs||)))\nf (6 4 7 3 5 9) (1 2 3 4 5 6 7 8) 0 -2 (0 0)\n"),
    ('段57: 証明器だけが受理する添字(乱数から 4)', "f : xs ys i j acc ?\n\t||ys|| < 2 | i < j + -2 | (i - j + 1) >= ||xs|| : acc\n\tf xs (ys ' 1~) (i + 1) (j + 1) (acc~ (xs ' (i - j + 1)))\nf (3 7) (1 2 3 4 5 6 7 8) -1 4 (0 0)\n"),
]
for name, src in STR_CASES:
    try: text = asm_of(src, "linux")
    except sign_asm.AsmError as e:
        check("出せるはず: " + name, "断り: %s" % e, "出力"); continue
    r = run_asm(text, linux=True)
    check("文字列: " + name, (r[0], r[1]), ("exit", interp_out(src)))

# arena が足りない呼び方をされたら、何も書かずに `__`(len = 0)を返す(stack_abi.md §4.7。呼ぶ側が正しく取れば起きないが、守りとして)
def call_builder(src, fn, regs, room_words, k):
    cpu = Cpu(asm_of(src))
    base = 0x300000
    for r, v in regs.items(): cpu.r[r] = v
    cpu.r["x8"], cpu.r["x15"] = base, k
    hdr = base + 16 * k
    cpu.store(hdr, hdr + 16); cpu.store(hdr + 8, hdr + 16 + 8 * room_words)
    cpu.run(fn)
    written = any(cpu.mem.get(base + i, 0) for i in range(0, 16 * k))
    return (cpu.r["x0"], cpu.r["x1"], written)
_src = "f : a b ? (a b) (b a)\nf 1 2\n"
check("arena: 十分あれば組む(x1 = 記述子の数)", call_builder(_src, "f", {"x0": 1, "x1": 2}, 4, 2)[1:], (2, True))
check("arena: 内容の領域が足りなければ何も書かず __", call_builder(_src, "f", {"x0": 1, "x1": 2}, 3, 2), (0, 0, False))
check("arena: 記述子の置き場が足りなければ何も書かず __", call_builder(_src, "f", {"x0": 1, "x1": 2}, 4, 1), (0, 0, False))

check("規則 刻み 0 は罠(処理系は『進みません』のエラー)", run_asm(asm_of("f : a s b ? [a ~+ s ~ b]\nf 1 0 9\n", "linux"), linux=True), ("trap", None))
check("規則 個数の計算の溢れは罠", run_asm(asm_of("f : a b ? ||[a ~ b]||\nf (0 - 9223372036854775807) 9223372036854775807\n", "linux"), linux=True), ("trap", None))
check("組み立ての要素の溢れは罠", run_asm(asm_of("f : a ? a * 4611686018427387904 a\nf 3\n", "linux"), linux=True), ("trap", None))

# ---- 単体の実行ファイルの足場(Linux): 結果を印字して exit ----
for name, src, want in [("印字", "sq : n ? n * n\nsq 12\n", "144\n"), ("負の数", "-9223372036854775807\n", "-9223372036854775807\n"),
                        ("0", "5 - 5\n", "0\n"), ("大きな数", "9223372036854775807\n", "9223372036854775807\n")]:
    check("linux 足場: " + name, run_asm(asm_of(src, "linux"), linux=True), ("exit", want, 0))
check("linux 足場: __ を印字", run_asm(asm_of("5 / 0\n", "linux"), linux=True), ("exit", "__\n", 0))
check("linux 足場: __ になりうる式の値の印字", run_asm(asm_of("f : n ?\n\tn < 2 : n\nf 1\n", "linux"), linux=True), ("exit", "1\n", 0))
check("linux 足場: __ になりうる式の __", run_asm(asm_of("f : n ?\n\tn < 2 : n\nf 7\n", "linux"), linux=True), ("exit", "__\n", 0))
check("linux 足場: 溢れは印字せず止まる", run_asm(asm_of("9223372036854775807 + 1\n", "linux"), linux=True), ("trap", None))

# ---- アセンブラで組める(clang があれば) ----
cc = subprocess.run(["which", "clang"], capture_output=True, text=True).stdout.strip()
if cc:
    d = tempfile.mkdtemp()
    for name, src in CASES + STR_CASES:
        try: text = asm_of(src, "linux")
        except sign_asm.AsmError: continue                  # 出せない形は上で数えた
        s = os.path.join(d, "a.s"); open(s, "w", encoding="utf-8").write(text)
        r = subprocess.run([cc, "--target=aarch64-linux-gnu", "-c", s, "-o", os.path.join(d, "a.o")], capture_output=True, text=True)
        check("組める: " + name, (r.returncode, r.stderr.strip()[:200]), (0, ""))
else:
    print("(clang が無いので、アセンブラでの確認は飛ばした)")

# ---- 入口 ----
cc = cc if "cc" in globals() else ""

# ---- 入口 `sign.py --asm` ----
def cli(args, src=None):
    d = tempfile.mkdtemp(); p = os.path.join(d, "t.sn")
    if src is not None: open(p, "w", encoding="utf-8").write(src)
    r = subprocess.run([sys.executable, os.path.join(HERE, "sign.py"), "--asm", *([p] if src is not None else []), *[a.replace("@D", d) for a in args]],
                       capture_output=True, text=True, timeout=60)
    return r, d
r, d = cli([], "sq : n ? n * n\nsq 12\n")
check("--asm: 標準出力に _.main を書く", (r.returncode, "_.main:" in r.stdout, "Traceback" in r.stderr), (0, True, False))
r, d = cli(["-o", "@D/o.s"], "1 + 2\n")
check("--asm -o: ファイルへ書く", (r.returncode, os.path.isfile(os.path.join(d, "o.s")) and "adds" in open(os.path.join(d, "o.s")).read()), (0, True))
r, d = cli(["--target=linux"], "7\n")
check("--asm --target=linux: _start と印字が付く", (r.returncode, "_start:" in r.stdout, "_sign_print_int:" in r.stdout), (0, True, True))
r, d = cli(["--target=bare"], "7\n")
check("--asm --target=bare: _start は付かない", (r.returncode, "_start:" in r.stdout), (0, False))
if cc:
    r, d = cli(["--elf=@D/a.out"], "sq : n ? n * n\nsq 12\n")
    ok = os.path.isfile(os.path.join(d, "a.out")) and open(os.path.join(d, "a.out"), "rb").read(20)[:4] == b"\x7fELF"
    check("--asm --elf: AArch64 の ELF ができる", (r.returncode, ok), (0, True))
    r, d = cli(["--elf=@D/n.out"], "f : xs a ? (a xs~) (xs~ a)\nf (1 2 3) 9\n")
    ok = os.path.isfile(os.path.join(d, "n.out")) and open(os.path.join(d, "n.out"), "rb").read(20)[:4] == b"\x7fELF"
    check("--asm --elf: 入れ子の器の ELF ができる", (r.returncode, ok), (0, True))
for name, args, src in [("出せない形", [], "f : a b ? a + b\nf 1\n"), ("構文の誤り", [], "( ( )\n"), ("ファイルが無い", ["/nonexistent.sn"], None),
                        ("指定が無い", [], None), ("知らない --target", ["--target=x86"], "1\n"), ("知らないオプション", ["--zzz"], "1\n")]:
    r, d = cli(args, src)
    check("--asm: " + name + " は理由を言って終わる(rc 1・追跡なし)", (r.returncode, "Traceback" in r.stderr, bool(r.stderr.strip())), (1, False, True))

# ---- スタック使用量の実測: 伸びる累積と食う再帰の同居で、再帰の深さに比例する(二次に積み上がらない) ----
def stack_used(src):
    cpu = Cpu(asm_of(src, "linux")); lo = [cpu.r["sp"]]; top = cpu.r["sp"]; orig = cpu.setreg
    def sr(name, v):
        orig(name, v)
        if name == "sp" and cpu.r["sp"] < lo[0]: lo[0] = cpu.r["sp"]
    cpu.setreg = sr; cpu.run("_start")
    return top - lo[0], cpu.out.decode().strip()
def grow_src(n):
    return ("f : xs acc ?\n\t||xs|| = 1 : acc~ (xs ' 0)\n\t(xs ' 0) (f (xs ' 1~) (acc~ 0))~\nl : %s\ng : ys ? ||f ys (3 3)||\ng l\n"
            % " ".join(str(i % 9) for i in range(n)))
(s1, o1), (s2, o2) = stack_used(grow_src(60)), stack_used(grow_src(120))
check("スタック実測: 累積と食う再帰の同居は深さに比例(倍にして 2.3 倍未満)", (o1, o2, s2 < s1 * 2.3), ("121", "241", True))

# ---- 輪の上界は辺ごとの式(傾き α = 輪の平均、定数 β は関数ごと)。値そのものを検査する ----
def bounds_of(src):
    P = sign_asm.Program(sign_interp.parse_source(src)); P.generate("linux"); return P.bound
check("輪の上界: 食う数・足す数が辺で違う輪は (傾き 3, 定数は関数ごと)", {k: bounds_of("a : xs ?\n\t||xs|| < 3 : (xs ' 0) 100\n\t(xs ' 0) 1 (b (xs ' 2~))~\nb : xs ?\n\t||xs|| < 2 : (xs ' 0) 200\n\t(xs ' 0) (xs ' 0) 4 4 4 4 4 (a (xs ' 1~))~\na (1 2 3 4 5 6 7 8 9 10 11 12 13)\n")[k] for k in ("a", "b")}, {"a": (2, {0: 3}), "b": (6, {0: 3})})
from fractions import Fraction
check("輪の上界: 二つの関数が交互に 1 と 2 を足す輪は 傾き 3/2(分数)", {k: bounds_of("ev : xs ?\n\t||xs|| = 1 : (xs ' 0) 100\n\t(xs ' 0) (od (xs ' 1~))~\nod : xs ?\n\t||xs|| = 1 : (xs ' 0) 200\n\t(xs ' 0) 0 (ev (xs ' 1~))~\nev (1 2 3 4 5)\n")[k] for k in ("ev", "od")}, {"ev": (2, {0: Fraction(3, 2)}), "od": (Fraction(5, 2), {0: Fraction(3, 2)})})
check("輪の上界: 入れ子の内側の総和の係数は、窓と残りが重ならないので足さず最大(1)", {k: bounds_of("a : m ?\n\t||m|| = 1 : m~ 100\n\t(m ' 0)~ 0 (b (m ' 1~))~\nb : m ?\n\t||m|| = 1 : m~ 200\n\t(m ' 0)~ 1 (a (m ' 1~))~\na ((1 2) (3 4) (5 6 7) (8 8))\n")[k] for k in ("a", "b")}, {"a": (1, {0: 1, ("m", 0): 1}), "b": (1, {0: 1, ("m", 0): 1})})
# 分数の傾きで取った置き場に、実際の出力が収まる(n = 2..39 を処理系と比べる)
import math
def real_len(defs, call, n):
    xs = " ".join(str(i % 7 + 1) for i in range(n))
    d = tempfile.mkdtemp(); pth = os.path.join(d, "t.sn"); open(pth, "w", encoding="utf-8").write(defs + call + " (" + xs + ")\n")
    r = subprocess.run([sys.executable, os.path.join(HERE, "sign.py"), pth], capture_output=True, text=True, timeout=60)
    return len(eval(r.stdout.strip()))
_m1 = "ev : xs ?\n\t||xs|| = 1 : (xs ' 0) 100\n\t(xs ' 0) (od (xs ' 1~))~\nod : xs ?\n\t||xs|| = 1 : (xs ' 0) 200\n\t(xs ' 0) 0 (ev (xs ' 1~))~\nev (1 2 3 4 5)\n"
_b = bounds_of(_m1)["ev"]
check("分数の傾きの上界が実際の出力長以上(m1, n = 2..39)", all(real_len(_m1.rsplit("\n", 2)[0] + "\n", "ev", n) <= math.ceil(_b[0]) + math.ceil(_b[1][0] * n) for n in range(2, 40)), True)

check("輪の上界: 輪から別の輪を底で呼ぶと傾きは大きい方(3)になる", {k: bounds_of("p : xs ?\n\t||xs|| < 3 : (xs ' 0) (c xs)~\n\t(xs ' 0) (q (xs ' 1~))~\nq : xs ?\n\t||xs|| < 3 : (xs ' 0) 9 (c xs)~\n\t(xs ' 0) 1 1 (p (xs ' 1~))~\nc : xs ?\n\t||xs|| = 1 : (xs ' 0) 300\n\t(xs ' 0) 0 (d (xs ' 1~))~\nd : xs ?\n\t||xs|| = 1 : (xs ' 0) 400\n\t(xs ' 0) 0 0 0 (c (xs ' 1~))~\np (1 2 3 4 5 6 7 8)\n")[k] for k in ("p", "q", "c", "d")}, {"p": (3, {0: 3}), "q": (4, {0: 3}), "c": (2, {0: 3}), "d": (3, {0: 3})})

# ---- 文字は 1 度だけ評価する(数える段と書く段で式を 2 度生成しない) ----
_asm = asm_of("f : s ? (s ' 0) (s ' 5) (s ' -1)\nf `abc`\n")
check("文字の並置: 文字の式は 1 度だけ生成される(2 つの文字 = 評価 2 つ)", _asm.count("// 文字(1 度だけ評価)"), 3)

# ---- 段 25: 文字列の連結の Int 項は 1 項につき 1 度だけ呼ぶ(数える段と書く段で呼び直さない) ----
_asm = asm_of("g : n ? n * n\nf : n ? `<` (g n) `>` (g n) (g n)\nf 3\n")
check("文字列の連結: Int 項の呼びは項の数だけ(3 項 = bl g が 3 回)", _asm.count("bl g\n"), 3)

# ---- 段 30: 輪を渡る呼びの新しい器が別の器に頼るとき、上界に収まる(長さを変えて処理系と比べる)----
_ok30 = True
for _n in range(2, 40, 3):
    for _m in (2, 3, 5):
        _src = "a : xs ys ?\n\t||ys|| < 4 : xs~ ys~\n\tb (ys ' 3~) ((xs ' 0) xs~ 9)\nb : xs ys ?\n\t||xs|| < 4 : xs~ ys~ 5\n\ta (xs ' 3~) ((ys ' 1) 6)\na (%s) (%s)\n" % (" ".join(str(i % 7) for i in range(_m)), " ".join(str(i % 9) for i in range(_n)))
        _d = tempfile.mkdtemp(); _p = os.path.join(_d, "t.sn"); open(_p, "w", encoding="utf-8").write(_src)
        _want = subprocess.run([sys.executable, os.path.join(HERE, "sign.py"), _p], capture_output=True, text=True, timeout=60).stdout
        _got = run_asm(sign_asm.generate(sign_interp.parse_source(_src), "linux"), linux=True)[1]
        if _got != _want: _ok30 = False
check("段30: 輪の新しい器が別の器の長さに頼る(n = 2..38, m = 2/3/5 を処理系と比べる)", _ok30, True)

# ---- 段 32: 輪の新しい器が入れ子の内側の長さに頼るとき、上界に収まる(内側の長さ・入れ子の個数を変えて処理系と比べる)----
import random as _rnd
_rnd.seed(7)
_ok32 = True
for _sh in range(3):
    _body = ["a : m ys ?\n\t||m|| < 3 : ys~ 1\n\tb (m ' 2~) ((m ' 0)~ 9)\nb : m ys ?\n\t||m|| < 3 : ys~ 2\n\ta (m ' 2~) ((m ' 1)~ 8)\n",
             "a : m ys ?\n\t||m|| < 3 : ys~ (m ' 0)~\n\tb (m ' 2~) (m ' 1)\nb : m ys ?\n\t||m|| < 3 : ys~ 2\n\ta (m ' 2~) ((m ' 0)~ (m ' 1)~)\n",
             "a : m ys ?\n\t||m|| < 3 : ys~ 1\n\t(m ' 0)~ (b (m ' 2~) ((m ' 1)~ 9))~\nb : m ys ?\n\t||m|| < 3 : ys~ 2\n\t(m ' 1)~ (a (m ' 2~) ((m ' 0)~ 8))~\n"][_sh]
    for _t in range(6):
        _inner = " ".join("(%s)" % " ".join(str(_rnd.randint(0, 9)) for _ in range(_rnd.randint(2, 15))) for _ in range(_rnd.randint(3, 12)))
        _ys = " ".join(str(_rnd.randint(0, 9)) for _ in range(_rnd.randint(2, 4)))
        _src = _body + "a (%s) (%s)\n" % (_inner, _ys)
        _d = tempfile.mkdtemp(); _p = os.path.join(_d, "t.sn"); open(_p, "w", encoding="utf-8").write(_src)
        _want = subprocess.run([sys.executable, os.path.join(HERE, "sign.py"), _p], capture_output=True, text=True, timeout=60).stdout
        if run_asm(sign_asm.generate(sign_interp.parse_source(_src), "linux"), linux=True)[1] != _want: _ok32 = False
check("段32: 輪の新しい器が入れ子の内側の長さに頼る(3 形 × 6 通りを処理系と比べる)", _ok32, True)

# ---- 段 33: 内側頼みの位置を渡し合う輪・器の長さと内側の総和の両方に頼る新しい器(ランダムに処理系と比べる)----
_rnd.seed(13)
_ok33 = True
_shapes33 = [("a : m xs ys ?\n\t||m|| < 4 : ys~ xs~ 1\n\tb (m ' 3~) ((m ' 0)~ xs~ 9)\nb : m ys ?\n\t||m|| < 4 : ys~ 2\n\ta (m ' 3~) (4 4) ((m ' 1)~ 8)\n", True),
             ("a : m ys ?\n\t||m|| < 3 : ys~ 1\n\tb (m ' 2~) ((m ' 0)~ 9)\nb : m ys ?\n\t||m|| < 3 : ys~ 2\n\ta (m ' 2~) (ys ' 1~)\n", False),
             ("a : m ys ?\n\t||m|| < 3 : ys~ 1\n\t(m ' 0)~ (b (m ' 2~) ((m ' 1)~ 9))~\nb : m ys ?\n\t||m|| < 3 : ys~ 2\n\t(m ' 1)~ (a (m ' 2~) ys)~\n", False)]
for _body, _x in _shapes33:
    for _t in range(6):
        _inner = " ".join("(%s)" % " ".join(str(_rnd.randint(0, 9)) for _ in range(_rnd.randint(2, 15))) for _ in range(_rnd.randint(8, 14)))
        _ys = " ".join(str(_rnd.randint(0, 9)) for _ in range(_rnd.randint(2, 9)))
        _xs = " ".join(str(_rnd.randint(0, 9)) for _ in range(_rnd.randint(2, 9)))
        _src = _body + ("a (%s) (%s) (%s)\n" % (_inner, _xs, _ys) if _x else "a (%s) (%s)\n" % (_inner, _ys))
        _d = tempfile.mkdtemp(); _p = os.path.join(_d, "t.sn"); open(_p, "w", encoding="utf-8").write(_src)
        _want = subprocess.run([sys.executable, os.path.join(HERE, "sign.py"), _p], capture_output=True, text=True, timeout=60).stdout
        if run_asm(sign_asm.generate(sign_interp.parse_source(_src), "linux"), linux=True)[1] != _want: _ok33 = False
check("段33: 内側頼みの位置を渡し合う輪・両方に頼る新しい器(3 形 × 6 通りを処理系と比べる)", _ok33, True)


# ---- 段 34: 入れ子を返す関数の累積(ランダムに処理系と比べる)----
_rnd.seed(34)
_ok34 = True
for _t in range(10):
    _xs = " ".join(str(_rnd.randint(0, 9)) for _ in range(_rnd.randint(2, 12)))
    _ys = " ".join(str(_rnd.randint(0, 9)) for _ in range(_rnd.randint(2, 14)))
    _src = "f : xs ys ?\n\t||xs|| = 1 : (ys~ (xs ' 0)) (xs ' 0 7)\n\tf (xs ' 1~) (ys~ (xs ' 0))\nf (%s) (%s)\n" % (_xs, _ys)
    _d = tempfile.mkdtemp(); _p = os.path.join(_d, "t.sn"); open(_p, "w", encoding="utf-8").write(_src)
    _want = subprocess.run([sys.executable, os.path.join(HERE, "sign.py"), _p], capture_output=True, text=True, timeout=60).stdout
    if run_asm(sign_asm.generate(sign_interp.parse_source(_src), "linux"), linux=True)[1] != _want: _ok34 = False
check("段34: 入れ子を返す関数の累積(10 通りを処理系と比べる)", _ok34, True)


_rnd.seed(35)
_ok35 = True
for _t in range(10):
    _xs = " ".join(str(_rnd.randint(0, 9)) for _ in range(_rnd.randint(1, 25)))
    _ys = " ".join(str(_rnd.randint(0, 9)) for _ in range(_rnd.randint(2, 16)))
    _src = "a : xs ys ?\n\t||xs|| < 3 : (ys~ (xs ' 0)) (xs ' 0 7)\n\tb (xs ' 2~) (ys~ (xs ' 0))\nb : xs ys ?\n\t||xs|| < 3 : (ys~ (xs ' 0)) (xs ' 0 8)\n\ta (xs ' 2~) (ys~ (xs ' 0))\na (%s) (%s)\n" % (_xs, _ys)
    _d = tempfile.mkdtemp(); _p = os.path.join(_d, "t.sn"); open(_p, "w", encoding="utf-8").write(_src)
    _want = subprocess.run([sys.executable, os.path.join(HERE, "sign.py"), _p], capture_output=True, text=True, timeout=60).stdout
    if run_asm(sign_asm.generate(sign_interp.parse_source(_src), "linux"), linux=True)[1] != _want: _ok35 = False
check("段35: 入れ子を返す輪で累積を渡す(10 通りを処理系と比べる)", _ok35, True)


_rnd.seed(36)
_ok36 = True
_sh36 = [open_ for open_ in ("f : xs ys zs ?\n\t||xs|| = 1 : (ys~ (xs ' 0)) (zs~ (xs ' 0) 5)\n\tf (xs ' 1~) (ys~ (xs ' 0)) (zs~ (xs ' 0) 1)\nf (4 5 6 7 8) (1 2) (9 9)\n", "a : xs ys zs ?\n\t||xs|| < 3 : (ys~ (xs ' 0)) (zs~ (xs ' 0) 7)\n\tb (xs ' 2~) (zs~ (xs ' 0)) (ys~ (xs ' 0) 3)\nb : ws us vs ?\n\t||ws|| < 3 : (us~ (ws ' 0)) (vs~ (ws ' 0) 8)\n\ta (ws ' 2~) (vs~ (ws ' 0)) (us~ (ws ' 0) 4)\na (4 5 6 7 8 9 1 2 3 4) (1 2) (3 3)\n")]
for _body in _sh36:
    for _t in range(8):
        _xs = " ".join(str(_rnd.randint(0, 9)) for _ in range(_rnd.randint(2, 22)))
        _a = " ".join(str(_rnd.randint(0, 9)) for _ in range(_rnd.randint(2, 12)))
        _b = " ".join(str(_rnd.randint(0, 9)) for _ in range(_rnd.randint(2, 12)))
        _src = _body.replace("(4 5 6 7 8 9 1 2 3 4)", "(%s)" % _xs).replace("(4 5 6 7 8)", "(%s)" % _xs).replace("(1 2)", "(%s)" % _a).replace("(3 3)", "(%s)" % _b).replace("(9 9)", "(%s)" % _b)
        _d = tempfile.mkdtemp(); _p = os.path.join(_d, "t.sn"); open(_p, "w", encoding="utf-8").write(_src)
        _want = subprocess.run([sys.executable, os.path.join(HERE, "sign.py"), _p], capture_output=True, text=True, timeout=60).stdout
        if run_asm(sign_asm.generate(sign_interp.parse_source(_src), "linux"), linux=True)[1] != _want: _ok36 = False
check("段36: 複数の累積・位置の違う輪(2 形 × 8 通りを処理系と比べる)", _ok36, True)


_rnd.seed(37)
_ok37 = True
for _body in ("f : xs ys zs ?\n\t||xs|| = 1 : ys~ zs~ (xs ' 0)\n\tf (xs ' 1~) (ys~ (xs ' 0)) (zs~ (xs ' 0) 1)\nf (4 5 6 7 8) (1 2) (9 9)\n", "f : xs ys zs ?\n\t||xs|| = 1 : zs\n\tf (xs ' 1~) (ys~ (xs ' 0)) (zs~ (xs ' 0) 1)\nf (4 5 6 7 8) (1 2) (9 9)\n", "f : s a b ?\n\t||s|| = 1 : a~ b~ 0\n\tf (s ' 1~) (a~ (s ' 0)) (b~ (s ' 0) 2)\nf (4 5 6 7 8) (1 2) (9 9)\n"):
    for _t in range(8):
        _xs = " ".join(str(_rnd.randint(0, 9)) for _ in range(_rnd.randint(2, 18)))
        _a = " ".join(str(_rnd.randint(0, 9)) for _ in range(_rnd.randint(2, 10)))
        _b = " ".join(str(_rnd.randint(0, 9)) for _ in range(_rnd.randint(2, 10)))
        _src = _body.replace("(4 5 6 7 8)", "(%s)" % _xs).replace("(1 2)", "(%s)" % _a).replace("(9 9)", "(%s)" % _b)
        _d = tempfile.mkdtemp(); _p = os.path.join(_d, "t.sn"); open(_p, "w", encoding="utf-8").write(_src)
        _want = subprocess.run([sys.executable, os.path.join(HERE, "sign.py"), _p], capture_output=True, text=True, timeout=60).stdout
        if run_asm(sign_asm.generate(sign_interp.parse_source(_src), "linux"), linux=True)[1] != _want: _ok37 = False
check("段37: L を返す関数の複数の累積(3 形 × 8 通りを処理系と比べる)", _ok37, True)


_rnd.seed(38)
_ok38 = True
for _body in ("a : xs ys ?\n\t||xs|| < 3 : ys~ (xs ' 0)\n\tb (xs ' 2~) (ys~ (xs ' 0))\nb : xs ys ?\n\t||xs|| < 3 : ys~ (xs ' 0) 8\n\ta (xs ' 2~) (ys~ (xs ' 0) 3)\na (4 5 6 7 8 9 1 2 3 4) (1 2)\n", "a : xs ys ?\n\t||xs|| < 3 : ys~ 1\n\tb (xs ' 2~) (ys~ 7)\nb : xs ys ?\n\t||xs|| < 3 : ys~ 2\n\ta (xs ' 2~) (ys~ 9)\na (4 5 6 7 8 9 1 2 3 4) (1 2)\n", "a : xs ys ?\n\t||xs|| < 3 : ys\n\tb (xs ' 2~) (ys~ (xs ' 0) 1)\nb : xs ys ?\n\t||xs|| < 3 : ys~ 4\n\ta (xs ' 2~) (ys~ (xs ' 0))\na (4 5 6 7 8 9 1 2 3 4 5 6 7 8 9 1 2 3 4 5 6) (1 2)\n", "a : xs ys ?\n\t||xs|| < 3 : ys~ (xs ' 0)\n\t(xs ' 0) (b (xs ' 1~) (ys~ (xs ' 0)))~ 5\nb : xs ys ?\n\t||xs|| < 3 : ys~ (xs ' 0) 8\n\t(xs ' 0) (a (xs ' 1~) (ys~ (xs ' 0) 3))~ 6\na (4 5 6 7 8 9 1 2 3 4) (1 2)\n"):
    for _t in range(8):
        _xs = " ".join(str(_rnd.randint(0, 9)) for _ in range(_rnd.randint(2, 24)))
        _a = " ".join(str(_rnd.randint(0, 9)) for _ in range(_rnd.randint(2, 12)))
        _src = _body.replace("(4 5 6 7 8 9 1 2 3 4 5 6 7 8 9 1 2 3 4 5 6)", "(%s)" % _xs).replace("(4 5 6 7 8 9 1 2 3 4)", "(%s)" % _xs).replace("(1 2)", "(%s)" % _a)
        _d = tempfile.mkdtemp(); _p = os.path.join(_d, "t.sn"); open(_p, "w", encoding="utf-8").write(_src)
        _want = subprocess.run([sys.executable, os.path.join(HERE, "sign.py"), _p], capture_output=True, text=True, timeout=60).stdout
        if run_asm(sign_asm.generate(sign_interp.parse_source(_src), "linux"), linux=True)[1] != _want: _ok38 = False
check("段38: L を返す輪の累積(4 形 × 8 通りを処理系と比べる)", _ok38, True)


_rnd.seed(39)
_ok39 = True
_abc = "abcdefghijklmnopqrstuvwxyz"
for _body in ("a : s acc ?\n\t||s|| < 3 : acc `!`\n\tb (s ' 2~) (acc `x`)\nb : s acc ?\n\t||s|| < 3 : acc `?` `?`\n\ta (s ' 2~) (acc `yy`)\na `abcdefghij` `01`\n", "a : s acc ?\n\t||s|| < 3 : acc\n\tb (s ' 2~) (acc `x`)\nb : s acc ?\n\t||s|| < 3 : acc `-`\n\ta (s ' 2~) (acc `yy`)\na `abcdefghijklmnop` `01`\n", "a : s acc ?\n\t||s|| < 3 : acc (s ' 0) `!`\n\tb (s ' 2~) (acc (s ' 0))\nb : s acc ?\n\t||s|| < 3 : `<` acc\n\ta (s ' 2~) (acc (s ' 0) `.`)\na `abcdefghijklmnopqrstuvwxyz` `01`\n"):
    for _t in range(8):
        _n = _rnd.randint(2, 24)
        _s = "".join(_rnd.choice(_abc) for _ in range(_n))
        _a = "".join(_rnd.choice("0123456789") for _ in range(_rnd.randint(2, 12)))
        _src = _body.replace("`abcdefghijklmnopqrstuvwxyz`", "`%s`" % _s).replace("`abcdefghijklmnop`", "`%s`" % _s).replace("`abcdefghij`", "`%s`" % _s).replace("`01`", "`%s`" % _a)
        _d = tempfile.mkdtemp(); _p = os.path.join(_d, "t.sn"); open(_p, "w", encoding="utf-8").write(_src)
        _want = subprocess.run([sys.executable, os.path.join(HERE, "sign.py"), _p], capture_output=True, text=True, timeout=60).stdout
        if run_asm(sign_asm.generate(sign_interp.parse_source(_src), "linux"), linux=True)[1] != _want: _ok39 = False
check("段39: 文字列を返す輪の累積(3 形 × 8 通りを処理系と比べる)", _ok39, True)


# ---- 段 42: 作業領域の見積もりが外れても壊さない(入る個数を 0 にした asm が、スタックを壊さず `__` を返す)----
import re as _re42
_ok42 = True
for _src in ("a : xs ys acc ?\n\t||xs|| < 2 & ||ys|| < 2 : acc~ 1\n\t||xs|| >= 2 : b (xs ' 1~) ys (acc~ (xs ' 0) 1)\n\tb xs (ys ' 1~) (acc~ (ys ' 0))\nb : xs ys acc ?\n\t||xs|| < 2 & ||ys|| < 2 : acc~ 2\n\t||ys|| >= 2 : a xs (ys ' 1~) (acc~ (ys ' 0) 2)\n\ta (xs ' 1~) ys (acc~ (xs ' 0))\na (4 5) (1 2 3 4 5 6) (3 3)\n", "a : xs ys ?\n\t||xs|| < 3 : ys~ (xs ' 0)\n\tb (xs ' 2~) (ys~ (xs ' 0))\nb : xs ys ?\n\t||xs|| < 3 : ys~ (xs ' 0) 8\n\ta (xs ' 2~) (ys~ (xs ' 0) 3)\na (4 5 6 7 8 9 1 2 3 4) (1 2)\n", "a : s acc ?\n\t||s|| < 3 : acc `!`\n\tb (s ' 2~) (acc `x`)\nb : s acc ?\n\t||s|| < 3 : acc `?` `?`\n\ta (s ' 2~) (acc `yy`)\na `abcdefghij` `01`\n", "f : xs ys zs ?\n\t||xs|| = 1 : (ys~ (xs ' 0)) (zs~ (xs ' 0) 5)\n\tf (xs ' 1~) (ys~ (xs ' 0)) (zs~ (xs ' 0) 1)\nf (4 5 6 7 8) (1 2) (9 9)\n"):
    _asm = sign_asm.generate(sign_interp.parse_source(_src), "linux")
    _bad = _re42.sub(r"mov x11, #(\d+)  // 1 回で伸びる個数", "mov x11, #0  // 1 回で伸びる個数", _asm)
    if _bad == _asm: _ok42 = False
    else:
        _r = run_asm(_bad, linux=True)
        if _r[0] != "exit" or not _r[1].endswith("__\n") or "work area overflow" not in _r[1]: _ok42 = False
check("段42: 作業領域に入らない伸びは書く前に __(4 形)", _ok42, True)

# ---- 段 44: 輪の相手を通る別名 / 裸(bare)では作業領域あふれが罠になる ----
_src44 = "a : xs ys n m ?\n\tn < 3 : ys~ 1\n\tb (xs ' 1~) (ys~ (xs ' (n - 2))) (n - 1) (m + 1)\nb : xs ys n m ?\n\tm > 40 : ys~ 2\n\ta (xs ' 1~) (ys~ (xs ' (n - 1)) 7) (n - 1) (m + 1)\na (4 5 6 7 8 9 1 2 3 4) (1 2) 10 0\n"
_d = tempfile.mkdtemp(); _p = os.path.join(_d, "t.sn"); open(_p, "w", encoding="utf-8").write(_src44)
_want44 = subprocess.run([sys.executable, os.path.join(HERE, "sign.py"), _p], capture_output=True, text=True, timeout=60).stdout
check("段44: 輪の相手を通る長さの別名(処理系と同じ)", run_asm(sign_asm.generate(sign_interp.parse_source(_src44), "linux"), linux=True)[1], _want44)
_b44 = sign_asm.generate(sign_interp.parse_source(_src44), "bare")
_bb44 = _re42.sub(r"mov x11, #(\d+)  // 1 回で伸びる個数", "mov x11, #0  // 1 回で伸びる個数", _b44)
check("段44: bare は作業領域あふれで罠(黙って __ にしない)", (_bb44 != _b44) and ".Ltrap" in _bb44, True)

# ---- 段 45: bare の作業領域あふれは x16 = 2 の印つきの罠(Int の溢れと区別できる)----
_t45 = "f : xs acc ?\n\t||xs|| < 2 : acc~ (xs ' 0)\n\tf (xs ' 1~) (acc~ (xs ' (||xs|| / 2)))\n||f (4 5 6 7 8 9 1 2) (0 0)||\n"
_a45 = sign_asm.generate(sign_interp.parse_source(_t45), "bare")
_b45 = _re42.sub(r"mov x11, #(\d+)  // 1 回で伸びる個数", "mov x11, #0  // 1 回で伸びる個数", _a45)
check("段45: 正常な bare は 10", run_asm(_a45), ("ok", 10))
_c45 = Cpu(_b45)
try: _c45.run("_.main"); _x16 = None
except Trap: _x16 = _c45.r.get("x16")
check("段45: 作業領域あふれは x16=2 の罠", _x16, 2)
_i45 = Cpu(sign_asm.generate(sign_interp.parse_source("f : n ?\n\tn = 0 : 1\n\tn * (f (n - 1))\nf 30\n"), "bare"))
try: _i45.run("_.main"); _y = None
except Trap: _y = _i45.r.get("x16", 0)
check("段46: Int の溢れの罠は x16 = 1", _y, 1)

# ---- 段 49: 渡すだけの辺がある輪を乱数で処理系と比べる(sweep_passthru.py。2 つの種)----
for _seed in (1, 2):
    _o = subprocess.run([sys.executable, os.path.join(HERE, "sweep_passthru.py"), str(_seed)], capture_output=True, text=True, timeout=600).stdout
    check("段49: 渡すだけの辺の輪(乱数 %d)が処理系と一致" % _seed, bool(re.search(r"bad 0\s*$", _o.strip())) and " ok 0 " not in _o, True)

# ---- 段 51: 添字の範囲解析の乱数試験(fuzz_idx.py。受理された asm が処理系と同じ答えか)----
for _seed in (1, 2, 3, 4, 5, 6):
    _o = subprocess.run([sys.executable, os.path.join(HERE, "fuzz_idx.py"), str(_seed), "100"], capture_output=True, text=True, timeout=900).stdout
    _m = re.search(r"受理 (\d+) 断り (\d+) 不一致 (\d+)", _o)
    check("段51: 添字の乱数試験(種 %d): 受理した形が処理系と一致" % _seed, bool(_m) and _m.group(3) == "0" and int(_m.group(1)) > 5, True)

# ---- 段 52: 輪・複数の累積・文字列の累積の乱数試験(fuzz_ring.py)----
for _seed in (1, 2, 3, 4, 5, 6):
    _o = subprocess.run([sys.executable, os.path.join(HERE, "fuzz_ring.py"), str(_seed), "100"], capture_output=True, text=True, timeout=900).stdout
    _m = re.search(r"受理 (\d+) 断り (\d+) 不一致 (\d+)", _o)
    check("段52: 輪の乱数試験(種 %d): 受理した形が処理系と一致" % _seed, bool(_m) and _m.group(3) == "0" and int(_m.group(1)) > 80, True)

# ---- 段 56: カウンタ輪でも作業領域に入らない伸びは書く前に `__`(安全確認)----
_a56 = sign_asm.generate(sign_interp.parse_source("f0 : s i acc ?\n\ti >= ||s|| : acc\n\tf1 s (i + 1) (acc~ (s ' i))\nf1 : s i acc ?\n\ti >= ||s|| : acc~ 9\n\tf0 s (i + 2) (acc~ (s ' i) 8)\nf0 (4 5 6 7 3 2) 0 (0 0)\n"), "linux")
_b56 = _re42.sub(r"mov x11, #(\d+)  // 1 回で伸びる個数", "mov x11, #0  // 1 回で伸びる個数", _a56)
_r56 = run_asm(_b56, linux=True) if _b56 != _a56 else None
check("段56: カウンタ輪の作業領域あふれは `__`", bool(_r56) and _r56[1].endswith("__\n") and "work area overflow" in _r56[1], True)

# ---- 段 57: 小さな証明器(sign_prove.py)の単体試験 ----
import sign_prove
def _unsat(cs):
    _s = sign_prove.Sys()
    for c, k in cs: _s.add(c, k)
    return _s.unsat()
check("証明器: 0 ≤ x ≤ L-1 のとき x ≥ L は成り立たない", _unsat([({"x": 1}, 0), ({"L": 1, "x": -1}, -1), ({"x": 1, "L": -1}, 0)]), True)
check("証明器: 0 ≤ x ≤ L-1 のとき x ≥ L-1 は成り立ちうる", _unsat([({"x": 1}, 0), ({"L": 1, "x": -1}, -1), ({"x": 1, "L": -1}, 1)]), False)
check("証明器: 2x ≥ 1 かつ 2x ≤ 1 は整数では成り立たない(切り上げ)", _unsat([({"x": 2}, -1), ({"x": -2}, 1)]), True)
check("証明器: 3x ≥ 1 と 3x ≤ 2 も整数では成り立たない", _unsat([({"x": 3}, -1), ({"x": -3}, 2)]), True)
check("証明器: x ≥ 1 と x ≤ 1 は成り立つ", _unsat([({"x": 1}, -1), ({"x": -1}, 1)]), False)

# ---- 段 57: 見積もりモード(仕様 stack_abi §4.7: 上界は見積もり。超えたら `__`、名指しは information)----
_e57 = "f : xs i acc ?\n\ti >= 6 : acc\n\tf xs (i + 1) (acc~ (xs ' 0))\nf (4 5 6) (0 - 4) (0 0)\n"
_n57 = sign_interp.parse_source(_e57)
_t57 = sign_asm.generate(_n57, "linux")
check("見積もり: 証明できない上界も通り、information で関数が名指しされる", any(fn == "f" for fn, _ in sign_asm.LAST_INFOS), True)
_r57 = run_asm(_t57, linux=True)
check("見積もり: 見積もりを超えたら `__` と診断(黙って壊れない)", _r57[1].endswith("__\n") and "work area overflow" in _r57[1], True)
_in57 = "f : xs i acc ?\n\ti >= ||xs|| : acc\n\tf xs (i + 1) (acc~ (xs ' i))\nf (4 5 6) 0 (0 0)\n"
sign_asm.generate(sign_interp.parse_source(_in57), "linux")
check("見積もり: 証明できる形は information を出さない", sign_asm.LAST_INFOS, [])
_p57 = subprocess.run([sys.executable, os.path.join(HERE, "sign.py"), "--asm", "-"], input=_e57, capture_output=True, text=True)
_f57 = os.path.join(HERE, "_es57.sn"); open(_f57, "w").write(_e57)
_p57 = subprocess.run([sys.executable, os.path.join(HERE, "sign.py"), "--asm", _f57], capture_output=True, text=True)
_q57 = subprocess.run([sys.executable, os.path.join(HERE, "sign.py"), "--asm", _f57, "--no-estimate"], capture_output=True, text=True)
os.remove(_f57)
check("見積もり: --asm は information を stderr に出す", "information: f:" in _p57.stderr, True)
check("見積もり: --no-estimate は証明できない上界を断る", _q57.returncode != 0 and "出せません" in (_q57.stderr + _q57.stdout), True)

# ---- 段 58: 回る回数の精密化 ----
def _asm58(src):
    _p = sign_asm.generate(sign_interp.parse_source(src), "linux"); return _p, list(sign_asm.LAST_INFOS)
def _want58(src):
    _f = os.path.join(HERE, "_w58.sn"); open(_f, "w").write(src)
    _o = subprocess.run([sys.executable, os.path.join(HERE, "sign.py"), _f], capture_output=True, text=True).stdout; os.remove(_f); return _o
for _nm, _src, _info in [
    ("Int カウンタが定数の上限まで: 証明で通る(情報なし)", "f : i acc ?\n\ti >= 6 : acc\n\tf (i + 1) (acc~ (i * 2))\nf 0 (9 9)\n", False),
    ("定数の上限と歩幅 3", "f : i acc ?\n\ti > 9 : acc\n\tf (i + 3) (acc~ i i)\nf 1 (7 7)\n", False),
    ("器があっても定数で回るなら証明", "f : xs i acc ?\n\ti >= 4 : acc\n\tf xs (i + 1) (acc~ (xs ' 0))\nf (1 2) 0 (7 7)\n", False),
    ("開始が上限より先: 0 回", "f : i acc ?\n\ti >= 5 : acc\n\tf (i + 1) (acc~ i)\nf 7 (7 7)\n", False),
    ("変わらず渡される Int で回る: 見積もり(情報あり)", "f : n i acc ?\n\ti >= n : acc\n\tf n (i + 1) (acc~ i)\nf 5 0 (7 7)\n", True),
]:
    _a, _inf = _asm58(_src)
    check("段58: " + _nm + ": 答えが処理系と一致", run_asm(_a, linux=True)[1], _want58(_src))
    check("段58: " + _nm + ": 情報の有無", bool(_inf), _info)

# ---- 段 59: Int の実引数(包みの関数)・下向きカウンタ ----
for _nm, _src, _info in [
    ("Int の仮引数で回る見積もりを、包みの関数の Int の仮引数から渡す", "f : n i acc ?\n\ti >= n : acc\n\tf n (i + 1) (acc~ i)\ng : k ?\n\tf k 0 (7 7)\ng 4\n", True),
    ("下向きのカウンタ(0 まで): 証明", "f : n acc ?\n\tn <= 0 : acc\n\tf (n - 1) (acc~ n)\nf 5 (7 7)\n", False),
    ("下向きのカウンタ(負の下限・歩幅 2): 証明", "f : n acc ?\n\tn <= (0 - 3) : acc\n\tf (n - 2) (acc~ n n)\nf 4 (7 7)\n", False),
    ("下向きのカウンタ: 開始が下限以下なら 0 回", "f : n acc ?\n\tn <= 0 : acc\n\tf (n - 1) (acc~ n)\nf (0 - 4) (7 7)\n", False),
    ("下向きのカウンタを包みの関数から渡す", "f : n acc ?\n\tn <= 0 : acc\n\tf (n - 1) (acc~ n)\ng : k ?\n\tf k (7 7)\ng 6\n", False),
]:
    _a, _inf = _asm58(_src)
    check("段59: " + _nm + ": 答えが処理系と一致", run_asm(_a, linux=True)[1], _want58(_src))
    check("段59: " + _nm + ": 情報の有無", bool(_inf), _info)

# ---- 段 60: Int の式の実引数・多重ループ(状態の数)----
_ib = "f : n i acc ?\n\ti >= n : acc\n\tf n (i + 1) (acc~ i)\n"
for _nm, _src, _info in [
    ("Int の式 `k + 2` を実引数にする", _ib + "g : k ?\n\tf (k + 2) 0 (7 7)\ng 3\n", True),
    ("器の長さ `||xs|| * 2 - 1` を実引数にする", _ib + "g : xs ?\n\tf (||xs|| * 2 - 1) 0 (7 7)\ng (1 2 3)\n", True),
    ("Int の和 `k + j` を実引数にする", _ib + "g : k j ?\n\tf (k + j) 0 (7 7)\ng 2 3\n", True),
    ("二重ループ(定数の上限 2 つ): 状態の数で証明", "f : i j acc ?\n\ti >= 3 : acc\n\tj >= 4 : f (i + 1) 0 acc\n\tf i (j + 1) (acc~ (i * 10 + j))\nf 0 0 (7 7)\n", False),
]:
    _a, _inf = _asm58(_src)
    check("段60: " + _nm + ": 答えが処理系と一致", run_asm(_a, linux=True)[1], _want58(_src))
    check("段60: " + _nm + ": 情報の有無", bool(_inf), _info)
_a60, _inf60 = _asm58("f : i j acc ?\n\ti >= 3 : acc\n\tj >= i : f (i + 1) 0 acc\n\tf i (j + 1) (acc~ j)\nf 0 0 (7 7)\n")
check("段60: 内側の上限が外側のカウンタ(定数でない)なら、証明とは言わず information を出す", bool(_inf60), True)
_a60, _inf60 = _asm58("f : i j acc ?\n\ti >= 3 : acc\n\tj >= 4 : f (i + 1) 0 acc\n\tf i (j + 1) (acc~ j)\nf 0 (0 - 2) (7 7)\n")
check("段60: カウンタが 0 以上と言えない(負で入る)二重ループは証明で通さない", bool(_inf60), True)

for _seed in (1, 2, 3):
    _o = subprocess.run([sys.executable, os.path.join(HERE, "fuzz_cnt.py"), str(_seed), "100"], capture_output=True, text=True, timeout=900).stdout
    _m = re.search(r"受理 (\d+) \(証明 (\d+) / 見積もり (\d+)、うち答えが一致 (\d+)\) 断り (\d+) 不一致 (\d+)", _o)
    check("段58: 回る回数の乱数試験(種 %d): 証明した形は一致、見積もりの形は一致か `__`" % _seed, bool(_m) and _m.group(6) == "0" and int(_m.group(1)) > 60 and int(_m.group(2)) > 20, True)
_env58 = dict(os.environ, SIGN_OLD="0")
for _seed in (1, 2):
    _o = subprocess.run([sys.executable, os.path.join(HERE, "fuzz_idx.py"), str(_seed), "100"], capture_output=True, text=True, timeout=900, env=_env58).stdout
    _m = re.search(r"受理 (\d+) 断り (\d+) 不一致 (\d+)", _o)
    check("段58: 個別規則を外して証明器だけでも添字の乱数試験(種 %d)が一致、受理は旧規則の併用以上" % _seed, bool(_m) and _m.group(3) == "0" and int(_m.group(1)) > 55, True)
_nest58 = "f : m i acc ?\n\ti >= ||m|| | i < 0 | ||m ' i|| < 2 : acc\n\tf m (i + 1) (acc~ ((m ' i) ' 1))\nf ((1 2 3) (4 5) (6 7 8 9)) 0 (0 0)\n"
os.environ["SIGN_OLD"] = "0"
try: _a58n = sign_asm.generate(sign_interp.parse_source(_nest58), "linux"); _ok58n = True
except sign_asm.AsmError: _ok58n = False
os.environ.pop("SIGN_OLD", None)
check("段58: 入れ子の要素の長さの条件を、証明器だけで添字の範囲に使える", _ok58n, True)
if _ok58n: check("段58: ……その答えは処理系と一致", run_asm(_a58n, linux=True)[1], _want58(_nest58))
_refuse58 = [
    ("輪で食う器が無い形は、見積もりでもまだ出せない", "f : n acc ?\n\tn >= 6 : acc\n\tg (n + 1) (acc~ n)\ng : n acc ?\n\tn >= 6 : acc\n\tf (n + 2) (acc~ n n)\nf 0 (9 9)\n"),
]
for _nm, _src in _refuse58:
    try: sign_asm.generate(sign_interp.parse_source(_src), "linux"); _r = "通った"
    except sign_asm.AsmError: _r = "断った"
    check("段58: " + _nm, _r, "断った")

# ---- 段 61: 別実装(llvm-mc)で、この試験で生成した全アセンブリが組めるか ----
import llvm_check
if llvm_check.available():
    _seen61 = set(); _bad61 = []
    for _t in _GEN_ALL:
        if _t in _seen61: continue
        _seen61.add(_t); _e = llvm_check.check(_t)
        if _e: _bad61.append(_e)
    check("段61: 生成した全アセンブリ(%d 本)が llvm-mc で組める" % len(_seen61), _bad61[:1], [])
else: print("段61: llvm-mc が無いので省略")

# ---- 段 63: 定数名どうしの計算でできた定義 ----
for _nm, _src in [("定数名どうしの + * で畳む", "a : 3\nb : a * 4 + 1\nf : x ? x + b\nf 2\n"),
                  ("16 進の基底番地+オフセット(MMIO の名前の形)", "base : 0x9100000\nreg : base + 0x08\nf : x ? reg - base + x\nf 1\n")]:
    _a = sign_asm.generate(sign_interp.parse_source(_src), "linux")
    check("段63: " + _nm + ": 答えが処理系と一致", run_asm(_a, linux=True)[1], _want58(_src))
_s63 = "g : x ? x + 1\nc : g 3\nc\n"
check("段63(第106段で出せるようになった): 定数でない定義(関数の結果)は起動のとき評価する: 答えが処理系と一致", run_asm(sign_asm.generate(sign_interp.parse_source(_s63), "linux"), linux=True)[1], _want58(_s63))
_s63b = "g : x ? x + 1\nc : g\nc 3\n"
check("段63(別名の展開で出せるようになった): 値が関数そのものの定義(別名)は同じ関数として出る: 答えが処理系と一致", run_asm(sign_asm.generate(sign_interp.parse_source(_s63b), "linux"), linux=True)[1], _want58(_s63b))

# ---- 段 64: 書き込み `a # v`(64 ビット、番地を返す)----
def _cpu64(src):
    _a = sign_asm.generate(sign_interp.parse_source(src), "linux"); _c = Cpu(_a); _c.run("_start"); return _c
_w = "w : a v ? a # v\nseq2 : a b ? b\nseq3 : a b c ? c\n"
for _nm, _src, _mem in [
    ("2 か所に書いて最後の式を印字", _w + "seq3 (w 4096 5) (w 4104 6) 42\n", {4096: 5, 4104: 6}),
    ("同じ番地に 2 回書くと後の値が残る(左から右)", _w + "seq3 (w 4096 1) (w 4096 2) 9\n", {4096: 2}),
    ("値が __ なら何も書かない(番地は返る)", _w + "seq3 (w 4096 7) (w 4096 __) 9\n", {4096: 7}),
    ("負の値は 2 の補数で書く", _w + "seq2 (w 4096 (0 - 2)) 3\n", {4096: (1 << 64) - 2}),
    ("定数名どうしの番地", "seq2 : a b ? b\nbase : 4096\nreg : base + 8\nseq2 (reg # 11) 5\n", {4104: 11}),
]:
    _c = _cpu64(_src)
    check("段64: " + _nm + ": 印字が処理系と一致", _c.out.decode(), _want58(_src))
    check("段64: " + _nm + ": メモリの中身", {k: _c.load(k) for k in _mem}, _mem)
for _nm, _src in [("リストを書く", "w : a v ? a # v\nw 4096 (1 2 3)\n")]:
    try: sign_asm.generate(sign_interp.parse_source(_src), "linux"); _r64 = "通った"
    except sign_asm.AsmError: _r64 = "断った"
    check("段64: 断る: " + _nm, _r64, "断った")
# ---- 段 64: 9 個以上の引数(スタック渡し)----
for _nm, _src in [
    ("9 個", "s9 : a b c d e f g h i ? a + b * 2 + c * 3 + d * 4 + e * 5 + f * 6 + g * 7 + h * 8 + i * 9\ns9 1 2 3 4 5 6 7 8 9\n"),
    ("器が 8 語目をまたぐ", "w : a b c d e f g h xs ys ? ||xs|| + ||ys|| + a + h\nw 1 2 3 4 5 6 7 8 (1 2 3) (4 5)\n"),
    ("末尾ループの中で 9 個を更新", "t : a b c d e f g h i ?\n\ti <= 0 : a\n\tt (a + 1) b c d e f g h (i - 1)\nt 0 1 2 3 4 5 6 7 5\n"),
    ("別の関数から 10 個を呼ぶ(再帰の中)", "s10 : a b c d e f g h i j ? a + i * 10 + j * 100\nr : n acc ?\n\tn <= 0 : acc\n\tr (n - 1) (acc + (s10 n 2 3 4 5 6 7 8 n 1))\nr 5 0\n"),
    ("器の引数の先頭を 9 個目に", "g : a b c d e f g h x ?\n\tx ' 0 + a + h\nf : n ?\n\tg n 2 3 4 5 6 7 n (7 9)\nf 3\n"),
]:
    _a = sign_asm.generate(sign_interp.parse_source(_src), "linux")
    check("段64: スタック渡し: " + _nm + ": 答えが処理系と一致", run_asm(_a, linux=True)[1], _want58(_src))

# ---- 段 65: `path`@~(取り込みの展開)----
import tempfile as _tf
_d65 = _tf.mkdtemp()
open(os.path.join(_d65, "mod.sn"), "w").write("dbl : x ? x * 2\ninc : x ? x + 1\n")
open(os.path.join(_d65, "main.sn"), "w").write("`mod.sn`@~\ninc (dbl 20)\n")
open(os.path.join(_d65, "twice.sn"), "w").write("`mod.sn`@~\n`mod.sn`@~\ninc (dbl 5)\n")
open(os.path.join(_d65, "mid.sn"), "w").write("`mod.sn`@~\nquad : x ? dbl (dbl x)\n")
open(os.path.join(_d65, "chain.sn"), "w").write("`mid.sn`@~\ninc (quad 3)\n")
open(os.path.join(_d65, "clash.sn"), "w").write("`mod.sn`@~\ndbl : x ? x\ndbl 1\n")        # あとの定義が勝つ
open(os.path.join(_d65, "clash2.sn"), "w").write("`mod.sn`@~\nk : 5\n`k2.sn`@~\n1\n")
open(os.path.join(_d65, "k2.sn"), "w").write("k : 6\n")
open(os.path.join(_d65, "loop_a.sn"), "w").write("`loop_b.sn`@~\na : x ? x\n")
open(os.path.join(_d65, "loop_b.sn"), "w").write("`loop_a.sn`@~\nb : x ? x\n")
open(os.path.join(_d65, "loop.sn"), "w").write("`loop_a.sn`@~\na 1\n")
open(os.path.join(_d65, "missing.sn"), "w").write("`nothing.sn`@~\n1\n")
open(os.path.join(_d65, "effect.sn"), "w").write("7\n")
open(os.path.join(_d65, "eff_main.sn"), "w").write("`effect.sn`@~\n1\n")
def _asm65(name):
    sign_asm.IMPORT_DIR[0] = _d65
    try: return sign_asm.generate(sign_interp.parse_source(open(os.path.join(_d65, name)).read()), "linux")
    finally: sign_asm.IMPORT_DIR[0] = None
def _want65(name):
    return subprocess.run([sys.executable, os.path.join(HERE, "sign.py"), os.path.join(_d65, name)], capture_output=True, text=True).stdout
for _nm, _f in [("名前の重なり: あとの定義が勝つ", "clash.sn"), ("1 段の取り込み", "main.sn"), ("同じファイルを 2 回取り込んでも 1 回", "twice.sn"), ("取り込みの連鎖(取り込み先がさらに取り込む)", "chain.sn")]:
    check("段65: " + _nm + ": 答えが処理系と一致", run_asm(_asm65(_f), linux=True)[1], _want65(_f))
for _nm, _f in [("値の定義の重なり", "clash2.sn"), ("循環", "loop.sn"), ("見つからないファイル", "missing.sn"), ("最上位に式があるファイルの取り込み", "eff_main.sn")]:
    try: _asm65(_f); _r65 = "通った"
    except sign_asm.AsmError: _r65 = "断った"
    check("段65: 断る: " + _nm, _r65, "断った")

# ---- 段 66: 読み `@a`・左が __ の `#` ----
_s2 = "seq2 : a b ? b\nseq3 : a b c ? c\n"
for _nm, _src in [
    ("書いた値を読み戻す", _s2 + "seq3 (4096 # 77) (8192 # (@4096 + 1)) @8192\n"),
    ("左が __ の書き込みは何も書かず __(右は評価しない)", _s2 + "seq2 (__ # (8192 # 6)) @8192\n"),
    ("0 除算で __ になる番地へは書かない", _s2 + "seq3 (4096 # 5) ((1 / 0) # 9) @4096\n"),
    ("読みの番地が __ なら __", _s2 + "seq2 (4096 # 5) @(1 / 0)\n"),
]:
    _a = sign_asm.generate(sign_interp.parse_source(_src), "linux")
    check("段66: " + _nm + ": 答えが処理系と一致", run_asm(_a, linux=True)[1], _want58(_src))

# ---- 段 67: 文字の定数定義と、文字を書く `#`(UART への書き込みの列を記録して処理系の出力と比べる)----
class _CpuLog(Cpu):
    def __init__(self, text, addr): super().__init__(text); self.addr = addr; self.log = []
    def store(self, a, v, n=8):
        if a == self.addr: self.log.append(v & 0xff)
        super().store(a, v, n)
_c67 = _CpuLog(sign_asm.generate(sign_interp.parse_source("nl : 0u000A\nbang : \\!\nseq3 : a b c ? c\nseq3 (4096 # bang) (4096 # nl) 7\n"), "linux"), 4096)
_c67.run("_start")
check("段67: 文字の定数を同じ番地へ書いた列", bytes(_c67.log), b"!\n")
_dc = os.path.join(HERE, "draw_circle.sn")
if os.path.exists(_dc):
    _c67 = _CpuLog(sign_asm.generate(sign_interp.parse_source(open(_dc, encoding="utf-8").read()), "linux"), 0x9000000)
    _c67.run("_start")
    _w67 = subprocess.run([sys.executable, os.path.join(HERE, "sign.py"), _dc], capture_output=True, text=True).stdout
    check("段67: draw_circle.sn の UART への書き込みの列が、処理系の出力(最後の結果の行を除く)と一致", bytes(_c67.log).decode(), _w67[:len(bytes(_c67.log).decode())])
    check("段67: ……最後の結果の行は標準出力へ", _c67.out.decode() + "", _w67[len(bytes(_c67.log).decode()):])

# ---- 段 68: Char − Char とビット演算 ----
_bf = "f : a b ? (a && b) + (a || b) * 10 + (a ;; b) * 100\n"
for _nm, _src in [
    ("算術右シフト(負)", "(0-8) >> 1\n"), ("&&", "6 && 3\n"), ("||", "6 || 3\n"), (";;", "6 ;; 3\n"),
    ("右シフトの数が負なら __", "5 >> (0-1)\n"), ("左シフトの数が負なら __", "5 << (0-1)\n"),
    ("左シフト", "3 << 4\n"), ("1 << 62", "1 << 62\n"), ("大きな右シフト(正)", "7 >> 70\n"),
    ("大きな右シフト(負)", "(0-7) >> 70\n"), ("0 << 100", "0 << 100\n"),
    ("引数経由の三つ組", _bf + "f 6 3\n"), ("左右のシフト", "g : a ? (a << 3) >> 1\ng 5\n"),
    ("左が __ の && は右", "u : a ? (a && 3)\nu __\n"), ("変数のシフト数", "u : a b ? a << b\nu 3 61\n"),
    ("Char − Char", "ca : 0u0041\ncb : 0u0043\nca - cb\n"), ("Char − Char(逆順)", "ca : 0u0041\ncb : 0u0043\ncb - ca\n"),
]:
    _a = sign_asm.generate(sign_interp.parse_source(_src), "linux")
    check("段68: " + _nm + ": 答えが処理系と一致", run_asm(_a, linux=True)[1], _want58(_src))
for _nm, _src in [("1 << 63 は値域の外で罠", "u : a ? a << 63\nu 1\n"), ("1 << 64 も罠", "u : a ? a << 64\nu 1\n")]:
    _a = sign_asm.generate(sign_interp.parse_source(_src), "linux")
    check("段68: " + _nm, run_asm(_a, linux=True)[1], None)

def refuses(src):
    try: sign_asm.generate(sign_interp.parse_source(src), "linux")
    except sign_asm.AsmError: return True
    return False

# ---- 段 69: 文字列のリスト `[`ab` , `cd`]` と括りの仮引数 `[a b c]` ----
_art = "ART : [`..#` , `#.#` , `###`]\n"
_cnt = "cnt : s i ?\n\ti >= ||s|| : 0\n\t((s ' i) = 0u0023) : 1 + (cnt s (i + 1))\n\tcnt s (i + 1)\ntot : rows r ?\n\tr >= 3 : 0\n\t(cnt (rows ' r) 0) + (tot rows (r + 1))\n"
for _nm, _src in [
    ("文字列のリストの要素を数える", _art + _cnt + "tot ART 0\n"),
    ("要素は文字列", _art + "ART ' 1\n"), ("要素の要素は文字", _art + "(ART ' 2) ' 0\n"),
    ("範囲の外は __", _art + "ART ' 5\n"),
    ("積の Int リスト・入れ子", "B : [1 , 2 , 3]\nC : [[1 2] , [3 4 5]]\nf : xs ? xs ' 1\n(f B) + (f (C ' 1))\n"),
    ("文字列のリストと積のリストが別の名前に", "A : [`ab` , `cd`]\nB : [1 , 2]\nf : xs ? xs ' 1\ng : s ? ||s||\nseq2 : a b ? b\nseq2 (g (A ' 0)) (f B)\n"),
    ("括り: 長さが合う", "f : [a b c] ? a + b * 10 + c * 100\nf [1 2 3]\n"),
    ("括り: 短い(足りない名前は __)", "f : [a b c] ? a + b * 10 + c * 100\nf [1 2]\n"),
    ("括り: 長い(余りは捨てる)", "f : [a b c] ? a + b * 10 + c * 100\nf [1 2 3 4]\n"),
    ("括り: 名前のリスト", "f : [a b c] ? a + b * 10 + c * 100\nxs : [4 5 6]\nf xs\n"),
    ("括り: 自分への呼び", "f : n [a b] ?\n\tn <= 0 : a + b\n\tf (n - 1) [b (a + b)]\nf 10 [0 1]\n"),
    ("括り: ほかの器の引数と並ぶ", "g : x [a b] ?\n\tx > 1 : a\n\tb\nh : v ? g (v ' 0) (v ' 1~)\nh [5 7 8]\n"),
    ("括り: 残り ~r(第110段で出せるようにした)", "f : [a ~r] ? a\nf [1 2]\n"),
    ("括り: 残りを畳む", "sum : [h ~t] ? h + (sum t)\nsum [1 2 3 4]\n"),
    ("括り: スカラーを渡す形(長さ 1 の並びとして読む)", "f : [a b c] ? a + b\nf 5\n"),
    ("Int は長さ 1 の並び: ||3||", "||3||\n"),
    ("Int は長さ 1 の並び: 添字 0", "f : a ? a ' 0\nf 3\n"),
    ("Int は長さ 1 の並び: 添字 1 は __", "f : a ? a ' 1\nf 3\n"),
    ("Int は長さ 1 の並び: 畳み", "f : a ? [+] a\nf 5\n"),
    ("仮引数と定数の並びの添字 1", "c : 4\nf : x ? (x c 4) ' 1\nf 7\n"),
    ("仮引数と定数の並びの添字 0", "c : 4\nf : x ? (x c 4) ' 0\nf 7\n"),
    ("仮引数と定数の並びの添字 -1", "f : x y ? (x y 3) ' (0 - 1)\nf 7 8\n"),
    ("仮引数と定数の並びの添字が外れる", "f : x ? (x 3) ' 5\nf 7\n"),
    ("仮引数の並びの長さ", "f : x y ? ||(x y 3 4)||\nf 7 8\n"),
    ("仮引数が __ なら関数は __", "c : 4\nf : x ? (x c 4) ' 1\nf __\n"),
    ("__ になりうる要素: 比べが真", "f : x y ? ((x < y) 3 y) ' 1\nf 1 2\n"),
    ("__ になりうる要素: 比べが偽(落ちて詰まる)", "f : x y ? ((x < y) 3 y) ' 1\nf 5 2\n"),
    ("__ になりうる要素: 負の添字", "f : x y ? ((x < y) 3 y) ' (0 - 1)\nf 5 2\n"),
    ("__ になりうる要素: 数が足りない添字", "f : x y ? ((x < y) (y < x) 9) ' 2\nf 1 2\n"),
    ("__ になりうる要素: 長さ", "f : x y ? ||((x < y) 3 y)||\nf 5 2\n"),
    ("__ になりうる要素: 関数の呼び", "g : a ? (a > 2)\nf : x ? ((g x) 8 x) ' 1\nf 5\n"),
    ("実行時の添字: 先頭", "f : x y i ? (x y 9) ' i\nf 7 8 0\n"),
    ("実行時の添字: 末尾", "f : x y i ? (x y 9) ' i\nf 7 8 2\n"),
    ("実行時の添字: 範囲の外は __", "f : x y i ? (x y 9) ' i\nf 7 8 3\n"),
    ("実行時の添字: 負は後ろから", "f : x y i ? (x y 9) ' i\nf 7 8 (0 - 1)\n"),
    ("実行時の添字: 後ろからでも足りない", "f : x y i ? (x y 9) ' i\nf 7 8 (0 - 4)\n"),
    ("実行時の添字: __ になりうる要素", "f : x y i ? ((x < y) 3 y) ' i\nf 5 2 1\n"),
    ("実行時の添字: 添字が __ になりうる", "f : x y i ? (x y) ' (i < 1)\nf 5 2 3\n"),
    ("先頭の呼びと余りの実引数", "g : a ? a + 1\nf : x ? (g x 5) ' 1\nf 3\n"),
    ("先頭の呼びと余りの実引数 2 個", "g : a ? a + 1\nf : x ? (g x 5 6) ' 2\nf 3\n"),
    ("先頭の呼びが __ を返すと落ちる", "g : a ? (a > 2)\nf : x ? (g x 5) ' 0\nf 1\n"),
    ("逆適用 x g", "g : a ? a + 1\nf : x ? x g\nf 3\n"),
    ("逆適用の括りの添字", "g : a ? a + 1\nf : x ? (x g) ' 0\nf 3\n"),
    ("__ になりうる要素 12 個", "f : x ? ((x < 2) 1 2 3 4 5 6 7 8 9 10 11) ' 11\nf 3\n"),
    ("入れ子の並びの添字(Int を選ぶ)", "f : x ? ((x 2) 3) ' 1\nf 3\n"),
    ("入れ子の並びの負の添字", "f : x ? ((x 2) 3) ' (0 - 1)\nf 3\n"),
    ("入れ子の並びの長さ", "f : x ? ||((x 2) 3)||\nf 3\n"),
    ("入れ子の並びの添字の連なり", "f : x ? (((x 2) 3) ' 0) ' 1\nf 3\n"),
    ("入れ子の並びの範囲の外は __", "f : x ? ((x 2) (x 3) 4) ' 5\nf 3\n"),
    ("入れ子の並びで後ろの Int を選ぶ", "f : x ? ((x 2) (x 3) 4) ' 2\nf 3\n"),
    ("入れ子の並びを選んで長さ", "f : x ? ||(((x 2) 3) ' 0)||\nf 3\n"),
    ("入れ子の並びを選んで引数に渡す", "len : a ? ||a||\nf : x ? len (((x 2 5) 3) ' 0)\nf 3\n"),
    ("入れ子の並びを選んで添字(3 段)", "f : x y ? ((x (y 5)) 3) ' 0 ' 1\nf 3 4\n"),
]:
    _a = sign_asm.generate(sign_interp.parse_source(_src), "linux")
    check("段69: " + _nm + ": 答えが処理系と一致", run_asm(_a, linux=True)[1], _want58(_src))
for _nm, _src in [("Int の入れ子と文字列の入れ子が同じ組に", "A : [`ab` , `cd`]\nC : [[1 2] , [3 4 5]]\nA ' 0\n"),
                  ("括り: 残りの後ろの名前", "f : [~i l] ? l\nf [1 2]\n")]:
    check("段69: 断る: " + _nm, refuses(_src), True)

# ---- 段 70: 文字を関数の引数に渡す・Char ± Int ----
for _nm, _src in [
    ("文字の引数を比べる", "isa : c ?\n\tc = 0u0041 : 1\n\t0\nisa (`ABC` ' 0)\n"),
    ("文字をそのまま返す", "nx : c ? c\nnx (`ABC` ' 1)\n"),
    ("文字 − 文字", "d : c ? c - 0u0030\nd (`7` ' 0)\n"),
    ("実引数の文字が __(範囲の外)なら呼び全体が __", "d : c ? c\nd (`7` ' 3)\n"),
    ("文字を引数に回す再帰", "cnt : s i c ?\n\ti >= ||s|| : 0\n\t((s ' i) = c) : 1 + (cnt s (i + 1) c)\n\tcnt s (i + 1) c\ncnt `a,b,,c` 0 0u002C\n"),
    ("文字を持ち回る末尾再帰", "w : c k ?\n\tk <= 0 : c\n\tw c (k - 1)\nw (`xyz` ' 2) 4\n"),
    ("Char + Int", "f : c n ? c + n\nf 0u30 5\n"), ("Char + Int が範囲の外", "f : c n ? c + n\nf 0u30 80\n"),
    ("Char − Int", "f : c n ? c - n\nf 0u30 (0-1)\n"), ("字面の Char + 引数", "f : n ? 0u30 + n\nf 7\n"),
    ("__ の文字 + Int は __", "f : c n ? c + n\nf (`a` ' 5) 1\n"), ("Char − Int が負になる", "f : c n ? c - n\nf 0u30 49\n"),
    ("文字の算術(最後の式)", "s : `abc`\n(s ' 0) + 1\n"), ("字面の文字を引数に", "f : c ? c\nf \\a\n"),
    ("Char + Int が U+0080 以上", "f : c n ? c + n\nf 0u7F 1\n"),
]:
    _a = sign_asm.generate(sign_interp.parse_source(_src), "linux")
    check("段70: " + _nm + ": 答えが処理系と一致", run_asm(_a, linux=True)[1], _want58(_src))

# ---- 段 70(続き): 1 要素のリスト `[0]` をリストの仮引数へ ----
for _nm, _src in [
    ("初期値 [0] の累積(リストを返す)", "mk : n acc ?\n\tn <= 0 : acc\n\tmk (n - 1) (acc~ n (n * n))\nmk 3 [0]\n"),
    ("初期値 [7] の累積を後で足す", "sm : xs i ?\n\ti >= ||xs|| : 0\n\t(xs ' i) + (sm xs (i + 1))\nmk : n acc ?\n\tn <= 0 : acc\n\tmk (n - 1) (acc~ n)\nsm (mk 3 [7]) 0\n"),
]:
    _a = sign_asm.generate(sign_interp.parse_source(_src), "linux")
    check("段70: " + _nm + ": 答えが処理系と一致", run_asm(_a, linux=True)[1], _want58(_src))

# ---- 段 71: Char + Char と、近い番地の information ----
for _nm, _src in [
    ("Char + Char", "f : a b ? a + b\nf 0u30 0u31\n"), ("Char + Char が範囲の外", "f : a b ? a + b\nf 0u40 0u40\n"),
    ("Char + Char の片方が __", "f : a b ? a + b\nf (`x` ' 0) (`x` ' 4)\n"), ("Char + 同じ Char", "f : a ? a + a\nf 0u20\n"),
    ("字面の文字を足す(最後の式)", "s : `abc`\n(s ' 0) + (s ' 1)\n"),
]:
    _a = sign_asm.generate(sign_interp.parse_source(_src), "linux")
    check("段71: " + _nm + ": 答えが処理系と一致", run_asm(_a, linux=True)[1], _want58(_src))
_n71 = "a : 0x100\nb : 0x104\nseq2 : x y ? y\nseq2 (a # 5) (@b)\n"
sign_asm.generate(sign_interp.parse_source(_n71), "linux")
check("段71: 8 バイト未満の番地の組は information に出る", any("幅より近い" in w for _, w in sign_asm.LAST_INFOS), True)
sign_asm.generate(sign_interp.parse_source("a : 0x100\nb : 0x108\nseq2 : x y ? y\nseq2 (a # 5) (@b)\n"), "linux")
check("段71: 8 バイト以上離れていれば出ない", any("幅より近い" in w for _, w in sign_asm.LAST_INFOS), False)

# ---- 段 72: 幅つきの番地 `1x…` `2x…` `4x…` `8x…`(value_representation.md §5)----
for _nm, _src in [
    ("幅ごとに切る(1・4・2 byte)", "seq4 : a b c d ? d\nseq4 (1x00001000 # 0x1234) (4x00001100 # (0-1)) (2x00001200 # 0x12345) (@1x00001000 + (@4x00001100) + (@2x00001200))\n"),
    ("名前で定義した幅つきの番地", "a : 4x00001000\nseq3 : x y z ? z\nseq3 (a # 0x1FFFFFFFF) (a + 0) (@a)\n"),
    ("4 byte 刻みの 2 つの番地は重ならない", "a : 4x00001000\nb : 4x00001004\nseq4 : p q r s ? s\nseq4 (a # 0x1AAAAAAAA) (b # (0-2)) (1x00001008 # 0x1ff) ((@a) + (@b) + (@1x00001008) + (@2x00001000))\n"),
    ("幅つきの番地 + 数 は同じ幅", "a : 4x00001000\nseq3 : x y z ? z\nseq3 ((a + 8) # 0x1FFFFFFFF) ((8 + a) # 0x2FFFFFFFF) (@(a + 8))\n"),
    ("幅は仮引数を通って届く", "put : p i v ? (p + (i * 4)) # v\nget : p i ? @(p + (i * 4))\nseq3 : x y z ? z\nseq3 (put 4x00002000 0 0x1FFFFFFFF) (put 4x00002000 1 7) ((get 4x00002000 0) + (get 4x00002000 1))\n"),
    ("語幅の番地は 64 bit", "seq2 : a b ? b\nseq2 (0x00003000 # 0x1FFFFFFFF) (@0x00003000)\n"),
]:
    _a = sign_asm.generate(sign_interp.parse_source(_src), "linux")
    check("段72: " + _nm + ": 答えが処理系と一致", run_asm(_a, linux=True)[1], _want58(_src))
check("段72: 幅の違う番地が同じ仮引数へ渡る形は断る", refuses("g : p ? @p\nseq2 : a b ? b\nseq2 (g 4x00001000) (g 2x00001000)\n"), True)
sign_asm.generate(sign_interp.parse_source("a : 4x00001000\nb : 4x00001002\nseq2 : x y ? y\nseq2 (a # 5) (@b)\n"), "linux")
check("段72: 4 byte の番地が 2 byte 隔てて重なれば information", any("幅より近い" in w for _, w in sign_asm.LAST_INFOS), True)
sign_asm.generate(sign_interp.parse_source("a : 4x00001000\nb : 4x00001004\nseq2 : x y ? y\nseq2 (a # 5) (@b)\n"), "linux")
check("段72: 4 byte の番地が 4 byte 隔てれば出ない", any("幅より近い" in w for _, w in sign_asm.LAST_INFOS), False)
import tempfile
with tempfile.NamedTemporaryFile("w", suffix=".sn", delete=False, encoding="utf-8") as _tf: _tf.write("3x1000 # 1\n")
_r = subprocess.run([sys.executable, os.path.join(HERE, "sign.py"), _tf.name], capture_output=True, text=True); os.unlink(_tf.name)
check("段72: 3x は機械に無い幅として診断", "命令は機械にありません" in (_r.stdout + _r.stderr), True)

# ---- 段 73: 最上位に式が無いファイルは、最後の定義の値を印字する ----
for _nm, _src in [
    ("Int の定義", "x : 5\n"), ("関数の定義(<fn/N>)", "f : a ? a\ng : a b ? a\n"), ("括りの仮引数の関数", "f : [a b] c ? a\n"),
    ("文字列の定義", "s : `hi`\n"), ("リストの定義", "l : [1 2 3]\n"), ("同じ名前の定義は最後の右辺", "x : 1\nx : 2\n"),
    ("__ の定義", "z : __\n"), ("番地の定義", "p : 0x10\n"), ("文字の定義", "c : 0u41\n"),
]:
    _a = sign_asm.generate(sign_interp.parse_source(_src), "linux")
    check("段73: " + _nm + ": 答えが処理系と一致", run_asm(_a, linux=True)[1], _want58(_src))

# ---- 段 74: Char * Int(回数が定数)は文字列の繰り返し ----
for _nm, _src in [
    ("字面そのまま", "0u30 * 3\n"), ("名前に束ねる", "bar : 0u3D * 4\nbar\n"),
    ("並置で連結", "bar : 0u3D * 4\ntitle : `[` bar `]`\ntitle\n"),
    ("長さ", "bar : 0u2D * 7\n||bar||\n"), ("要素", "bar : 0u2D * 7\nbar ' 3\n"),
]:
    _a = sign_asm.generate(sign_interp.parse_source(_src), "linux")
    check("段74: " + _nm + ": 答えが処理系と一致", run_asm(_a, linux=True)[1], _want58(_src))
check("段74: 回数が実行時に決まる形は断る", refuses("f : k ? 0u30 * k\nf 3\n"), True)
check("段74: 回数 0 は断る", refuses("0u30 * 0\n"), True)

# ---- 段 75: charset: utf32(メモリ上の Char が 4 バイト。IO 境界は UTF-8) ----
def _want_u32(src):
    _f = os.path.join(HERE, "_w75.sn"); open(_f, "w", encoding="utf-8").write(src)
    _o = subprocess.run([sys.executable, os.path.join(HERE, "sign.py"), _f, "--charset=utf32"], capture_output=True).stdout.decode("utf-8", "replace"); os.remove(_f); return _o
def _asm_u32(src): return sign_asm.generate(sign_interp.parse_source(src), "linux", charset="utf32")
for _nm, _src in [
    ("日本語の文字列を最後の式として印字", "s : `日本語 ab`\ns\n"),
    ("長さは文字の数(バイトの数ではない)", "s : `日本語`\n||s||\n"),
    ("要素の取り出し(文字)", "s : `日本語`\ns ' 1\n"),
    ("末尾の切り出し", "s : `日本語`\ns ' 1~\n"),
    ("文字の字面(U+3042)", "0u3042\n"),
    ("Char + Int が ASCII の外へ出る", "0u3042 + 1\n"),
    ("Char - Int", "0u3042 - 2\n"),
    ("Char + Char(符号位置の和)", "0u3042 + 0u0001\n"),
    ("Char − Char は Int", "0u3044 - 0u3042\n"),
    ("U+10FFFF の上は __", "0u10FFFF + 1\n"),
    ("サロゲートに入る手前は文字", "0uD7FF + 0\n"),
    ("サロゲートは __", "0uD7FF + 1\n"),
    ("4 バイト目の文字(U+1F600)", "0u1F600\n"),
    ("連結(日本語・ASCII・数)", "mk : n ? `数` (0u3042 + n) `は` n\nmk 2\n"),
    ("文字列を関数へ渡して数える", "cnt : s i ?\n\ti >= ||s|| : 0\n\t((s ' i) = 0u3042) : 1 + (cnt s (i + 1))\n\tcnt s (i + 1)\ncnt `あいあうあ` 0\n"),
    ("累積で文字列を作る", "f : s i acc ?\n\ti >= ||s|| : acc\n\tf s (i + 1) (acc (s ' i) 0u3044)\nf `あう` 0 `x`\n"),
    ("Char * Int(定数回)", "0u3042 * 3\n"),
]:
    try: _a = _asm_u32(_src)
    except sign_asm.AsmError as _e: check("段75: " + _nm, "refused: %s" % _e, "ok"); continue
    check("段75: " + _nm + ": 答えが処理系と一致", run_asm(_a, linux=True)[1], _want_u32(_src))
check("段75: 既定の ascii では U+0080 以上の文字列は断る", refuses("s : `日本語`\ns\n"), True)
def _refuses_u32(src):
    try: _asm_u32(src)
    except sign_asm.AsmError: return True
    return False
check("段75: utf32 でもサロゲートの字面は断る", _refuses_u32("0uD800\n"), True)

print("\n全部 ok" if not fails else "\n失敗 %d 件" % fails)
sys.exit(1 if fails else 0)
