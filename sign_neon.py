#!/usr/bin/env python3
"""sign_neon.py — NEON Sign(試作): Vector(4 レーンの Float)の算術だけの関数を、AArch64 の NEON 命令で出す。

範囲(DESIGN_NEON.md 段 1 の最小):
  - 関数の本体が `+ - * /`・括弧・仮引数・Float の字面・Vector の字面 `[a b c d]` だけ。
  - 最後の式が、その関数を Vector / Float の字面で呼ぶ形(`f [1.0 2.0 3.0 4.0] 0.5`)、
    またはそれに `' k`(レーンの読み)が付いた形。
  - 仮引数の型(Vector か Float か)は、その呼びの実引数で決める(Sign の仮引数に型は無いので、呼びで決まる)。
値の持ち方: Vector = v レジスタ 1 本(4 × binary32。`--check-f32` と同じ丸め)、Float = d レジスタ(binary64)。
  Float と Vector を混ぜる所は、Float を binary32 に丸めて全レーンへ撒く(処理系の規則)。
出せない形(% ^ ・比較・関数の入れ子の呼び・Int との混在)は NeonError で断る。静かに違う答えを出さない。
`scalar=True` は比べるための基準: 同じ式を NEON を使わず、レーンごとの s レジスタの命令で出す。"""
import struct

class NeonError(Exception): pass

OPS = {"+": "fadd", "-": "fsub", "*": "fmul", "/": "fdiv"}

def f32(x):
    try: return struct.unpack("<f", struct.pack("<f", x))[0]
    except OverflowError: return float("inf") if x > 0 else float("-inf")

def _fv(n):
    """Float の字面(負は ('neg', 字面))の値。Float の字面でなければ None。"""
    if n[0] == "lit" and isinstance(n[1], float): return n[1]
    if n[0] == "neg" and len(n) == 2 and n[1][0] == "lit" and isinstance(n[1][1], float): return -n[1][1]
    return None

def _is_vec_lit(n):
    return n[0] == "block" and len(n) == 2 and n[1][0] == "seq" and len(n[1][1]) == 4 and all(_fv(e) is not None for e in n[1][1])

def _is_float_lit(n): return _fv(n) is not None

def _list_lit(n):
    """Float の字面の List(2 つ以上、4 つちょうどは Vector)の値。そうでなければ None。"""
    n = n if n[0] == "block" else _strip(n)
    if n[0] == "block" and len(n) == 2 and n[1][0] == "seq":
        vs = [_fv(e) for e in n[1][1]]
        if len(vs) >= 2 and len(vs) != 4 and all(v is not None for v in vs): return vs
    return None

def _strip(n):
    while n[0] == "block" and len(n) == 2 and not _is_vec_lit(n): n = n[1]
    return n

def flag_of(x):
    """値の `__` の旗(0 / 1 の入った x レジスタの番号)。`__` にならない値は None。"""
    return x[2] if len(x) > 2 else None

class Gen:
    def __init__(self, nodes, scalar=False, target="bare"):
        self.scalar = scalar; self.target = target
        self.defs = {}; self.defnodes = {}; main = None
        for n in nodes:
            if n[0] == "def":
                self.defnodes[n[1]] = n
                if n[2][0] == "lam": self.defs[n[1]] = n[2]
            else:
                if main is not None: raise NeonError("最後の式が 2 つ以上あります")
                main = n
        if main is None: raise NeonError("最後の式がありません")
        self.main = main
        self.data = []; self.lines = []; self.nlab = 0; self.nk = 0; self.nflag = 0; self.consts = {}

    # ---- 型(V / F) ----
    def ty(self, n, env):
        n = _strip(n) if not _is_vec_lit(n) else n
        if _is_vec_lit(n): return "V"
        if _is_float_lit(n): return "F"
        if n[0] == "lit" and isinstance(n[1], int): return "I"
        if n[0] == "id" and n[1] in env: return env[n[1]]
        if n[0] == "bin" and n[1] == "'" and len(n) == 4 and n[3][0] == "lit" and isinstance(n[3][1], int) and 0 <= n[3][1] < 4:
            if self.ty(n[2], env) != "V": raise NeonError("`' k` は Vector にだけ付けられます")
            return "F"
        if n[0] == "bin" and n[1] in OPS and len(n) == 4:
            a, b = self.ty(n[2], env), self.ty(n[3], env)
            if a == "I" and b == "I": raise NeonError("Int どうしの演算は NEON の関数の中では出せません(Int は Float か Vector と混ぜる所でだけ使えます。Int の計算は Int の関数で)")
            return "V" if "V" in (a, b) else "F"
        raise NeonError("NEON で出せない形です: %r" % (n[:2],))

    def lit_label(self, kind, vals):
        key = (kind, tuple(vals))
        for lab, k, v in self.data:
            if (k, tuple(v)) == key: return lab
        self.nlab += 1; lab = ".LN%d" % self.nlab; self.data.append((lab, kind, list(vals))); return lab

    def emit(self, s, c=""): self.lines.append("\t" + s + (("\t// " + c) if c else ""))

    # ---- 式 ----
    # 値の置き場: ("V", 'v16') / ("F", 'd16') / scalar モードの V は ("V4", ['s16','s17','s18','s19'])
    def alloc(self):
        r = self.nreg; self.nreg += 1
        if r > (23 if self.scalar else (7 if self.consts else 15)): raise NeonError("式が深すぎます(レジスタが足りません)")
        return 16 + r if r < 16 else r - 8          # 基準(scalar)だけ v8〜v15 も使う(使えば本物は退避が要るので、基準に有利な見積もり)

    def expr(self, n, env):
        n = _strip(n) if not _is_vec_lit(n) else n
        if _is_vec_lit(n):
            vals = [f32(_fv(e)) for e in n[1][1]]; lab = self.lit_label("float", vals); r = self.alloc()
            self.emit("adrp x9, %s" % lab); self.emit("add x9, x9, :lo12:%s" % lab)
            if self.scalar:
                regs = []
                for k in range(4):
                    rr = self.alloc() if k else r
                    self.emit("ldr s%d, [x9, #%d]" % (rr, 4 * k)); regs.append("s%d" % rr)
                return ("V4", regs)
            self.emit("ldr q%d, [x9]" % r, "Vector の字面"); return ("V", "v%d" % r)
        if _is_float_lit(n) and _fv(n) in self.consts: return ("F", "d%d" % self.consts[_fv(n)])
        if _is_float_lit(n):
            lab = self.lit_label("double", [_fv(n)]); r = self.alloc()
            self.emit("adrp x9, %s" % lab); self.emit("add x9, x9, :lo12:%s" % lab); self.emit("ldr d%d, [x9]" % r, "Float の字面")
            return ("F", "d%d" % r)
        if n[0] == "lit" and isinstance(n[1], int):
            if abs(n[1]) >= 1 << 53: raise NeonError("Int の字面 %d は Float で正確に表せません" % n[1])
            return self.expr(("lit", float(n[1])), env)
        if n[0] == "id":
            x = env[n[1]]
            if x[0] == "I":
                r = self.alloc(); self.emit("scvtf d%d, %s" % (r, x[1]), "Int を Float へ(昇格)"); return ("F", "d%d" % r)
            return x
        if n[0] != "bin" or len(n) != 4 or (n[1] not in OPS and n[1] != "'"):
            raise NeonError("NEON で出せない形です: %r" % (n[:2],))
        if n[1] == "'":
            if self.ty(n[2], self.tenv) != "V" or n[3][0] != "lit" or not isinstance(n[3][1], int) or not 0 <= n[3][1] < 4:
                raise NeonError("`' k` は Vector と 0〜3 の字面だけです")
            x = self.expr(n[2], env); r = self.alloc()
            if x[0] == "V4": self.emit("fcvt d%d, %s" % (r, x[1][n[3][1]]))
            else:
                self.emit("mov s%d, %s.s[%d]" % (r, x[1], n[3][1]), "レーンを読む"); self.emit("fcvt d%d, s%d" % (r, r), "32 ビットの値をそのまま 64 ビットで表す")
            return ("F", "d%d" % r, flag_of(x))                      # `__` のレーンは `__`(旗をそのまま渡す)
        a = self.expr(n[2], env); b = self.expr(n[3], env); op = OPS[n[1]]
        fa, fb = flag_of(a), flag_of(b)
        if (fa or fb) and a[0] != b[0]:
            raise NeonError("`__` になりうる値と型の違う値(Vector と Float)の演算は出せません(`__` は相手の値をそのまま答えにするので、結果の型が実行時に決まる)")
        fd = None
        if a[0] == "F" and b[0] == "F":
            r = self.alloc(); self.emit("%s d%d, %s, %s" % (op, r, a[1], b[1])); res = ("F", "d%d" % r)
        else:
            a, b = self.splat(a), self.splat(b)
            if self.scalar:
                if n[1] == "/": raise NeonError("基準(scalar)の割り算は出しません")
                out = []
                for k in range(4):
                    r = self.alloc(); self.emit("%s s%d, %s, %s" % (op, r, a[1][k], b[1][k])); out.append("s%d" % r)
                return ("V4", out)
            r = self.alloc(); self.emit("%s v%d.4s, %s.4s, %s.4s" % (op, r, a[1], b[1])); res = ("V", "v%d" % r)
            if n[1] == "/":
                d = _strip(n[3])
                if d[0] == "lit" and isinstance(d[1], int) and d[1] != 0: d = ("lit", float(d[1]))
                if not (_is_float_lit(d) and f32(_fv(d)) != 0.0):          # 0 でない字面で割るなら `__` は出ない。そうでなければ、割る数のどれかのレーンが 0 なら全体が `__`
                    t = self.alloc(); fd = self.falloc()
                    self.emit("fcmeq v%d.4s, %s.4s, #0.0" % (t, b[1]), "割る数の 0 のレーン"); self.emit("umaxv s%d, v%d.4s" % (t, t))
                    self.emit("fmov w%d, s%d" % (fd, t)); self.emit("lsr w%d, w%d, #31" % (fd, fd), "0 のレーンがあれば 1(全体が `__`)")
        if not (fa or fb or fd): return res
        # `__` の持ち回り(処理系の規則): 片方が `__` なら答えはもう片方の値そのまま、両方 `__` なら `__`。割る数に 0 のレーンがあれば `__`。
        fr = self.falloc(); mv = (lambda x: "mov v%s.16b, v%s.16b" % (res[1][1:], x[1][1:])) if res[0] == "V" else (lambda x: "fmov d%s, d%s" % (res[1][1:], x[1][1:]))
        self.emit("mov w%d, %s" % (fr, "w%d" % fd if fd else "wzr"), "旗: 割り算の `__`")
        if fb:
            L = self.klabel(); self.emit("cbz w%d, %s" % (fb, L)); self.emit(mv(a), "右が `__` なら左そのまま"); self.emit("mov w%d, wzr" % fr); self.lines.append(L + ":")
        if fa:
            L = self.klabel(); self.emit("cbz w%d, %s" % (fa, L)); self.emit(mv(b), "左が `__` なら右そのまま"); self.emit("mov w%d, %s" % (fr, "w%d" % fb if fb else "wzr")); self.lines.append(L + ":")
        return res + (fr,)

    def falloc(self):
        r = self.nflag; self.nflag += 1
        if r > 6: raise NeonError("`__` の旗のレジスタが足りません")
        return 11 + r

    def klabel(self):
        self.nk += 1; return ".LK%d" % self.nk

    def splat(self, x):
        """Float は binary32 に丸めて全レーンへ撒く。"""
        if x[0] in ("V", "V4"): return x
        r = self.alloc(); self.emit("fcvt s%d, %s" % (r, x[1]), "binary32 に丸める")
        if self.scalar: return ("V4", ["s%d" % r] * 4)
        self.emit("dup v%d.4s, v%d.s[0]" % (r, r), "全レーンへ撒く"); return ("V", "v%d" % r)

    # ---- 関数と入口 ----
    def spec(self, name, sig):
        if name not in self.defs: raise NeonError("定義の無い関数 %s" % name)
        params = self.defs[name][1]; body = self.defs[name][2]
        if len(params) != len(sig): raise NeonError("%s の引数の数が合いません" % name)
        if len(sig) > 8: raise NeonError("引数が 8 個を超えます")
        mangled = "_neon_%s_%s" % (name, "".join(sig)); self.nreg = 0; self.nflag = 0
        env = {}; self.tenv = {p[1]: t for p, t in zip(params, sig)}; self.lines.append("%s:" % mangled)
        ni = nf = 0
        if sig == ["L"] and params[0][0] == "name":
            if self.map_shape(body, params[0][1]) is not None: self.map_kernel(name, params[0][1], body); self.mapfn = mangled
            else: self.fold_kernel(name, params[0][1], body)
            self.may_void = False; return mangled
        for p, t in zip(params, sig):
            if p[0] != "name": raise NeonError("仮引数の形が出せません")
            if t == "L": raise NeonError("List(Float) は `[op] (map $g xs)` の形の関数の引数としてだけ出せます")
            if t == "I":
                env[p[1]] = ("I", "x%d" % ni); ni += 1; continue
            i = nf; nf += 1
            if self.scalar and t == "V":
                regs = []
                for k in range(4):
                    r = self.alloc(); self.emit("mov s%d, v%d.s[%d]" % (r, i, k)); regs.append("s%d" % r)
                env[p[1]] = ("V4", regs)
            else: env[p[1]] = ("V", "v%d" % i) if t == "V" else ("F", "d%d" % i)
        if self.ty(body, self.tenv) == "I": raise NeonError("結果が Int の関数です(NEON の道は Float / Vector を返す関数だけ。Int の関数は Int の道で)")
        res = self.expr(body, env)
        self.ret(res); self.may_void = flag_of(res) is not None; return mangled

    # ---- `[op] (map $g xs)` の融合(List(Float)): 中間の List を作らず、4 要素ずつ回す ----
    FOLD = {"+": "fadd", "-": "fsub", "*": "fmul", "/": "fdiv"}

    def fold_shape(self, body, xs):
        """本体が `[op] (m $g xs)`(m は map の形の定義)か `[op] xs`。→ (op, g(仮引数名, 本体) か None)"""
        b = _strip(body)
        if b[0] != "seq" or len(b[1]) != 2 or b[1][0][0] != "sec" or b[1][0][1] != "fold": raise NeonError("List(Float) の関数の本体は `[op] (map $g xs)` か `[op] xs` だけです")
        sec = b[1][0]; op = sec[2]
        if op not in self.FOLD or sec[3] is not None or sec[4] is not False: raise NeonError("畳みの演算は + - * / だけです")
        arg = _strip(b[1][1])
        if arg == ("id", xs): return op, None
        if arg[0] != "seq" or len(arg[1]) != 3 or arg[1][0][0] != "id" or arg[1][1][0] != "addr" or _strip(arg[1][2]) != ("id", xs):
            raise NeonError("List(Float) の関数の本体は `[op] (map $g xs)` か `[op] xs` だけです")
        import sign_fuse
        m = self.defnodes.get(arg[1][0][1])
        if m is None or not sign_fuse.map_like(m): raise NeonError("`map` は `m : f [h ~t] ? (@f h) (m f t)~` の形だけです")
        gn = _strip(arg[1][1][1])
        if gn[0] == "id":
            d = self.defs.get(gn[1])
            if d is None or len(d[1]) != 1 or d[1][0][0] != "name": raise NeonError("g は引数 1 個の関数だけです")
            return op, (d[1][0][1], d[2])
        if gn[0] == "sec" and gn[1] == "right" and gn[2] in OPS and gn[4] is False and _is_float_lit(_strip(gn[3])) | (_strip(gn[3])[0] == "lit"):
            return op, ("x", ("bin", gn[2], ("id", "x"), gn[3]))
        if gn[0] == "lam" and len(gn[1]) == 1 and gn[1][0][0] == "name": return op, (gn[1][0][1], gn[2])
        raise NeonError("g は名前の関数・右の節 `[* 2.0]`・無名の関数だけです")

    def expr2(self, n, env):
        """`.2d`(binary64 を 2 本)で g の本体を作る。+ - * / と Float / Int の字面と仮引数だけ。"""
        n = _strip(n)
        if n[0] == "id" and n[1] in env: return env[n[1]]
        if (n[0] == "lit" and isinstance(n[1], (int, float))) or _is_float_lit(n):
            v = float(n[1]) if n[0] == "lit" else _fv(n)
            if isinstance(n[1], int) and n[0] == "lit" and abs(n[1]) >= 1 << 53: raise NeonError("Int の字面 %d は Float で正確に表せません" % n[1])
            if v in self.consts: return "v%d" % self.consts[v]
            lab = self.lit_label("double", [v, v]); r = self.alloc()
            self.emit("adrp x9, %s" % lab); self.emit("add x9, x9, :lo12:%s" % lab); self.emit("ldr q%d, [x9]" % r, "字面を 2 本に"); return "v%d" % r
        if n[0] == "bin" and n[1] in OPS and len(n) == 4:
            a = self.expr2(n[2], env); b = self.expr2(n[3], env); r = self.alloc()
            self.emit("%s v%d.2d, %s.2d, %s.2d" % (OPS[n[1]], r, a, b)); return "v%d" % r
        raise NeonError("g の本体は仮引数・字面・+ - * / だけです")

    def preload_lits(self, gb):
        """g の字面は、輪に入る前に v24〜v31 へ 2 本ずつ置く(輪の中で読み直さない)。"""
        lits = []
        def walk(n):
            if isinstance(n, tuple):
                if n[0] == "lit" and isinstance(n[1], (int, float)) and not isinstance(n[1], bool): lits.append(float(n[1]))
                elif n[0] == "neg" and len(n) == 2 and n[1][0] == "lit" and isinstance(n[1][1], (int, float)): lits.append(-float(n[1][1]))
                else:
                    for x in n: walk(x)
            elif isinstance(n, list):
                for x in n: walk(x)
        walk(gb); uniq = []
        for v in lits:
            if v not in uniq: uniq.append(v)
        if len(uniq) > 8: raise NeonError("g の字面が 8 種類を超えます")
        for i, v in enumerate(uniq):
            lab = self.lit_label("double", [v, v]); self.emit("adrp x9, %s" % lab); self.emit("add x9, x9, :lo12:%s" % lab); self.emit("ldr q%d, [x9]" % (24 + i), "字面 %r を 2 本に" % v)
            self.consts[v] = 24 + i

    def map_shape(self, body, xs):
        """本体が `m $g xs`(m は map の形の定義)なら g を返す(`fold_shape` の g と同じ形: (仮引数名, 本体))。そうでなければ None。"""
        b = _strip(body)
        if b[0] != "seq" or len(b[1]) != 3 or b[1][0][0] != "id" or b[1][1][0] != "addr" or _strip(b[1][2]) != ("id", xs): return None
        import sign_fuse
        m = self.defnodes.get(b[1][0][1])
        if m is None or not sign_fuse.map_like(m): return None
        fake = ("seq", [("sec", "fold", "+", None, False), b])            # g の取り出しは fold_shape に任せる(畳みの演算は使わない)
        return self.fold_shape(fake, xs)[1]

    def map_kernel(self, name, xs, body):
        """`m $g xs`(結果は Float の List): x0 = 先頭の番地、x1 = 長さ(2 以上)、x2 = 書く先の番地(長さ分の double)。g だけを 4 つずつ(2 本 × 2 レーン)並べて計算して書く。
        1 要素ずつの端数は、スカラーで同じ式。x0 = `__` の旗(なし)。"""
        g = self.map_shape(body, xs)
        if g is None: raise NeonError("List(Float) の関数の本体は `[op] (map $g xs)`・`[op] xs`・`map $g xs` だけです")
        gp, gb = g
        if self.ty(gb, {gp: "F"}) != "F": raise NeonError("g の結果は Float だけです")
        env1 = {gp: ("F", "d1")}
        self.preload_lits(gb)
        L1, L2, L3 = self.klabel(), self.klabel(), self.klabel()
        self.emit("mov x3, #0", "次の番号")
        if not self.scalar:
            self.lines.append(L1 + ":"); self.emit("add x4, x3, #4"); self.emit("cmp x4, x1"); self.emit("b.hi %s" % L2)
            self.emit("add x5, x0, x3, lsl #3"); self.emit("ldp q1, q2, [x5]", "4 つ(2 本 × 2 レーン)")
            self.nreg = 0
            a = self.expr2(gb, {gp: "v1"}); b = self.expr2(gb, {gp: "v2"})
            self.emit("add x6, x2, x3, lsl #3"); self.emit("stp q%s, q%s, [x6]" % (a[1:], b[1:]), "4 つ書く")
            self.emit("mov x3, x4"); self.emit("b %s" % L1)
        self.lines.append(L2 + ":"); self.emit("cmp x3, x1"); self.emit("b.hs %s" % L3)
        self.emit("ldr d1, [x0, x3, lsl #3]"); self.nreg = 0; self.emit("fmov d4, %s" % self.expr(gb, env1)[1]); self.emit("str d4, [x2, x3, lsl #3]")
        self.emit("add x3, x3, #1"); self.emit("b %s" % L2)
        self.lines.append(L3 + ":"); self.emit("mov x0, #0", "x0 = `__` の旗(なし)"); self.emit("ret"); self.consts = {}

    def fold_kernel(self, name, xs, body):
        """x0 = 先頭の番地、x1 = 長さ(1 以上)。d0 = 答え(Float)。先頭の 1 つを 1 つずつ、あとを 4 つずつ(2 本 × 2 レーン)、残りを 1 つずつ。
        畳みは左から 1 つずつ(足し算の順は変えない: 処理系と同じ丸めになる)。map の部分(g)だけを並べて計算する。"""
        op, g = self.fold_shape(body, xs); fo = self.FOLD[op]
        if g is not None:
            gp, gb = g
            if self.ty(gb, {gp: "F"}) != "F": raise NeonError("g の結果は Float だけです")
            env1 = {gp: ("F", "d1")}
        if g is not None: self.preload_lits(gb)
        def scalar_g():
            self.nreg = 0
            if g is None: return "d1"
            return self.expr(gb, env1)[1]
        L1, L2, L3 = self.klabel(), self.klabel(), self.klabel()
        self.emit("ldr d1, [x0]", "先頭の 1 つ"); self.emit("fmov d0, %s" % scalar_g(), "答えの初めの値"); self.emit("mov x2, #1", "次の番号")
        if not self.scalar:
            self.lines.append(L1 + ":"); self.emit("add x3, x2, #4"); self.emit("cmp x3, x1"); self.emit("b.hi %s" % L2)
            self.emit("add x4, x0, x2, lsl #3"); self.emit("ldp q1, q2, [x4]", "4 つ(2 本 × 2 レーン)")
            self.nreg = 0
            if g is None: a, b = "v1", "v2"
            else: a = self.expr2(gb, {gp: "v1"}); b = self.expr2(gb, {gp: "v2"})
            for v in (a, b):
                self.emit("%s d0, d0, d%s" % (fo, v[1:]), "左から 1 つずつ畳む"); self.emit("mov d3, %s.d[1]" % v); self.emit("%s d0, d0, d3" % fo)
            self.emit("mov x2, x3"); self.emit("b %s" % L1)
        self.lines.append(L2 + ":"); self.emit("cmp x2, x1"); self.emit("b.hs %s" % L3)
        self.emit("ldr d1, [x0, x2, lsl #3]"); self.emit("fmov d4, %s" % scalar_g()); self.emit("%s d0, d0, d4" % fo)
        self.emit("add x2, x2, #1"); self.emit("b %s" % L2)
        self.lines.append(L3 + ":"); self.emit("mov x0, #0", "x0 = `__` の旗(なし)"); self.emit("ret"); self.consts = {}

    def ret(self, res):
        if res[0] == "V": self.emit("mov v0.16b, %s.16b" % res[1])
        elif res[0] == "V4":
            for k in range(4): self.emit("mov v0.s[%d], v%s.s[0]" % (k, res[1][k][1:]))
        else: self.emit("fmov d0, %s" % res[1])
        f = flag_of(res)
        self.emit("mov w0, w%d" % f if f else "mov x0, #0", "x0 = `__` の旗(1 なら結果は `__`)")
        self.emit("ret")

    def int_part(self, int_args):
        """Int の実引数(式)を、Int の道(sign_asm)で作る。_neon_ints : d ? (式1) (式2) … 0 という関数を作り、
        返った並びの要素を x レジスタへ読む。Int の関数の定義は、式から届く物だけを持ち込む。"""
        import sign_asm
        need, todo = [], list(int_args)
        def walk(n):
            if isinstance(n, tuple):
                if len(n) == 2 and n[0] == "id" and n[1] in self.defnodes and n[1] not in need: need.append(n[1]); walk(self.defnodes[n[1]])
                for x in n: walk(x)
            elif isinstance(n, list):
                for x in n: walk(x)
        for a in int_args: walk(a)
        nodes = [self.defnodes[k] for k in need]
        if has_float(nodes) or has_float(int_args): raise NeonError("Int の実引数が Float を使っています(Int の関数は Float を持てません)")
        nodes.append(("def", "_neon_ints", ("lam", [("name", "_d", None)], ("seq", list(int_args) + [("lit", 0)]))))
        nodes.append(("seq", [("id", "_neon_ints"), ("lit", 0)]))
        try: text = sign_asm.generate(nodes, target="bare")
        except sign_asm.AsmError as e: raise NeonError("Int の実引数: %s" % e)
        if "\n_neon_ints:" not in text: raise NeonError("Int の実引数の関数が残りませんでした(最適化で消えた)")
        return text.replace("_.main", "_.main_int")

    def generate(self):
        m = _strip(self.main); lane = None
        if m[0] == "bin" and m[1] == "'" and len(m) == 4 and m[3][0] == "lit" and isinstance(m[3][1], int) and 0 <= m[3][1] < 4:
            lane = m[3][1]; m = _strip(m[2])
        if m[0] != "seq" or m[1][0][0] != "id": raise NeonError("最後の式は `f 実引数…` の形だけです")
        name, args = m[1][0][1], m[1][1:]
        sig = []; int_args = []
        for a in args:
            a2 = a if _is_vec_lit(a) else _strip(a)
            if _list_lit(a) is not None: sig.append("L")
            elif _is_vec_lit(a2): sig.append("V")
            elif _is_float_lit(a2): sig.append("F")
            elif has_float(a): raise NeonError("実引数は Vector か Float の字面か、Int の式だけです(Float の式は出せません)")
            else: sig.append("I"); int_args.append(a)
        fn = self.spec(name, sig)
        int_text = self.int_part(int_args) if int_args else ""
        self.lines.append("\t.globl _.main\n_.main:")
        self.emit("stp x29, x30, [sp, #-16]!"); self.emit("mov x29, sp")
        if int_args:
            k = len(int_args) + 1; self.emit("sub sp, sp, #%d" % (16 * ((8 * k + 15) // 16)), "Int の実引数の並びの置き場")
            self.emit("mov x8, sp"); self.emit("mov x15, #%d" % k); self.emit("mov x0, #0"); self.emit("bl _neon_ints"); self.emit("mov x10, x0")
        ni = nf = ji = 0
        for i, a in enumerate(args):
            a = a if _is_vec_lit(a) else _strip(a)
            if sig[i] == "L":
                vs = _list_lit(args[i]); lab = self.lit_label("double", vs)
                self.emit("adrp x%d, %s" % (ni, lab)); self.emit("add x%d, x%d, :lo12:%s" % (ni, ni, lab)); self.emit("mov x%d, #%d" % (ni + 1, len(vs)), "List(Float) の字面(ポインタと長さ)"); ni += 2
            elif sig[i] == "I":
                self.emit("ldr x%d, [x10, #%d]" % (ni, 8 * ji), "Int の実引数 %d" % ji); ni += 1; ji += 1
            elif sig[i] == "V":
                lab = self.lit_label("float", [f32(_fv(e)) for e in a[1][1]])
                self.emit("adrp x9, %s" % lab); self.emit("add x9, x9, :lo12:%s" % lab); self.emit("ldr q%d, [x9]" % nf); nf += 1
            else:
                lab = self.lit_label("double", [_fv(a)])
                self.emit("adrp x9, %s" % lab); self.emit("add x9, x9, :lo12:%s" % lab); self.emit("ldr d%d, [x9]" % nf); nf += 1
        if sig == ["L"] and lane is None and sig_result(self, name, sig) == "M":
            self.mlen = len(_list_lit(args[0])); self.emit("adrp x2, _neon_out"); self.emit("add x2, x2, :lo12:_neon_out", "書く先(Float の List の結果)")
        self.emit("bl %s" % fn)
        if lane is not None:
            if sig_result(self, name, sig) != "V": raise NeonError("`' k` は Vector にだけ付けられます")
            self.emit("mov s0, v0.s[%d]" % lane); self.emit("fcvt d0, s0", "レーンは 32 ビットの値をそのまま 64 ビットで表す")
        if int_args: self.emit("mov sp, x29", "置き場を捨てる")
        self.emit("ldp x29, x30, [sp], #16"); self.emit("ret")
        kind = "F" if lane is not None else sig_result(self, name, sig)
        if kind == "M" and self.target != "linux": raise NeonError("Float の List を返す関数は --target=linux だけで出せます(bare では結果の置き場の約束がありません)")
        rkind = kind
        if kind == "M" and self.mlen > 64: raise NeonError("Float の List の結果は 64 要素までです")
        if kind == "I": raise NeonError("結果が Int の関数です(NEON の道は Float / Vector を返す関数だけ。Int の関数は Int の道で)")
        out = ["\t.text"] + self.lines
        if self.target == "linux": out += self.start(kind).splitlines()
        out.append("\t.section .rodata\n\t.balign 16")
        for lab, kind, vals in self.data:
            out.append("%s:" % lab)
            if kind == "float": out.append("\t.float " + ", ".join(repr(v) if v == v and abs(v) != float("inf") else "0" for v in vals))
            else: out.append("\t.double " + ", ".join(repr(v) for v in vals))
        if rkind == "M": out += ["\t.section .bss", "\t.balign 16", "_neon_out:", "\t.skip %d" % (8 * self.mlen), "\t.text"]
        text = "\n".join(out) + "\n"
        if int_text: text = int_text + "\n" + text
        if self.target == "linux":
            import sign_fmt
            text = text.replace("\t.section .rodata", sign_fmt.routine() + "\t.section .rodata", 1) + sign_fmt.data()
        return text

    def start(self, kind):
        """--target=linux の入口: 結果(v0 = Vector / d0 = Float)を処理系と同じ綴りで書いて exit(0)。Vector は binary32 の最短、Float は binary64 の最短。"""
        L = ["\t.globl _start", "_start:", "\tbl _.main"]
        if getattr(self, "may_void", False):                                   # x0 = 1 なら結果は `__`
            L += ["\tcbz x0, .LKv", "\tsub sp, sp, #16", "\tmov w3, #95", "\tstrb w3, [sp]", "\tstrb w3, [sp, #1]", "\tmov w3, #10", "\tstrb w3, [sp, #2]",
                  "\tmov x0, #1", "\tmov x1, sp", "\tmov x2, #3", "\tmov x8, #64", "\tsvc #0", "\tmov x0, #0", "\tmov x8, #93", "\tsvc #0", ".LKv:"]
        L += ["\tsub sp, sp, #%d" % (16 * ((26 * getattr(self, "mlen", 0) + 270) // 16)) if kind == "M" else "\tsub sp, sp, #256", "\tmov x21, sp"]
        def ch(c): L.extend(["\tmov w3, #%d" % ord(c), "\tstrb w3, [x21]", "\tadd x21, x21, #1"])
        def num(mode): L.extend(["\tmov x1, #%d" % mode, "\tmov x2, x21", "\tbl _sign_fmt_float", "\tadd x21, x21, x0"])
        if kind == "M":
            L += ["\tadrp x22, _neon_out", "\tadd x22, x22, :lo12:_neon_out"]; ch("[")
            for k in range(self.mlen):
                L.append("\tldr x0, [x22, #%d]" % (8 * k)); num(0)
                if k < self.mlen - 1: ch(","); ch(" ")
            ch("]")
        elif kind == "V":
            L.append("\tstr q0, [sp, #192]"); ch("[")
            for k in range(4):
                L.append("\tldr w0, [sp, #%d]" % (192 + 4 * k)); num(1)
                if k < 3: ch(" ")
            ch("]")
        else:
            L.append("\tfmov x0, d0"); num(0)
        ch("\n")
        L.extend(["\tmov x0, #1", "\tmov x1, sp", "\tsub x2, x21, x1", "\tmov x8, #64", "\tsvc #0", "\tmov x0, #0", "\tmov x8, #93", "\tsvc #0"])
        return "\n".join(L) + "\n"

def sig_result(g, name, sig):
    if sig == ["L"]: return "M" if g.map_shape(g.defs[name][2], g.defs[name][1][0][1]) is not None else "F"      # `[op] (map $g xs)` の答えは Float、`map $g xs` は Float の List
    env = {p[1]: t for p, t in zip(g.defs[name][1], sig)}
    return g.ty(g.defs[name][2], env)

def generate(nodes, scalar=False, target="bare"): return Gen(nodes, scalar, target).generate()

def has_float(n):
    """構文木のどこかに Float の字面があるか(あれば NEON の道へ回す)。"""
    if isinstance(n, float): return True
    if isinstance(n, (tuple, list)): return any(has_float(x) for x in n)
    return False

if __name__ == "__main__":
    import sys, sign_interp
    nodes = sign_interp.parse_source(open(sys.argv[1], encoding="utf-8").read(), sys.argv[1])
    print(generate(nodes, scalar="--scalar" in sys.argv), end="")


def main_needs_float(nodes):
    """最後の式から届く定義(と最後の式)に Float の字面があるか。使われない Float の関数があるだけなら Int の道のまま。"""
    defs = {n[1]: n for n in nodes if n[0] == "def"}
    mains = [n for n in nodes if n[0] != "def"]
    seen, todo = set(), list(mains)
    while todo:
        n = todo.pop()
        if isinstance(n, float): return True
        if isinstance(n, (tuple, list)):
            if isinstance(n, tuple) and len(n) == 2 and n[0] == "id" and n[1] in defs and n[1] not in seen:
                seen.add(n[1]); todo.append(defs[n[1]])
            todo.extend(n)
    return False
