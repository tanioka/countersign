"""sign_opt.py — AArch64 の出力に対する、関数ごとの大域最適化(制御フロー解析つき)。

`sign_asm.FnGen.finish` が組み上げた 1 関数ぶんの命令列(文字)を読み直し、次をする。意味は変えない。
  1. 制御フロー解析   命令ごとの後続(b・b.cc・cbz 系・ret・罠)から、レジスタ x0〜x28・フラグ・フレームのスロットの『生きている』を
                      不動点まで解く(後ろ向きのデータフロー)。
  2. 共通部分式       前向きの『同じ値』の解析(ブロックの境では共通部分をとる)。同じ即値の作り直し・同じスロットの読み直し・
                      同じ式の再計算(乗除・シフト)を消し、コピーの先を元のレジスタに置き換える。
  3. デッドコード削除  結果がどの道でも読まれない命令(副作用の無いもの)と、読まれないスロットへの保存を消す。
  4. ループ不変式の移動 戻り辺をもつループで、毎回同じ値を作る副作用の無い命令を、ループの前へ出す。
  5. レジスタ割り付け   フレームのスロット(x29 相対)のうち、番地を取られないものを、生きている区間の干渉グラフで色分けして、
                      呼び出し先が保存する x19〜x28 に置く(ループの中で使われるほど優先)。入口で保存し、出口で戻す。
  そのあと sign_peep(窓の置き換え)にかける。
判らないものは何もしない(制御が読めない関数・x29 の番地を取る関数・知らない命令など)。
  - `bl` は x0〜x18・x30・フラグを壊し、x0〜x7・x8・x15・x17 を読む。Sign の関数は x19〜x28 を保つが、`_sign_*` の補助・`blr` は x19〜x25 も壊す
    (手書きの補助が使うため)ので、補助の呼びをまたいで生きる値は x26〜x28 にしか置かない。
  - 罠(`.Ltrap*`)は何も読まない。
環境変数 SIGN_OPT=0 で、この段だけ切れる(sign_peep は残る)。
"""
import re
import sign_peep
from sign_peep import Ins, _parse, _regs

LABEL = re.compile(r"^([A-Za-z_.][\w.$]*):\s*$")
F_BIT = 1 << 31
ALLREG = (1 << 31) - 1                      # x0〜x30
CALLER = (1 << 19) - 1 | (1 << 30)          # x0〜x18・x30
ARGS = sum(1 << i for i in (0, 1, 2, 3, 4, 5, 6, 7, 8, 15, 17))
RETUSE = (1 << 9) - 1 | (1 << 30)            # ret が読む: x0〜x8・x30
HELPER_EXTRA = sum(1 << i for i in range(19, 26))

ALU = set(sign_peep.ALU_W) | {"adc", "sbc", "adcs", "sbcs", "bics", "cneg", "csetm", "movk", "umulh", "smulh", "mneg", "umaddl"}
FLAGSET = {"adds", "subs", "negs", "ands", "bics", "adcs", "sbcs"}
FLAGUSE = {"csel", "csinc", "csinv", "csneg", "cset", "cinc", "csetm", "cneg", "adc", "sbc", "adcs", "sbcs"}
CMPS = {"cmp", "cmn", "tst"}
CCMPS = {"ccmp", "ccmn"}
EXPR = {"add", "sub", "mul", "lsl", "lsr", "asr", "and", "orr", "eor", "neg", "mvn", "sdiv", "udiv", "madd", "msub", "smulh", "umulh",
        "sxtw", "uxtw", "sxtb", "uxtb", "sxth", "uxth", "ror", "ubfx", "sbfx"}
EXPENSIVE = {"mul", "sdiv", "udiv", "madd", "msub", "smulh", "umulh", "lsl", "lsr", "asr"}
HOIST = {"mov", "add", "sub", "lsl", "lsr", "asr", "and", "orr", "eor", "neg", "mvn", "movz", "movn", "adrp", "adr", "mul", "sxtw", "uxtw", "sxtb", "uxtb"}
MEM8 = re.compile(r"^\[x29(?:, #(-?\d+))?\]$")


class Bail(Exception): pass


class It:
    __slots__ = ("k", "ins", "name", "raw", "dead", "keep")
    def __init__(self, k, ins=None, name=None, raw=None): self.k, self.ins, self.name, self.raw, self.dead, self.keep = k, ins, name, raw, False, False


def parse_items(lines):
    items = []
    for ln in lines:
        m = LABEL.match(ln)
        if m: items.append(It("l", name=m.group(1), raw=ln)); continue
        if ln.strip().startswith(".global"): items.append(It("c", raw=ln)); continue
        p = _parse(ln)
        if p == "c": items.append(It("c", raw=ln))
        elif p is None: raise Bail("raw: " + ln)
        else: items.append(It("i", ins=p, raw=ln))
    return items


def alive(items): return [it for it in items if not it.dead]


class Fn:
    """解析の対象: 項目(命令・ラベル・コメント)の並びと、枠の様子。"""
    def __init__(self, lines):
        self.items = parse_items(lines)
        self.F = None
        self.cand = set()
        self.scan_frame()

    # ---- フレームのスロット ----
    def scan_frame(self):
        F = None; acc = {}; bad = set(); rets = 0; ldps = 0; escaped = False
        for it in self.items:
            if it.k != "i": continue
            i = it.ins; mn, ops = i.mn, i.ops
            if mn == "stp" and ops[:2] == ["x29", "x30"] and len(ops) == 3 and ops[2].startswith("[sp, #-") and ops[2].endswith("]!"):
                f = int(ops[2][len("[sp, #-"):-2])
                if F is not None and F != f: raise Bail("枠が食い違う")
                F = f; continue
            if mn == "ldp" and ops[:2] == ["x29", "x30"] and len(ops) == 4 and ops[2] == "[sp]": ldps += 1; continue
            if mn == "ret": rets += 1; continue
            if mn == "mov" and ops == ["x29", "sp"]: continue
            if mn == "mov" and ops == ["sp", "x29"]: continue
            if not any(("x29" in o) for o in ops): continue
            if mn == "bl" or mn.startswith("b"): continue
            mem = [o for o in ops if o.startswith("[")]
            others = [o for o in ops if not o.startswith("[")]
            if any(re.search(r"\bx29\b", o) for o in others): escaped = True; continue          # 番地を取る(--par の仕事の置き場など): スロットは割り付け・削除の対象にしない
            if len(mem) != 1: raise Bail("x29 の使い方が読めない: " + i.text())
            m = MEM8.match(mem[0])
            if not m:
                if re.search(r"\bx29\b", mem[0]): raise Bail("x29 の番地の形: " + mem[0])
                continue
            k = int(m.group(1) or 0)
            w = None
            if mn in ("ldr", "str") and re.fullmatch(r"(x\d+|xzr)", ops[0]): w = 8
            elif mn in ("ldrb", "strb", "ldurb", "sturb", "ldrsb"): w = 1
            elif mn in ("ldrh", "strh", "ldrsh", "ldurh", "sturh"): w = 2
            elif mn in ("ldr", "str", "ldrsw") and ops[0].startswith("w"): w = 4
            elif mn in ("ldp", "stp"): w = 16 if ops[0].startswith("x") else 8
            else: raise Bail("x29 相対の命令が読めない: " + i.text())
            if w == 8 and ops[0] != "xzr" and not re.fullmatch(r"x\d+", ops[0]): raise Bail("?")
            acc.setdefault(k, set()).add(w)
            if w != 8: bad.update(range(k, k + w))
        self.F = F; self.rets = rets; self.ldps = ldps
        cand = set()
        if F is not None:
            for k, ws in acc.items():
                if ws == {8} and 16 <= k < F and k % 8 == 0 and not any(b in bad for b in range(k, k + 8)): cand.add(k)
        if escaped: cand = set()
        self.cand = cand; self.escaped = escaped
        self.stackargs = {k for k in acc if F is not None and k >= F}

    def slot_of(self, i):
        """x29 相対の 8 バイトの読み書きなら ('ld'|'st', k)。"""
        if i.mn in ("ldr", "str") and len(i.ops) == 2:
            m = MEM8.match(i.ops[1])
            if m and re.fullmatch(r"(x\d+|xzr)", i.ops[0]):
                k = int(m.group(1) or 0)
                if k in self.cand: return ("ld" if i.mn == "ldr" else "st", k)
        return None


# ---- 命令の効果 ----
def regbits(o):
    b = 0
    for _, n in _regs(o): b |= 1 << n
    return b


class Eff:
    __slots__ = ("use", "defs", "rm", "call", "slot", "unk", "br", "tgt", "uncond", "term")
    def __init__(self): self.use = 0; self.defs = 0; self.rm = False; self.call = None; self.slot = None; self.unk = False; self.br = None; self.tgt = None; self.uncond = False; self.term = False


def effect(fn, i, slotbit, wbit=None):
    e = Eff(); mn, ops = i.mn, i.ops
    if mn == "stp" and ops[:2] == ["x29", "x30"] and len(ops) == 3 and ops[2].startswith("[sp"): e.use = (1 << 29) | (1 << 30); return e
    if mn == "ldp" and ops[:2] == ["x29", "x30"] and len(ops) == 4: e.defs = (1 << 29) | (1 << 30); return e
    if mn == "ret": e.use = RETUSE; e.term = True; e.uncond = True; return e
    if mn == "b" and len(ops) == 1: e.br = "b"; e.tgt = ops[0]; e.uncond = True; return e
    if mn.startswith("b.") and len(ops) == 1: e.br = "bc"; e.tgt = ops[0]; e.use = F_BIT; return e
    if mn in ("cbz", "cbnz") and len(ops) == 2: e.br = "bc"; e.tgt = ops[1]; e.use = regbits(ops[0]); return e
    if mn in ("tbz", "tbnz") and len(ops) == 3: e.br = "bc"; e.tgt = ops[2]; e.use = regbits(ops[0]); return e
    if mn == "bl" and len(ops) == 1:
        sign = not ops[0].startswith(("_sign_", "_.", "."))
        e.call = "sign" if sign else "help"
        e.use = ARGS if sign else ALLREG
        if ops[0] == "_sign_par_submit": e.use = 3                       # x0 = 入れ物, x1 = 強制(sign_asmpar.py の約束)
        elif ops[0] in ("_sign_par_join", "_sign_par_steal"): e.use = 1   # x0 = 入れ物
        e.defs = CALLER | F_BIT | (0 if sign else HELPER_EXTRA)
        return e
    if mn in ("blr", "br", "svc") or mn == "bl":
        if mn == "br": raise Bail("br")
        e.call = "help"; e.use = ALLREG; e.defs = CALLER | F_BIT | HELPER_EXTRA; return e
    sl = fn.slot_of(i)
    if sl:
        e.slot = sl
        b = wbit if wbit is not None else slotbit[sl[1]]
        if sl[0] == "ld": e.defs = regbits(ops[0]); e.use = b; e.rm = True
        else: e.use = regbits(ops[0]); e.defs = b; e.rm = True
        if sl[0] == "ld" and not (e.defs and e.defs <= (1 << 31) - 1): e.unk = True
        return e
    # 一般の命令
    if mn in ALU and ops:
        d = ops[0]
        if not re.fullmatch(r"[xw]\d+", d):
            if d in ("sp", "x29"):
                e.use = sum(regbits(o) for o in ops[1:]); e.defs = 0; e.unk = True; return e
            e.unk = True; e.use = ALLREG; return e
        e.use = 0
        for o in ops[1:]: e.use |= regbits(o)
        e.defs = regbits(d)
        if mn == "movk": e.use |= regbits(d)
        if mn in FLAGSET: e.defs |= F_BIT
        if mn in FLAGUSE: e.use |= F_BIT
        e.rm = int(d[1:]) < 29
        return e
    if mn in CMPS: e.use = sum(regbits(o) for o in ops); e.defs = F_BIT; e.rm = True; return e
    if mn in CCMPS: e.use = sum(regbits(o) for o in ops) | F_BIT; e.defs = F_BIT; e.rm = True; return e
    if mn in sign_peep.LOADS and len(ops) == 2 and ops[1].startswith("[") and re.fullmatch(r"[xw]\d+", ops[0]):
        e.use = regbits(ops[1]); e.defs = regbits(ops[0])
        e.rm = bool(re.match(r"^\[x29[,\]]", ops[1]))           # フレームの読みは副作用なし(ほかの番地の読みは残す)
        return e
    if mn in sign_peep.STORES and len(ops) == 2: e.use = sum(regbits(o) for o in ops); return e
    if mn in ("stp", "ldp") and len(ops) == 3 and ops[2].startswith("["):
        if mn == "stp": e.use = regbits(ops[0]) | regbits(ops[1]) | regbits(ops[2])
        else: e.use = regbits(ops[2]); e.defs = regbits(ops[0]) | regbits(ops[1])
        return e
    e.unk = True; e.use = ALLREG | F_BIT
    return e


class Analysis:
    def __init__(self, fn):
        self.fn = fn
        self.rebuild()

    def rebuild(self):
        fn = self.fn
        its = fn.items
        self.slots = sorted(fn.cand)
        self.slotbit = {k: 1 << (32 + n) for n, k in enumerate(self.slots)}
        self.labels = {}
        for n, it in enumerate(its):
            if it.k == "l" and not it.dead: self.labels[it.name] = n
        self.idx = [n for n, it in enumerate(its) if it.k == "i" and not it.dead]
        self.pos = {n: p for p, n in enumerate(self.idx)}
        self.eff = {n: effect(fn, its[n].ins, self.slotbit) for n in self.idx}
        self.webof = {}; self.wbit = {}; self.webslot = {}
        # 次の命令・飛び先
        self.nxt = {}
        for p, n in enumerate(self.idx): self.nxt[n] = self.idx[p + 1] if p + 1 < len(self.idx) else None
        self.first_after = {}
        for name, ln in self.labels.items():
            k = ln + 1
            while k < len(its) and (its[k].dead or its[k].k != "i"): k += 1
            self.first_after[name] = k if k < len(its) else None
        self.succ = {}
        for n in self.idx:
            e = self.eff[n]; s = []
            if e.term: pass
            elif e.br:
                t = e.tgt
                if t.startswith(".Ltrap"): pass
                elif t in self.labels:
                    if self.first_after[t] is not None: s.append(self.first_after[t])
                else: raise Bail("外への飛び先: " + t)
                if e.br == "bc" and self.nxt[n] is not None: s.append(self.nxt[n])
                if e.br == "bc" and t.startswith(".Ltrap"): pass
            elif self.nxt[n] is not None: s.append(self.nxt[n])
            self.succ[n] = s
        self.make_webs()
        self.liveness()

    def reeff(self, n):
        w = self.webof.get(n)
        self.eff[n] = effect(self.fn, self.fn.items[n].ins, self.slotbit, self.wbit[w] if w is not None else None)
        return self.eff[n]

    def make_webs(self):
        """スロットの定義(str)と使用(ldr)を、届く定義でつないだ『網』に分ける。同じスロットでも、生きている区間が別なら別の変数になる。"""
        if not self.slots: return
        idx = self.idx; eff = self.eff
        parent = {}
        def find(x):
            while parent.setdefault(x, x) != x:
                parent[x] = parent[parent[x]]; x = parent[x]
            return x
        def union(a_, b_):
            ra, rb = find(a_), find(b_)
            if ra != rb: parent[ra] = rb
        # ブロック
        leaders = {idx[0]} if idx else set()
        for n in idx:
            e = eff[n]
            if (e.br or e.term) and self.nxt[n] is not None: leaders.add(self.nxt[n])
        for name, k in self.first_after.items():
            if k is not None: leaders.add(k)
        blocks = []; blk = {}; cur = None
        for n in idx:
            if n in leaders: cur = []; blocks.append(cur)
            cur.append(n); blk[n] = len(blocks) - 1
        sb = [[] for _ in blocks]; pb = [[] for _ in blocks]
        for b, ns in enumerate(blocks):
            for t in self.succ[ns[-1]]:
                if t in blk and blk[t] not in sb[b]: sb[b].append(blk[t]); pb[blk[t]].append(b)
        entries = {0} | {blk[k] for name, k in self.first_after.items() if k is not None and not name.startswith(".L") and k in blk}
        slots = self.slots
        # 入口で届いている定義: 各スロットの ("e", k)
        out = [None] * len(blocks)             # out[b][k] = frozenset
        inn = [None] * len(blocks)
        def transfer(b, st, record):
            for n in blocks[b]:
                e = eff[n]
                if e.slot:
                    kind, k = e.slot
                    if kind == "ld":
                        if record:
                            ds = st[k]
                            first = None
                            for d_ in ds:
                                if first is None: first = d_
                                else: union(first, d_)
                            if first is None: first = ("u", n)
                            union(("l", n), first)
                    else:
                        st[k] = frozenset([("s", n)])
                        if record: union(("l", n), ("s", n))
            return st
        work = list(range(len(blocks))); inq = set(work)
        while work:
            b = work.pop(0); inq.discard(b)
            st = {}
            for k in slots:
                u = set()
                if b in entries: u.add(("e", k))
                for p in pb[b]:
                    if out[p] is not None: u |= out[p][k]
                st[k] = frozenset(u)
            inn[b] = dict(st)
            o = transfer(b, st, False)
            if out[b] != o:
                out[b] = o
                for t in sb[b]:
                    if t not in inq: work.append(t); inq.add(t)
        for b in range(len(blocks)):
            if inn[b] is not None: transfer(b, dict(inn[b]), True)
        roots = {}
        for n in idx:
            e = eff[n]
            if e.slot:
                r = find(("l", n))
                if r not in roots: roots[r] = len(roots); self.wbit[roots[r]] = 1 << (32 + roots[r]); self.webslot[roots[r]] = e.slot[1]
                self.webof[n] = roots[r]
        for n, w in self.webof.items(): self.reeff(n)

    def liveness(self):
        live_in = {n: 0 for n in self.idx}; live_out = {n: 0 for n in self.idx}
        order = list(reversed(self.idx))
        ch = True
        while ch:
            ch = False
            for n in order:
                e = self.eff[n]
                lo = 0
                for s in self.succ[n]: lo |= live_in[s]
                li = e.use | (lo & ~e.defs)
                if lo != live_out[n] or li != live_in[n]:
                    live_out[n] = lo; live_in[n] = li; ch = True
        self.live_in, self.live_out = live_in, live_out


# ---- デッドコード削除 ----
def dce(fn):
    total = 0
    while True:
        a = Analysis(fn); ch = 0
        for n in a.idx:
            e = a.eff[n]
            if e.rm and e.defs and (e.defs & a.live_out[n]) == 0 and not fn.items[n].keep:
                fn.items[n].dead = True; ch += 1
        total += ch
        if not ch: return total


# ---- 共通部分式・コピーの伝播(前向き) ----
def bits_of(mask):
    out = []; n = 0
    while mask:
        if mask & 1: out.append(n)
        mask >>= 1; n += 1
    return out


def avail(fn):
    a = Analysis(fn); its = fn.items
    idx = a.idx
    if not idx: return 0
    # 基本ブロック
    leaders = {idx[0]}
    for n in idx:
        e = a.eff[n]
        if e.br or e.term:
            if a.nxt[n] is not None: leaders.add(a.nxt[n])
    for name, k in a.first_after.items():
        if k is not None: leaders.add(k)
    blocks = []; blk_of = {}
    cur = None
    for n in idx:
        if n in leaders: cur = []; blocks.append(cur)
        cur.append(n); blk_of[n] = len(blocks) - 1
    succ_b = [[] for _ in blocks]
    for b, ns in enumerate(blocks):
        for s in a.succ[ns[-1]]:
            if s in blk_of and blk_of[s] not in succ_b[b]: succ_b[b].append(blk_of[s])
    in_st = [None] * len(blocks)
    in_st[0] = {}
    entries = {0}
    for name, k in a.first_after.items():          # `.L` で始まらないラベル(関数の入口・`.rec` の入口)は外から入れる: 何も分かっていない状態から始める
        if k is not None and not name.startswith(".L") and k in blk_of: in_st[blk_of[k]] = {}; entries.add(blk_of[k])

    def getid(st, key, n):
        if key not in st: st[key] = ("u", key, n)
        return st[key]

    def opid(st, o, n):
        o = o.strip()
        if o.startswith("#") or o.startswith(":"): return ("i", o)
        m = re.fullmatch(r"x(\d+)", o)
        if m and int(m.group(1)) < 29: return getid(st, int(m.group(1)), n)
        if o == "xzr": return ("i", "#0")
        return ("t", o)

    def transfer(st, n, rewrite):
        """命令 n を通したあとの状態を st に作る。rewrite なら (消す・置き換える) を返す。"""
        it = its[n]; i = it.ins; e = a.eff[n]; mn, ops = i.mn, i.ops
        action = None
        if e.call:
            for r in range(0, 19):
                st.pop(r, None)
            st.pop(30, None)
            if e.call == "help":
                for r in range(19, 26): st.pop(r, None)
            return None
        if e.unk:
            for r in range(0, 29): st.pop(r, None)
            return None
        if e.slot:
            kind, k = e.slot; key = ("s", k)
            reg = ops[0]
            if kind == "ld":
                d = int(reg[1:]); v = st.get(key)
                if v is None:
                    v = ("u", key, n); st[key] = v
                    st[d] = v
                    return None
                if st.get(d) == v:
                    return ("del",)
                if rewrite:
                    for r in sorted(r for r, vv in st.items() if isinstance(r, int) and vv == v and r != d and (r < 13 or r >= 19)):
                        action = ("mov", "x%d" % d, "x%d" % r); break
                st[d] = v
                return action
            else:
                if reg == "xzr": v = ("i", "#0")
                else: v = getid(st, int(reg[1:]), n)
                if st.get(key) == v: return ("del",)
                st[key] = v
                return None
        # 一般
        for r in bits_of(e.defs & ALLREG):
            if r < 29 and not (mn in ALU and ops and re.fullmatch(r"[xw]\d+", ops[0]) and int(ops[0][1:]) == r and mn in EXPR | {"mov"} and not any(re.fullmatch(r"w\d+", o) for o in ops)):
                pass
        d = None
        if mn in ALU and ops and re.fullmatch(r"x\d+", ops[0]) and int(ops[0][1:]) < 29: d = int(ops[0][1:])
        if d is not None and not (e.defs & F_BIT) and mn != "movk" and not any(re.fullmatch(r"w\d+", o) for o in ops):
            if mn == "mov" and len(ops) == 2:
                v = opid(st, ops[1], n)
                if v[0] == "t": v = ("d", n)
            elif mn in EXPR:
                v = (mn,) + tuple(opid(st, o, n) for o in ops[1:])
                if any(x[0] == "t" for x in v[1:] if isinstance(x, tuple)): v = ("d", n)
            else: v = ("d", n)
            if v[0] == "i" and False: pass
            if st.get(d) == v and v[0] != "d": return ("del",)
            if rewrite and mn in EXPENSIVE and v[0] not in ("d",):
                for r in sorted(r for r, vv in st.items() if isinstance(r, int) and vv == v and r != d and (r < 13 or r >= 19)):
                    action = ("mov", "x%d" % d, "x%d" % r); break
            # 書く先の古い値で、スロットが持っていたものは変わらない(スロットは別の鍵)
            for r in bits_of(e.defs & ALLREG):
                if r != d: st.pop(r, None)
            st[d] = v
            return action
        for r in bits_of(e.defs & ALLREG):
            if r < 29: st.pop(r, None)
        return None

    # 不動点
    work = sorted(entries); seen_iter = 0
    while work and seen_iter < 20000:
        seen_iter += 1
        b = work.pop(0)
        st = dict(in_st[b])
        for n in blocks[b]: transfer(st, n, False)
        for s in succ_b[b]:
            if in_st[s] is None: in_st[s] = dict(st); work.append(s)
            elif s in entries and not in_st[s]: pass
            else:
                new = {k: v for k, v in in_st[s].items() if st.get(k) == v}
                if new != in_st[s]: in_st[s] = new; work.append(s)
    # 書き換え
    changed = 0
    for b, ns in enumerate(blocks):
        if in_st[b] is None: continue
        st = dict(in_st[b])
        for n in ns:
            it = its[n]
            if it.dead: continue
            i = it.ins; e = a.eff[n]
            # 即値を持つレジスタが加減・比べの最後のオペランドなら、即値の形へ
            if (i.mn in ("add", "adds", "sub", "subs") and len(i.ops) == 3) or (i.mn in ("cmp", "cmn") and len(i.ops) == 2):
                mm = re.fullmatch(r"x(\d+)", i.ops[-1])
                if mm and int(mm.group(1)) < 13 and not any(re.fullmatch(r"w\d+", o) for o in i.ops) and not any(re.search(r"(?<![\w.#:])x%s\b" % mm.group(1), o) for o in i.ops[:-1]):
                    v = st.get(int(mm.group(1)))
                    if v and v[0] == "i" and re.fullmatch(r"#(0x[0-9a-fA-F]+|\d+)", v[1]) and int(v[1][1:], 0) <= 4095:
                        it.ins = Ins(i.mn, i.ops[:-1] + [v[1]], i.cm); it.raw = None; i = it.ins; changed += 1
                        e = a.reeff(n)
            # 読む側のコピー先を、同じ値を持つ別のレジスタへ
            if not e.call and not e.unk and i.mn not in ("movk",):
                rp = _readpos(i)
                new = list(i.ops); touched = False
                for k in rp:
                    for m in set(re.findall(r"(?<![\w.#:])x(\d+)\b", i.ops[k])):
                        r = int(m)
                        if r >= 13 or r not in st: continue
                        cls = sorted(q for q, vv in st.items() if isinstance(q, int) and vv == st[r] and q != r and (q < r and q < 13 or q >= 19))
                        if cls:
                            q = cls[0] if cls[0] < 13 else cls[-1]
                            nn = re.sub(r"(?<![\w.#:])x%d\b" % r, "x%d" % q, new[k])
                            if nn != new[k]: new[k] = nn; touched = True
                if touched and not any(re.fullmatch(r"w\d+", o) for o in i.ops):
                    it.ins = Ins(i.mn, new, i.cm); it.raw = None; i = it.ins; changed += 1
                    e = a.reeff(n)
            act = transfer(st, n, True)
            if act:
                if act[0] == "del": it.dead = True; changed += 1
                elif act[0] == "mov":
                    it.ins = Ins("mov", [act[1], act[2]], i.cm); it.raw = None; changed += 1
    return changed


def _readpos(i):
    mn = i.mn
    if mn in ALU and i.ops: return range(1, len(i.ops))
    if mn in sign_peep.LOADS: return range(1, len(i.ops))
    return range(len(i.ops))


# ---- ループ不変式の移動 ----
def licm(fn):
    a = Analysis(fn); its = fn.items; moved = 0
    # 戻り辺: 後ろのラベルへ飛ぶ分岐
    loops = []
    for n in a.idx:
        e = a.eff[n]
        if e.br and e.tgt in a.labels and a.labels[e.tgt] < n and a.first_after[e.tgt] is not None:
            loops.append((a.labels[e.tgt], n, e.tgt))
    for (hl, be, name) in loops:
        # 範囲 (hl, be]。外から範囲の中(先頭以外)への飛び込みが無いこと。先頭へは落ちて入る(前が無条件の飛び・ret でない)こと。
        body = [n for n in a.idx if hl < n <= be]
        ok = True
        for n in a.idx:
            e = a.eff[n]
            if e.br and e.tgt in a.labels:
                t = a.labels[e.tgt]
                inside = hl < n <= be
                if not inside and hl < t <= be: ok = False
                if not inside and t == hl and n > be: ok = False
        # 先頭ラベルの前の命令
        prev = None
        for k in range(hl - 1, -1, -1):
            if its[k].k == "i" and not its[k].dead: prev = k; break
        if prev is None or a.eff[prev].uncond: ok = False
        # 先頭ラベルが複数あっても(ラベルの並び)よいが、その手前に別のラベルがあれば、そこへの飛び込みが前から来るので不可
        k = hl - 1
        while k >= 0 and its[k].k in ("c",) : k -= 1
        if k >= 0 and its[k].k == "l": ok = False
        if not ok: continue
        has_call = any(a.eff[n].call for n in body)
        defcount = {}
        for n in body:
            for r in bits_of(a.eff[n].defs): defcount[r] = defcount.get(r, 0) + 1
        header_live = a.live_in[a.first_after[name]]
        cand = []
        for n in body:
            i = its[n].ins; e = a.eff[n]
            if i.mn not in HOIST or e.call or e.unk or (e.defs & F_BIT): continue
            if not re.fullmatch(r"x\d+", i.ops[0]): continue
            if any(re.fullmatch(r"w\d+", o) for o in i.ops): continue
            d = int(i.ops[0][1:])
            if d >= 29 or defcount.get(d, 0) != 1 or (header_live >> d) & 1: continue
            srcs = bits_of(e.use & ALLREG)
            if any(defcount.get(r, 0) for r in srcs): continue
            if 29 in srcs: continue
            cand.append(n)
        if not cand: continue
        # 1 つずつ(依存は次の回で)
        n = cand[0]
        node = its[n]
        node.dead = True
        its.insert(hl, It("i", ins=node.ins, raw=None))
        moved += 1
        return moved + licm(fn)             # 添字が動いたので解析し直す
    return moved


# ---- レジスタ割り付け ----
MIN_WEIGHT = 6


def loop_ranges(a):
    out = []
    for n in a.idx:
        e = a.eff[n]
        if e.br and e.tgt in a.labels and a.labels[e.tgt] < n: out.append((a.labels[e.tgt], n))
    return out


def promote(fn):
    a = Analysis(fn); its = fn.items
    if fn.F is None or fn.rets != 1 or fn.ldps != 1 or not a.slots: return 0
    if fn.F + 200 > 30000: return 0
    for n in a.idx:                         # 関数が既に x19〜x28 を使っていれば手を出さない
        if any(re.search(r"(?<![\w.#:])[xw](19|2[0-8])\b", o) for o in its[n].ins.ops): return 0
    loops = loop_ranges(a)
    W = sorted(a.wbit)
    if not W: return 0
    weight = {w: 0 for w in W}; cross = {w: False for w in W}
    for n in a.idx:
        e = a.eff[n]
        if e.slot:
            depth = sum(1 for (h, bb) in loops if h < n <= bb)
            weight[a.webof[n]] += 10 ** min(depth, 3)
        if e.call == "help":
            for w in W:
                if a.live_out[n] & a.wbit[w]: cross[w] = True
    edges = {w: set() for w in W}
    for n in a.idx:
        e = a.eff[n]
        if e.slot and e.slot[0] == "st":
            v = a.webof[n]
            for u in W:
                if u != v and a.live_out[n] & a.wbit[u]: edges[v].add(u); edges[u].add(v)
    if a.idx:
        li = a.live_in[a.idx[0]]
        ent = [w for w in W if li & a.wbit[w]]
        for x in ent:
            for y in ent:
                if x != y: edges[x].add(y)
    color = {}
    for k in sorted(W, key=lambda w: (-weight[w], w)):
        if weight[k] < MIN_WEIGHT: continue
        allowed = [26, 27, 28] if cross[k] else list(range(19, 29))
        used = {color[u] for u in edges[k] if u in color}
        for r in allowed:
            if r not in used: color[k] = r; break
    if not color: return 0
    regs = sorted(set(color.values()))
    S = 16 * ((len(regs) + 1) // 2); F = fn.F; NF = F + S
    # 命令の書き換え
    for n in a.idx:
        e = a.eff[n]
        if e.slot and a.webof[n] in color:
            r = "x%d" % color[a.webof[n]]; i = its[n].ins
            if e.slot[0] == "st": its[n].ins = Ins("mov", [r, i.ops[0]], i.cm)
            else: its[n].ins = Ins("mov", [i.ops[0], r], i.cm)
            its[n].raw = None
    # 枠の大きさ・積み上げ引数の位置・保存と復元
    out = []
    def saves(base):
        res = []; j = 0
        while j < len(regs):
            off = F + 8 * j
            if j + 1 < len(regs) and off + 8 <= 504: res.append(("stp", ["x%d" % regs[j], "x%d" % regs[j + 1], "[x29, #%d]" % off])); j += 2
            else: res.append(("str", ["x%d" % regs[j], "[x29, #%d]" % off])); j += 1
        return res
    def restores():
        res = []; j = 0
        while j < len(regs):
            off = F + 8 * j
            if j + 1 < len(regs) and off + 8 <= 504: res.append(("ldp", ["x%d" % regs[j], "x%d" % regs[j + 1], "[x29, #%d]" % off])); j += 2
            else: res.append(("ldr", ["x%d" % regs[j], "[x29, #%d]" % off])); j += 1
        return res
    for it in its:
        if it.dead or it.k != "i": out.append(it); continue
        i = it.ins; mn, ops = i.mn, i.ops
        if mn == "stp" and ops[:2] == ["x29", "x30"]:
            it.ins = Ins(mn, [ops[0], ops[1], "[sp, #-%d]!" % NF], i.cm); it.raw = None; out.append(it); continue
        if mn == "ldp" and ops[:2] == ["x29", "x30"]:
            for (m2, o2) in restores():
                x = It("i", ins=Ins(m2, o2, " 保存したレジスタを戻す")); x.keep = True; out.append(x)
            it.ins = Ins(mn, [ops[0], ops[1], ops[2], "#%d" % NF], i.cm); it.raw = None; out.append(it); continue
        if any("[x29, #" in o for o in ops):
            new = []
            for o in ops:
                m = re.fullmatch(r"\[x29, #(\d+)\]", o)
                new.append("[x29, #%d]" % (int(m.group(1)) + S) if (m and int(m.group(1)) >= F) else o)
            if new != ops: it.ins = Ins(mn, new, i.cm); it.raw = None
        out.append(it)
        if mn == "mov" and ops == ["x29", "sp"]:
            for (m2, o2) in saves(F):
                x = It("i", ins=Ins(m2, o2, " 呼ぶ側のために保存(x19〜x28 は呼び出し先が保つ約束)")); x.keep = True; out.append(x)
    fn.items = out; fn.F = NF
    return len(color)


# ---- 命令の並べ替え(ブロックの中の表のスケジューリング) ----
LAT_LOAD = 4
def _a53():
    """SIGN_SCHED_MODEL=a53: Cortex-A53(in-order・2 命令同時発行)向けの変種(実験。既定は従来のまま)。資料(GCC・LLVM の A53 のモデル)の読み 3・乗算 3・除算 8・
    同時発行の決め(1 サイクル 2 本まで・読み書きは 1 本ずつ・乗算は単独)に合わせる。実機で効くかは pi_sched/ で測る"""
    import os
    return os.environ.get("SIGN_SCHED_MODEL", "") == "a53"
def _lat(i):
    if i.mn in sign_peep.LOADS or i.mn == "ldr": return 3 if _a53() else LAT_LOAD
    if i.mn in ("mul", "smulh", "umulh", "madd", "msub", "smull", "umull"): return 3
    if i.mn in ("sdiv", "udiv"): return 8
    return 1


def _memkey(fn, i, escaped):
    """('r'|'w', キー)。キーは x29 相対の定数番地(エスケープが無いとき)か 'u'(どこかへ)。"""
    mn, ops = i.mn, i.ops
    if mn in sign_peep.LOADS or mn == "ldp": rw = "r"
    elif mn in sign_peep.STORES or mn == "stp": rw = "w"
    else: return None
    mem = [o for o in ops if o.startswith("[")]
    key = "u"
    if mem and not escaped:
        m = MEM8.match(mem[0])
        if m:
            w = 16 if mn in ("ldp", "stp") else 8
            key = (int(m.group(1) or 0), w)
    return (rw, key)


def _alias(k1, k2):
    if k1 == "u" or k2 == "u": return True
    return not (k1[0] + k1[1] <= k2[0] or k2[0] + k2[1] <= k1[0])


def schedule(lines):
    try:
        fn = Fn(lines)
        a = Analysis(fn)
    except Bail:
        return lines
    its = fn.items; esc = fn.escaped
    # 区切り: ラベル・コメント以外の壁・分岐・呼び・知らない命令
    out = []; seg = []
    def flush():
        if not seg: return
        out.extend(_sched_seg(fn, a, seg, esc)); del seg[:]
    for n, it in enumerate(its):
        if it.dead: continue
        if it.k != "i": flush(); out.append(it); continue
        e = a.eff[n]
        if re.search(r"(?<![\w.#:])sp\b", " ".join(it.ins.ops)) or (it.ins.ops and it.ins.ops[0] in ("x29", "x30")) or it.ins.mn in ("stp", "ldp") and "[sp" in " ".join(it.ins.ops):
            flush(); out.append(it); continue            # sp・x29・x30 を動かす命令(枠の出入り)は動かさない
        if e.call or e.unk or e.br or e.term or it.keep or it.ins.mn in ("nop", "yield", "wfi", "dmb", "dsb", "isb", "msr", "mrs", "ldaxr", "stlxr", "ldxr", "stxr", "ldar", "stlr"):
            if e.br and e.tgt.startswith(".Ltrap") and e.br == "bc" and not e.uncond:
                seg.append((n, it)); continue      # 罠への分岐は区切らない(順序だけ守る)
            flush(); out.append(it); continue
        seg.append((n, it))
    flush()
    return [(it.raw if it.raw is not None else it.ins.text()) for it in out]


def _sched_seg(fn, a, seg, esc):
    m = len(seg)
    if m < 3: return [it for _, it in seg]
    class _E: pass
    effs = []
    for n, _ in seg:
        o = a.eff[n]; q = _E(); q.use = o.use | ((1 << 29) if o.slot else 0); q.defs = o.defs; effs.append(q)
    mems = [_memkey(fn, it.ins, esc) if not (a.eff[n].br) else None for n, it in seg]
    istrap = [bool(a.eff[n].br) for n, _ in seg]
    preds = [set() for _ in range(m)]
    for j in range(m):
        ej = effs[j]
        for i in range(j):
            ei = effs[i]
            dep = (ei.defs & ej.use) or (ei.use & ej.defs) or (ei.defs & ej.defs)
            if not dep:
                mi, mj = mems[i], mems[j]
                if mi and mj and (mi[0] == "w" or mj[0] == "w") and _alias(mi[1], mj[1]): dep = True
                elif istrap[i] and (mj and mj[0] == "w"): dep = True
                elif istrap[j] and (mi and mi[0] == "w"): dep = True
                elif istrap[i] and istrap[j]: dep = True
            if dep: preds[j].add(i)
    succs = [[] for _ in range(m)]
    for j in range(m):
        for i in preds[j]: succs[i].append(j)
    prio = [0] * m
    for i in range(m - 1, -1, -1):
        prio[i] = _lat(seg[i][1].ins) + max((prio[j] for j in succs[i]), default=0)
    done = [False] * m; ready_at = [0] * m; npred = [len(p) for p in preds]
    cyc = 0; order = []
    avail_ = [i for i in range(m) if npred[i] == 0]
    if _a53():                                              # 1 サイクルに 2 本まで・読み書きは 1 本・乗算は単独
        ismul = [seg[i][1].ins.mn in ("mul", "smulh", "umulh", "madd", "msub", "smull", "umull") for i in range(m)]
        while len(order) < m:
            slots = 2; used_mem = False; picked = []
            while slots > 0:
                ok = [i for i in avail_ if ready_at[i] <= cyc and i not in picked and not (mems[i] and used_mem) and not (ismul[i] and slots < 2)]
                if not ok: break
                pick = max(ok, key=lambda i: (prio[i], -i))
                picked.append(pick); order.append(pick); avail_.remove(pick)
                if mems[pick]: used_mem = True
                slots = 0 if ismul[pick] else slots - 1
            for pick in picked:
                for j in succs[pick]:
                    ready_at[j] = max(ready_at[j], cyc + _lat(seg[pick][1].ins))
                    npred[j] -= 1
                    if npred[j] == 0: avail_.append(j)
            if picked: cyc += 1
            elif avail_: cyc = max(cyc + 1, min(ready_at[i] for i in avail_))
            else: break
        return [seg[i][1] for i in order]
    while len(order) < m:
        ok = [i for i in avail_ if ready_at[i] <= cyc]
        if ok: pick = max(ok, key=lambda i: (prio[i], -i))
        else:
            pick = min(avail_, key=lambda i: (ready_at[i], -prio[i], i)); cyc = ready_at[pick]
        avail_.remove(pick); order.append(pick); done[pick] = True
        t = cyc + 1
        for j in succs[pick]:
            ready_at[j] = max(ready_at[j], cyc + _lat(seg[pick][1].ins))
            npred[j] -= 1
            if npred[j] == 0: avail_.append(j)
        cyc = t
    return [seg[i][1] for i in order]


def optimize(lines):
    import os
    if os.environ.get("SIGN_OPT", "1") == "0": return sign_peep.optimize(lines)
    try:
        fn = Fn(lines)
        Analysis(fn)
    except Bail:
        return sign_peep.optimize(lines)
    try:
        for _ in range(4):
            c = avail(fn) + dce(fn)
            if not c: break
        if os.environ.get("SIGN_OPT_RA", "1") != "0": promote(fn)
        for _ in range(3):
            c = avail(fn) + dce(fn)
            if not c: break
        licm(fn)
        for _ in range(3):
            c = avail(fn) + dce(fn)
            if not c: break
    except Bail:
        return sign_peep.optimize(lines)
    out = [(it.raw if it.raw is not None else it.ins.text()) for it in fn.items if not it.dead]
    out = sign_peep.optimize(out)
    if os.environ.get("SIGN_SCHED", "1") != "0":
        try: out = schedule(out)
        except Bail: pass
    return out
