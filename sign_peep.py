"""sign_peep.py — AArch64 の出力に対するピープホール最適化(関数ごと、基本ブロックの中だけ)。

出力された命令列(文字)を、小さな窓と『その先で読まれるか』の確かめで置き換える。意味は変えない。
  P1 保存→読み込みの転送   str xS,[x29,#k] … ldr xD,[x29,#k]  →  ldr を消す(D≠S なら mov xD,xS)
  P2 即値の畳み込み        mov xA,#n … add/sub/cmp … xA        →  #n を命令に埋める(0〜4095)
  P3 コピーの伝播          mov xA,xB … xA を読む              →  xB を読む(あとで xA が読まれなければ mov を消す)
  P4 定義の付け替え        … xA を作る … mov xB,xA             →  最初から xB に作る(xA がそのあと読まれなければ)
  P5 次の行へ飛ぶだけの b、mov xA,xA を消す
安全のための決まり(判らなければ何もしない):
  - ラベル・指令・未知の命令・bl/blr/br/ret・罠以外への分岐は『全部読まれる』とみなす(そこで探索を止め、消さない)。
  - 罠(`.Ltrap*`)への分岐は何も読まない(罠の先はレジスタを見ない。x16 だけ書く)。
  - w レジスタの形・書き戻し付きの番地・未知の命令が絡むときは触らない。
  - 使うレジスタは x0〜x12 だけ(x13 の `__` の印、x15/x17 の返値の受け渡し、x29/x30 には触らない)。
環境変数 SIGN_PEEP=0(または `--no-peephole`)で無効にできる。
"""
import re

_INSN = re.compile(r"^\t([a-z][a-z0-9.]*)(?:\s+(.*?))?\s*$")
_REG = re.compile(r"(?<![\w.#:])([xw])(\d+)\b")

ALU_W = {"mov", "add", "adds", "sub", "subs", "mul", "and", "orr", "eor", "lsl", "lsr", "asr", "ror", "neg", "negs", "mvn",
         "sdiv", "udiv", "cset", "csel", "csinc", "csinv", "csneg", "movz", "movn", "sxtw", "uxtw", "sxtb", "uxtb", "sxth", "uxth",
         "ands", "bic", "madd", "msub", "smulh", "umulh", "adrp", "adr", "clz", "rbit", "ubfx", "sbfx", "smull", "umull", "cinc"}
ALU_R = {"cmp", "cmn", "tst", "ccmp", "ccmn"}          # 書かない・読むだけ
LOADS = {"ldr", "ldrb", "ldrh", "ldrsb", "ldrsh", "ldrsw", "ldur", "ldurb", "ldurh"}
STORES = {"str", "strb", "strh", "stur", "sturb", "sturh"}
CBR = {"cbz", "cbnz", "tbz", "tbnz"}
SAFE = range(0, 13)


def _split_ops(s):
    ops, depth, cur = [], 0, ""
    for ch in s:
        if ch == "[": depth += 1
        elif ch == "]": depth -= 1
        if ch == "," and depth == 0: ops.append(cur.strip()); cur = ""
        else: cur += ch
    if cur.strip(): ops.append(cur.strip())
    return ops


class Ins:
    __slots__ = ("mn", "ops", "cm")
    def __init__(self, mn, ops, cm): self.mn, self.ops, self.cm = mn, ops, cm
    def text(self): return "\t%s%s%s" % (self.mn, (" " + ", ".join(self.ops)) if self.ops else "", ("  //" + self.cm) if self.cm is not None else "")


def _parse(line):
    """行 → Ins / 'c'(コメントだけの行。素通り)/ None(ラベル・指令・その他。壁)。"""
    if "\n" in line: return None
    body, sep, cm = line.partition("//")
    if not body.strip(): return "c" if sep else None
    m = _INSN.match(body)
    if not m: return None
    return Ins(m.group(1), _split_ops(m.group(2) or ""), cm if sep else None)


def _regs(op):
    return [(k, int(n)) for k, n in _REG.findall(op)]


def _info(i, strict=True):
    """(種類, 読むレジスタ番号の集合, 必ず書くレジスタ番号の集合, 'w の形がある')。種類: alu / load / store / trapbr / trapb / barrier。"""
    mn, ops = i.mn, i.ops
    if (not strict) and mn in ("stp", "ldp") and len(ops) >= 3 and ops[:2] == ["x29", "x30"] and ops[2].startswith("[sp"):
        return ("frame", ({29, 30} if mn == "stp" else set()), ({29, 30} if mn == "ldp" else set()), False)
    if any("!" in o for o in ops) or any(re.search(r"\],\s*#", o) for o in ops): return ("barrier", set(), set(), True)
    wform = any(k == "w" for o in ops for k, _ in _regs(o))
    def R(ix): return {n for o in ix for _, n in _regs(o)}
    if mn in ALU_W and ops:
        if mn == "movk": return ("barrier", set(), set(), True)
        d = _regs(ops[0])
        if len(d) != 1 or ops[0] not in ("x%d" % d[0][1], "w%d" % d[0][1]): return ("barrier", set(), set(), True)
        return ("alu", R(ops[1:]), {d[0][1]}, wform)
    if mn in ALU_R: return ("alu", R(ops), set(), wform)
    if mn in LOADS and len(ops) == 2:
        d = _regs(ops[0])
        if len(d) != 1 or ops[0] not in ("x%d" % d[0][1], "w%d" % d[0][1]) or not ops[1].startswith("["): return ("barrier", set(), set(), True)
        return ("load", R(ops[1:]), {d[0][1]}, wform)
    if mn in STORES and len(ops) == 2: return ("store", R(ops), set(), wform)
    if mn.startswith("b.") and len(ops) == 1:
        return ("trapbr" if ops[0].startswith(".Ltrap") else ("cbr" if ops[0] in _CTX["labels"] else "barrier"), set(), set(), False)
    if mn in CBR and len(ops) >= 2 and ops[-1].startswith(".Ltrap"): return ("trapbr", R(ops[:-1]), set(), wform)
    if mn in CBR and len(ops) >= 2 and ops[-1] in _CTX["labels"]: return ("cbr", R(ops[:-1]), set(), wform)
    if mn == "b" and len(ops) == 1 and ops[0].startswith(".Ltrap"): return ("trapb", set(), set(), False)
    return ("barrier", set(), set(), True)


def _skip(x): return x == "c" or x == "del"


_CTX = {"labels": {}}


def _dead_after(items, pos, r):
    """items[pos] の後で、レジスタ r が読まれる前に必ず書かれる/罠に落ちる/返る(x9〜x12 は返値ではない)と、すべての道で言えれば True。
    同じ関数の中のラベルへの分岐は辿る。それ以外(呼び・未知の命令・指令)は『読まれる』とみなす。"""
    labels = _CTX["labels"]; seen = set()
    def walk(k):
        while k < len(items):
            if k in seen: return True
            seen.add(k)
            it = items[k]
            if _skip(it): k += 1; continue
            if it is None:
                if k in _CTX["labidx"]: k += 1; continue
                return False
            mn, ops = it.mn, it.ops
            if mn == "ret": return r >= 9
            if mn == "bl" and len(ops) == 1 and not ops[0].startswith(("_sign_", "_.", ".")) : return r >= 9      # Sign の関数の呼び: 引数は x0〜x7・x8・x15・x17 だけ。x9〜x12 の値は呼びをまたいで生きない(AAPCS の破壊される側)
            if mn == "b" and len(ops) == 1 and ops[0] in labels: k = labels[ops[0]]; continue
            kind, rd, wr, wf = _info(it, strict=False)
            if mn.startswith("b.") and len(ops) == 1 and ops[0] in labels:
                if not walk(labels[ops[0]]): return False
                k += 1; continue
            if mn in CBR and ops and ops[-1] in labels:
                if r in {n for o in ops[:-1] for _, n in _regs(o)}: return False
                if not walk(labels[ops[-1]]): return False
                k += 1; continue
            if kind == "barrier": return False
            if r in rd: return False
            if kind == "trapb": return True
            if r in wr: return True
            k += 1
        return False
    return walk(pos + 1)


def _sub(op, a, b):
    """オペランド文字列の中の x<a> を x<b> に。"""
    return re.sub(r"(?<![\w.#:])x%d\b" % a, "x%d" % b, op)


def _has(op, r):
    return any(n == r for _, n in _regs(op))


def _mentions(i, r):
    return any(_has(o, r) for o in i.ops)


def _readpos(i, kind):
    """読む側のオペランドの位置(書く先の第 1 オペランドは含めない)。"""
    return range(1, len(i.ops)) if (kind in ("alu", "load") and i.mn not in ALU_R) else range(len(i.ops))


def p_forward_store_load(items):
    ch = False
    for i, it in enumerate(items):
        if not isinstance(it, Ins) or it.mn != "str" or len(it.ops) != 2 or not re.fullmatch(r"x\d+", it.ops[0]) or not re.fullmatch(r"\[x29, #\d+\]", it.ops[1]): continue
        s = int(it.ops[0][1:]); slot = it.ops[1]
        for j in range(i + 1, len(items)):
            jt = items[j]
            if _skip(jt): continue
            if not isinstance(jt, Ins): break
            kind, rd, wr, wf = _info(jt)
            if kind in ("barrier", "store", "trapb"): break
            if jt.mn == "ldr" and len(jt.ops) == 2 and jt.ops[1] == slot and re.fullmatch(r"x\d+", jt.ops[0]):
                d = int(jt.ops[0][1:])
                if d == s: items[j] = "del"; ch = True
                elif d in SAFE and s in SAFE: items[j] = Ins("mov", [jt.ops[0], it.ops[0]], jt.cm); ch = True
                break
            if s in wr: break
    return ch


def p_imm_fold(items):
    ch = False
    for i, it in enumerate(items):
        if not isinstance(it, Ins) or it.mn != "mov" or len(it.ops) != 2 or not re.fullmatch(r"x\d+", it.ops[0]): continue
        a = int(it.ops[0][1:])
        if a not in SAFE: continue
        m = re.fullmatch(r"#(0x[0-9a-fA-F]+|\d+)", it.ops[1])
        if not m or int(m.group(1), 0) > 4095: continue
        imm = it.ops[1]
        for j in range(i + 1, min(len(items), i + 8)):
            jt = items[j]
            if _skip(jt): continue
            if not isinstance(jt, Ins): break
            kind, rd, wr, wf = _info(jt)
            if kind == "barrier": break
            if a in rd or a in wr:
                n = 2 if jt.mn in ("cmp", "cmn") else 3
                if (not wf and jt.mn in ("add", "adds", "sub", "subs", "cmp", "cmn") and len(jt.ops) == n and jt.ops[-1] == "x%d" % a
                        and not any(_has(o, a) for o in jt.ops[:-1])):
                    jt.ops[-1] = imm
                    if _dead_after(items, i, a): items[i] = "del"
                    ch = True
                break
    return ch


def p_copy_prop(items):
    ch = False
    for i, it in enumerate(items):
        if not isinstance(it, Ins) or it.mn != "mov" or len(it.ops) != 2: continue
        if not (re.fullmatch(r"x\d+", it.ops[0]) and re.fullmatch(r"x\d+", it.ops[1])): continue
        a, b = int(it.ops[0][1:]), int(it.ops[1][1:])
        if a == b or a not in SAFE or b not in SAFE: continue
        trial = list(items); ok = True
        for j in range(i + 1, len(items)):
            jt = trial[j]
            if _skip(jt): continue
            if not isinstance(jt, Ins): break
            kind, rd, wr, wf = _info(jt)
            if kind == "barrier": break
            if a in rd:
                if wf: ok = False; break
                new = list(jt.ops)
                for k in _readpos(jt, kind): new[k] = _sub(jt.ops[k], a, b)
                if any(_has(new[k], a) for k in _readpos(jt, kind)): ok = False; break
                trial[j] = Ins(jt.mn, new, jt.cm)
            if b in wr or a in wr or kind == "trapb": break
        if not ok: continue
        if _dead_after(trial, i, a):
            trial[i] = "del"
            items[:] = trial; ch = True
    return ch


def p_retarget(items):
    ch = False
    for j, it in enumerate(items):
        if not isinstance(it, Ins) or it.mn != "mov" or len(it.ops) != 2: continue
        if not (re.fullmatch(r"x\d+", it.ops[0]) and re.fullmatch(r"x\d+", it.ops[1])): continue
        b, a = int(it.ops[0][1:]), int(it.ops[1][1:])
        if a == b or a not in SAFE or b not in SAFE: continue
        if not _dead_after(items, j, a): continue
        trial = {}; found = False
        for k in range(j - 1, -1, -1):
            kt = items[k]
            if _skip(kt): continue
            if not isinstance(kt, Ins): break
            kind, rd, wr, wf = _info(kt)
            if kind in ("barrier", "trapb", "cbr") or wf: break
            if _mentions(kt, b) and not (a in wr and a not in rd and b not in wr): break      # b を読んで a を作る命令(subs x9,x0,#1 など)だけは、b に作り直してよい
            if a in rd or a in wr:
                new = list(kt.ops)
                rp = set(_readpos(kt, kind))
                for q, o in enumerate(kt.ops):
                    if q in rp: new[q] = _sub(o, a, b)
                    elif a in wr: new[q] = _sub(o, a, b)       # 書く先(第 1 オペランド)
                trial[k] = Ins(kt.mn, new, kt.cm)
                if a in wr and a not in rd: found = True; break
        if not found: continue
        for k, v in trial.items(): items[k] = v
        items[j] = "del"; ch = True
    return ch


def p_selfmov(items):
    ch = False
    for i, it in enumerate(items):
        if isinstance(it, Ins) and it.mn == "mov" and len(it.ops) == 2 and it.ops[0] == it.ops[1] and re.fullmatch(r"x\d+", it.ops[0]):
            items[i] = "del"; ch = True
    return ch


def optimize(lines, passes=8):
    """lines: 関数の命令列(行の文字列の並び)。同じ意味の短い列を返す。"""
    work = []
    _CTX["labels"] = {}; _CTX["labidx"] = set()
    for k, ln in enumerate(lines):
        mm = re.match(r"^([A-Za-z_.][\w.$]*):\s*$", ln)
        if mm: _CTX["labels"][mm.group(1)] = k; _CTX["labidx"].add(k)
    for ln in lines:
        p = _parse(ln)
        work.append(p)                                   # Ins / "c" / None(壁)
    for _ in range(passes):
        ch = False
        for p in (p_forward_store_load, p_imm_fold, p_copy_prop, p_retarget, p_selfmov):
            if p(work): ch = True
        if not ch: break
    out = []
    for w, orig in zip(work, lines):
        if w == "del": continue
        out.append(w.text() if isinstance(w, Ins) else orig)
    # 次の行へ飛ぶだけの b を消す
    res = []
    for ln in out:
        res.append(ln)
    k = 0
    while k < len(res) - 1:
        m = re.match(r"^\tb (\S+)\s*(//.*)?$", res[k])
        if m:
            n = k + 1
            while n < len(res) and res[n].strip().startswith("//"): n += 1
            if n < len(res) and res[n] == m.group(1) + ":": del res[k]; continue
        k += 1
    # b.cc A / b B / A:  →  b.!cc B / A:
    INV = {"eq": "ne", "ne": "eq", "ge": "lt", "lt": "ge", "gt": "le", "le": "gt", "hs": "lo", "lo": "hs", "cs": "cc", "cc": "cs",
           "mi": "pl", "pl": "mi", "vs": "vc", "vc": "vs", "hi": "ls", "ls": "hi"}
    k = 0
    while k < len(res) - 2:
        m1 = re.match(r"^\tb\.(\w+) (\S+)\s*(//.*)?$", res[k]); m2 = re.match(r"^\tb (\S+)\s*(//.*)?$", res[k + 1])
        if m1 and m2 and m1.group(1) in INV and res[k + 2] == m1.group(2) + ":" and not m1.group(2).startswith(".Ltrap"):
            res[k:k + 2] = ["\tb.%s %s" % (INV[m1.group(1)], m2.group(1))]; continue
        k += 1
    return res
