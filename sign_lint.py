#!/usr/bin/env python3
"""sign_lint.py — 生成した asm(テキスト)の「置き場の寿命」検査。

Sign には所有権の仕組みがない(置き場は alloca で取り、寿命はコンパイル時に決まる)。
これは言語の機能ではなく、バックエンドの出力が置き場の寿命を守っているかを見る静的な検査である。
関数ごとに、命令を上から順にたどり、次の 3 つを調べる。

  L1 sp の釣り合い : `sub sp` で取った置き場が、`ret` の前に捨てられている(mov sp, x29 / add sp)。
  L2 逃げ      : sp / x29 から作ったアドレス(置き場の中を指す)を、自分のフレームの外のメモリへ書かない
                 (自分のフレームの `[x29,#n]` `[sp,#n]` への退避はよい)。x0 に入れたまま ret もしない。
  L3 捨てた後の使用: 置き場を捨てた(mov sp,x29 / add sp)あとで、その置き場から作ったレジスタを
                 作り直さずに読まない。

分岐は追わない(上から 1 本の流れで見る)。ラベルに来たら汚れ(taint)の集合は保ったままにする。
見つけたものは (関数, 行, 規則, 説明) の一覧で返す。違反が 0 件なら空。"""
import re, sys

REG = r"[xw]\d+|sp|xzr|wzr"


def split_functions(text):
    """ラベル(行頭の `name:`)で始まり、`ret` で終わるまとまりを 1 関数とする。"""
    funcs, cur, name = [], [], None
    for ln, raw in enumerate(text.split("\n"), 1):
        s = raw.split("//")[0].strip()
        if not s: continue
        m = re.match(r"^([A-Za-z_.$][\w.$]*):$", s)
        if m and not m.group(1).startswith((".L", "L")) and not re.match(r"^\.?L\d", m.group(1)):
            if cur: funcs.append((name, cur))
            name, cur = m.group(1), []
            continue
        cur.append((ln, s))
    if cur: funcs.append((name, cur))
    return funcs


def base(r):
    return "x" + r[1:] if r[0] == "w" else r


def check_function(name, insns):
    out = []
    taint = {}          # レジスタ -> 置き場の通し番号(sp / x29 から作ったアドレス)
    dyn = 0             # 取ったままの置き場の数
    released = set()    # 捨てた置き場の番号
    slot_no = 0
    cur_slot = None
    for ln, s in insns:
        op, _, rest = s.partition(" ")
        args = [a.strip() for a in re.split(r",(?![^\[]*\])", rest)] if rest else []
        def add(rule, msg): out.append((name, ln, rule, msg + "  | " + s))
        # --- sp の動き ---
        if op == "sub" and args[:2] == ["sp", "sp"]:
            dyn += 1; slot_no += 1; cur_slot = slot_no
            continue
        if op == "mov" and args == ["sp", "x29"]:
            for k in range(1, slot_no + 1): released.add(k)
            dyn = 0
            continue
        if op == "add" and args[:2] == ["sp", "sp"]:
            dyn = max(0, dyn - 1)
            if cur_slot: released.add(cur_slot); cur_slot = max([k for k in range(1, slot_no + 1) if k not in released] or [None]) if slot_no else None
            continue
        if op == "ret":
            if dyn: add("L1", "置き場 %d 個を捨てずに ret" % dyn)
            for r, k in taint.items():
                if r in ("x0", "x1"):                       # フレームは ret で消える。捨てた後でも持ち出しは逃げ
                    add("L2", "%s に置き場のアドレスを持ったまま ret" % r)
            continue
        # --- アドレスの生成 ---
        if op == "mov" and len(args) == 2 and args[1] == "sp":
            taint[base(args[0])] = cur_slot if cur_slot else 0; continue
        if op in ("add", "sub") and len(args) == 3 and args[1] in ("sp", "x29") and not args[0] == "sp":
            taint[base(args[0])] = cur_slot if args[1] == "sp" and cur_slot else 0; continue
        # --- 汚れの伝わり ---
        if op in ("mov", "add", "sub", "lsl", "lsr", "and", "orr") and args:
            d = base(args[0])
            srcs = [base(a) for a in args[1:] if re.fullmatch(REG, a)]
            src_t = [taint[a] for a in srcs if a in taint]
            if src_t and op in ("mov", "add", "sub"): taint[d] = src_t[0]
            else: taint.pop(d, None)
            for a in srcs:
                if a in taint and taint[a] and taint[a] in released and a != d:
                    add("L3", "捨てた置き場 %d から作った %s を読む" % (taint[a], a))
            continue
        # --- メモリ ---
        if op in ("str", "stp", "strb", "strh"):
            m = re.search(r"\[([^\]]*)\]", rest)
            addr = m.group(1) if m else ""
            ab = base(addr.split(",")[0].strip()) if addr else ""
            own = addr.startswith(("x29", "sp")) or ab in taint      # 自分のフレーム、または置き場の中への書き込み
            vals = [base(a) for a in args if re.fullmatch(REG, a) and a != "sp"]
            vals = vals[:2] if op == "stp" else vals[:1]
            for v in vals:
                if v in taint and not own:
                    add("L2", "置き場のアドレス %s を、自分のフレームの外へ書く" % v)
            continue
        if op in ("ldr", "ldp", "ldrb", "ldrh", "ldrsw"):
            for a in args:
                if re.fullmatch(REG, a) and a != "sp": taint.pop(base(a), None)
            continue
        if op == "bl":
            for r in list(taint):
                if r.startswith("x") and r[1:].isdigit() and int(r[1:]) <= 18: taint.pop(r, None)
    return out


def lint(text):
    res = []
    for name, ins in split_functions(text):
        res += check_function(name, ins)
    return res


def main(argv):
    sys.path.insert(0, ".")
    import sign_interp, sign_asm
    bad = 0
    for p in argv[1:]:
        nodes = sign_interp.parse_source(open(p, encoding="utf-8").read(), p)
        s = None
        for cs in ("ascii", "utf32"):          # 既定の ascii、だめなら --charset=utf32 と同じ
            try:
                s = sign_asm.generate(nodes, charset=cs); break
            except Exception as e:
                err = e
        if s is None:
            print("%s: 生成できず(%s)" % (p, str(err)[:40])); continue
        r = lint(s)
        print("%s: 違反 %d" % (p, len(r)))
        for x in r[:5]: print("   ", x)
        bad += len(r)
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
