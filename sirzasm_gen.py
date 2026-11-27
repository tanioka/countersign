"""sign_asm.py が出す整数 `+ - * / %` の命令列(`bin_tail`。左右が `!_` になりうる形)を取り出し、
formal/lean/SirZAsm.lean の `I` の配列(Lean の文字)に写す。`--no-peephole --no-opt` の出力から、
`movz x13, #0x8000, lsl #48` + `cmp x9, x13` で始まる所から、終わりの印(最初の `b` の行き先)までを取る。
使い方: python3 sirzasm_gen.py        (Lean の文字を出す)
        python3 sirzasm_gen.py --check (formal/lean/SirZAsm.lean の GENERATED と同じか確かめる。違えば exit 1)"""
import contextlib, io, os, re, sys, tempfile
import sign_asm as A

OPS = [("add", "+"), ("sub", "-"), ("mul", "*"), ("div", "/"), ("mod", "%")]

def compile_op(op):
    with tempfile.TemporaryDirectory() as d:
        p = os.path.join(d, "t.sn")
        open(p, "w").write(f"f : x y z ? (x / y) {op} (x / z)\nf 8 2 1\n")
        buf = io.StringIO()
        with contextlib.redirect_stdout(buf):
            A.main([p, "--no-peephole", "--no-opt"])
    return buf.getvalue().split("\n")

def block(lines):
    ls = [re.sub(r"//.*", "", l).strip() for l in lines]
    ls = [l for l in ls if l]
    for k in range(len(ls) - 1):
        if ls[k].startswith("movz x13, #0x8000, lsl #48") and ls[k + 1] == "cmp x9, x13": break
    else: raise SystemExit("テンプレートの始まりが見つからない")
    out = []
    end = None
    for l in ls[k:]:
        if end and l == end + ":": out.append(l); break
        out.append(l)
        m = re.fullmatch(r"b (\.L\d+)", l)
        if m and end is None: end = m.group(1)
    return out

def to_lean(name, blk):
    labels, idx = {}, 0
    for l in blk:
        if l.endswith(":"): labels[l[:-1]] = idx
        else: idx += 1
    r = lambda s: int(s.strip()[1:])
    ins = []
    for l in blk:
        if l.endswith(":"): continue
        op, _, rest = l.partition(" ")
        a = [x.strip() for x in rest.split(",")]
        if op == "movz": assert a[1:] == ["#0x8000", "lsl #48"], l; ins.append(f"I.movz {r(a[0])}")
        elif op == "mov": ins.append(f"I.mov {r(a[0])} {r(a[1])}")
        elif op == "cmp" and len(a) == 3: assert a[2] == "asr #63", l; ins.append(f"I.cmpAsr {r(a[0])} {r(a[1])} 63")
        elif op == "cmp" and a[1].startswith("#"): ins.append(f"I.cmpI {r(a[0])} {int(a[1][1:])}")
        elif op == "cmp": ins.append(f"I.cmpR {r(a[0])} {r(a[1])}")
        elif op in ("adds", "subs", "mul", "smulh", "sdiv"): ins.append(f"I.{op} {r(a[0])} {r(a[1])} {r(a[2])}")
        elif op == "msub": ins.append(f"I.msub {r(a[0])} {r(a[1])} {r(a[2])} {r(a[3])}")
        elif op == "csel": ins.append(f"I.csel {r(a[0])} {r(a[1])} {r(a[2])} Cond.{a[3]}")
        elif op.startswith("b."): ins.append(f"I.bc Cond.{op[2:]} {labels[rest.strip()]}")
        elif op == "b": ins.append(f"I.b {labels[rest.strip()]}")
        else: raise SystemExit("知らない命令: " + l)
    return f"def {name} : Array I := #[\n  " + ",\n  ".join(f"({x})" for x in ins) + "]\n"

def generated():
    return "".join(to_lean("tpl_" + n, block(compile_op(o))) + "\n" for n, o in OPS)

if __name__ == "__main__":
    g = generated()
    if "--check" in sys.argv:
        s = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "formal/lean/SirZAsm.lean")).read()
        m = re.search(r"-- BEGIN GENERATED\n(.*?)-- END GENERATED", s, re.S)
        if not m or m.group(1) != g: print("SirZAsm.lean の GENERATED が、いまの sign_asm.py の出力と違う"); sys.exit(1)
        print("ok: 5 つの命令列が sign_asm.py の出力と同じ"); sys.exit(0)
    print(g)
