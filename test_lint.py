#!/usr/bin/env python3
"""sign_lint の試験: (1) 作り物の悪い asm を拾う (2) 実際の出力から命令を消して拾う (3) 良い出力は 0 件。"""
import sys; sys.path.insert(0, ".")
import sign_lint, sign_interp, sign_asm
ng = 0
def chk(label, cond):
    global ng
    print(("ok  " if cond else "NG  ") + label); ng += (not cond)
def rules(t): return sorted({r[2] for r in sign_lint.lint(t)})
F = "f:\n\tstp x29, x30, [sp, #-32]!\n\tmov x29, sp\n%s\n\tldp x29, x30, [sp], #32\n\tret\n"
chk("良い: 取って捨てる", rules(F % "\tsub sp, sp, #80\n\tmov x8, sp\n\tstr xzr, [x8]\n\tmov sp, x29") == [])
chk("L1 捨て忘れ", rules(F % "\tsub sp, sp, #80\n\tmov x8, sp") == ["L1"])
chk("L2 外のメモリへアドレスを書く", rules(F % "\tsub sp, sp, #80\n\tmov x8, sp\n\tstr x8, [x0]\n\tmov sp, x29") == ["L2"])
chk("L2 フレームへの退避はよい", rules(F % "\tsub sp, sp, #80\n\tmov x8, sp\n\tstr x8, [x29, #16]\n\tmov sp, x29") == [])
chk("L2 アドレスを x0 に持って ret", rules(F % "\tsub sp, sp, #80\n\tmov x0, sp\n\tmov sp, x29") == ["L2"])
chk("L3 捨てた後に読む", "L3" in rules(F % "\tsub sp, sp, #80\n\tmov x8, sp\n\tmov sp, x29\n\tmov x1, x8"))
chk("L3 作り直せばよい", rules(F % "\tsub sp, sp, #80\n\tmov x8, sp\n\tmov sp, x29\n\tmov x8, #0\n\tmov x1, x8") == [])
progs = ["n2.sn", "n3.sn", "n4.sn", "fib_bench.sn", "sierpinski.sn"]
import os
for p in progs:
    if not os.path.exists(p): continue
    nodes = sign_interp.parse_source(open(p, encoding="utf-8").read(), p)
    s = sign_asm.generate(nodes)
    chk("実出力 %s は 0 件" % p, sign_lint.lint(s) == [])
    if "mov sp, x29" in s:
        bad = s.replace("\tmov sp, x29", "\tnop", 1)
        chk("  %s: mov sp,x29 を消すと L1" % p, "L1" in rules(bad))
# 生成時に走る: 壊した出力で LAST_LINT に出る / --no-lint で走らない
orig = sign_asm.Program.generate
sign_asm.Program.generate = lambda self, *a, **k: orig(self, *a, **k).replace("\tmov sp, x29  //", "\tnop  //")
n = sign_interp.parse_source(open("n2.sn", encoding="utf-8").read(), "n2.sn")
sign_asm.generate(n); chk("生成時の lint が L1 を出す", [r[2] for r in sign_asm.LAST_LINT] == ["L1"])
sign_asm.LINT[0] = False; sign_asm.generate(n); chk("LINT 切りなら出ない", sign_asm.LAST_LINT == [])
sign_asm.LINT[0] = True; sign_asm.Program.generate = orig
sign_asm.generate(n); chk("正常な出力は警告なし", sign_asm.LAST_LINT == [])
print("全部 ok" if not ng else "NG %d 件" % ng); sys.exit(1 if ng else 0)
