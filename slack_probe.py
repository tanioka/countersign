# 作業領域の余裕の目安: 入口の sp からの最大の沈み(バイト)と、答えの要素数×8 の比。沈みにはフレームも含むので上限の目安。
import sys, re, subprocess
sys.path.insert(0,'/mnt/user-data/outputs')
src=open('/mnt/user-data/outputs/test_asm.py',encoding='utf-8').read()
ns={'__file__':'/mnt/user-data/outputs/test_asm.py','__name__':'emu'}
exec(compile(src[:src.index('# ---------------- 処理系の答え')],'emu','exec'),ns)
import sign_asm, sign_interp
class R(dict):
    lo=None
    def __setitem__(s,k,v):
        if k=="sp": s.lo = v if s.lo is None else min(s.lo,v)
        if k=="x12" and "sp" in s and v==s["sp"]+16: s.caps.append(s.get("x10"))
        dict.__setitem__(s,k,v)
for f in sys.argv[1:]:
    t=open(f,encoding='utf-8').read()
    try: a=sign_asm.generate(sign_interp.parse_source(t),'linux')
    except sign_asm.AsmError as e: print(f,'断り'); continue
    c=ns['Cpu'](a); r=R(c.r); r.caps=[]; c.r=r; sp0=r.get("sp"); r.lo=sp0
    c.run("_start"); out=c.out.decode()
    n=len(re.findall(r"-?\d+|`",out)) or 1
    print(f, "作業領域の個数", r.caps, "/ 答え", n, "要素 =", [round(x/n,1) for x in r.caps], "倍;", "沈み", sp0-r.lo, "B / 答え", n, "要素 =", round((sp0-r.lo)/(8*n),1), "倍")
