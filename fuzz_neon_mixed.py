"""fuzz_neon_mixed.py — Int の関数の値を Float / Vector の関数へ渡す混在の乱数試験(処理系と --target=linux の通しを比べる)。使い方: python3 fuzz_neon_mixed.py 種 本数"""
import os,sys,random
os.chdir("/mnt/user-data/outputs"); sys.path.insert(0,".")
seed=int(sys.argv[1]); N=int(sys.argv[2]); sys.argv=["x"]
src=open("test_neon.py",encoding="utf-8").read().split("V1, V2 =")[0].replace("HERE = os.path.dirname(os.path.abspath(__file__))","HERE = \"/mnt/user-data/outputs\"")
exec(compile(src,"tn","exec"))
import sign_asm
def run_linux(prog):
    text=sign_asm.generate(sign_interp.parse_source(prog),target="linux")
    c=NeonCpu(text); c.r["sp"]=0x7fff0000; c.run("_start",limit=80_000_000); return bytes(c.out).decode(), c.exit
rnd=random.Random(seed); n=bad=ref=0
for i in range(N):
    kind=rnd.choice(["V","F"])
    a = "[%s]"%" ".join(rnd.choice(["1.0","2.5","0.1","100.0","0.3333"]) for _ in range(4)) if kind=="V" else rnd.choice(["0.1","2.5","3.0"])
    e="a"
    for _ in range(rnd.randint(1,4)):
        t=rnd.choice(["n","m","0.5","a","3","n","m"]); op=rnd.choice("+-*")
        e="(%s %s %s)"%(e,op,t) if rnd.random()<.6 else "(%s %s %s)"%(t,op,e)
    if "n" not in e and "m" not in e: continue
    prog="g : n ? n * 2 + 1\nf : a n m ? %s\nf %s %s %s\n"%(e,a,rnd.choice(["(g 3)","(g 10)","77","0"]),rnd.choice(["5","(g 2)","123456789","9007199254740993"]))
    w=interp(prog)
    try: got=run_linux(prog)
    except (sign_neon.NeonError, sign_asm.AsmError) as ex:
        ref+=1
        if ref<4: print("断り",str(ex)[:60],repr(e))
        continue
    n+=1
    if got!=(w+"\n",0): bad+=1; print("NG",repr(prog),got,w)
print("混在の乱数: 比べた",n,"断り",ref,"不一致",bad)
