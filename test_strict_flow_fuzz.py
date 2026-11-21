"""--asm --strict の部分適用(R83・R84)の乱数試験: `!_` になりうる実引数の呼びの前後に値を並べた小さな関数を作り、strict の値と asm の値を突き合わせる。
断るのは許す(断りは違う答えより良い)。使い方: python3 test_strict_flow_fuzz.py [種 [件数]]"""
import sys, os, random, io
HERE=os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0,HERE); sys.setrecursionlimit(20000)
src=open(HERE+"/test_asm.py",encoding="utf-8").read()
ns={"__file__":HERE+"/test_asm.py","__name__":"emu"}
exec(compile(src[:src.index("# ---------------- 処理系の答え")],"emu","exec"),ns)
import sign_asm, sign_interp as S
sign_asm.STRICT[0]=True
def sval(t):
    S.STRICT_GATES=True
    try:
        S.MEMORY.clear(); S.WARNINGS.clear(); old=sys.stdout; sys.stdout=io.StringIO()
        try: r=S.run(t)
        finally: sys.stdout=old
        return S.show(r[-1]) if r else "!_"
    except BaseException: return None
    finally: S.STRICT_GATES=False
random.seed(int(sys.argv[1]) if len(sys.argv)>1 else 7)
G="g : x ? x + 1\nk : x y ? x * 2 + y\nm : s ? (s ' 0)\nn : xs ? ||xs||\nq : xs ? (xs ' 0) + 1\n"
def intarg(): return random.choice(["(x > %d)","(x < %d)","(x - %d > 0)","(x %% %d)","(x / %d)"]) % random.randint(0,6)
def lit(): return str(random.randint(0,9))
def gen():
    k=random.choice(range(6))
    pre=" ".join(lit() for _ in range(random.randint(0,2))); post=" ".join(lit() for _ in range(random.randint(1,3)))
    if k==0: body="%s (g %s) %s"%(pre,intarg(),post)
    elif k==1: body="%s (k %s %s) %s"%(pre,intarg(),lit(),post)
    elif k==2: body="%s (k %s %s) %s"%(pre,lit(),intarg(),post)
    elif k==3: body="%s (n (xs ' %d~)) %s"%(pre,random.randint(1,3),post); return "f : xs ? "+body+"\n\nf (%s)\n"%" ".join(lit() for _ in range(random.randint(1,5)))
    elif k==4: body="%s (q (xs ' %d~)) %s"%(pre,random.randint(1,3),post); return "f : xs ? "+body+"\n\nf (%s)\n"%" ".join(lit() for _ in range(random.randint(1,5)))
    else: body="%s + (g %s)"%(lit(),intarg())
    return "f : x ? "+body+"\n\nf %d\n"%random.randint(0,9)
bad=ok=ref=skip=0
for i in range(int(sys.argv[2]) if len(sys.argv)>2 else 60):
    t=G+"\n"+gen(); sv=sval(t)
    if sv is None: skip+=1; continue
    try:
        tree,rest=sign_asm.strict_rewrite(S.parse_source(t))
        if rest: ref+=1; continue
        got=ns["run_asm"](sign_asm.generate(tree,"linux"),linux=True)
    except (sign_asm.StrictRefusal, sign_asm.AsmError): ref+=1; continue
    except Exception as e: ref+=1; continue
    if got[0]=="exit" and got[1].strip()==("__" if sv=="!_" else sv): ok+=1
    else: bad+=1; print("NG",repr(t[len(G):]),"strict",sv,"asm",got)
print("一致", ok, "断り", ref, "strict が断る", skip, "違う答え", bad)
print("全部 ok" if not bad and ok > 30 else "NG")
sys.exit(1 if bad or ok <= 30 else 0)
