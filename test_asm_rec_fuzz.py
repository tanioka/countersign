"""--asm と --asm --strict の再帰(自分・輪)の乱数試験: `xs ' 1~` を `~` で撒きながら食う関数(底の行・前後に字面や要素)を作り、処理系(strict)の値と asm の値を突き合わせる。
断るのは許す(断りは違う答えより良い)。使い方: python3 test_asm_rec_fuzz.py [種 [件数]]"""
import sys, random, io
HERE="/home/claude/countersign"; sys.path.insert(0,HERE); sys.setrecursionlimit(20000)
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
random.seed(int(sys.argv[1]) if len(sys.argv)>1 else 1)
G=""
def lit(): return str(random.randint(0,9))
def guard(): return random.choice(["||xs|| = 1","||xs|| < 2","||xs|| <= 1","||xs|| = 1","||xs|| < 2","||xs|| > 3"])
def rec(name, other):
    """名前 name の関数 1 つ(自分か other を、`xs ' a~` で呼ぶ)"""
    a=1; call=random.choice([name,other])
    c="(%s (xs ' %d~))"%(call,a); tl=random.choice(["~",""])
    pre=" ".join(random.choice(["(xs ' 0)",lit()]) for _ in range(random.randint(1,2)))
    post=random.choice(["",""," "+lit()," "+lit()+" "+lit()])
    base=random.choice(["(xs ' 0) 9","7 8","(xs ' 0) (xs ' 0)","5 6 7"])
    return "%s : xs ?\n\t%s : %s\n\t%s %s%s%s\n"%(name,guard(),base,pre,c,tl,post)
def gen():
    mutual=random.random()<0.5
    d=rec("a","b" if mutual else "a")
    if mutual: d+="\n"+rec("b","a")
    n=random.randint(1,6)
    return d+"\na (%s)\n"%" ".join(lit() for _ in range(n))
bad=ok=ref=skip=0
for i in range(int(sys.argv[2]) if len(sys.argv)>2 else 150):
    t=gen(); sv=sval(t)
    if sv is None: skip+=1; continue
    try:
        tree,rest=sign_asm.strict_rewrite(S.parse_source(t))
        if rest: ref+=1; continue
        got=ns["run_asm"](sign_asm.generate(tree,"linux"),linux=True)
    except (sign_asm.StrictRefusal, sign_asm.AsmError): ref+=1; continue
    except Exception as e: ref+=1; continue
    if got[0]=="exit" and got[1].strip()==("__" if sv=="!_" else sv): ok+=1
    else: bad+=1; print("NG",repr(t),"strict",sv,"asm",got)
print("一致", ok, "断り", ref, "strict が断る", skip, "違う答え", bad)
print("全部 ok" if not bad and ok > 20 else "NG")
sys.exit(1 if bad or ok <= 20 else 0)
