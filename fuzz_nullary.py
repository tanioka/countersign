import os as _os
HERE_ = _os.path.dirname(_os.path.abspath(__file__))
import os,sys,random
os.chdir(HERE_); sys.path.insert(0,HERE_)
src_t=open("test_asm.py",encoding="utf-8").read().split("MAX, MIN1 =")[0]
exec(compile(src_t.replace("__file__",repr(os.path.abspath("test_asm.py"))),"h","exec"))
rnd=random.Random(int(sys.argv[1]) if len(sys.argv)>1 else 1)
def num(): return str(rnd.choice([0,1,2,3,5,7,10,100]))
def ex(d,names):
    if d==0 or rnd.random()<0.3: return rnd.choice(names) if names and rnd.random()<0.7 else num()
    a=ex(d-1,names); b=ex(d-1,names)
    k=rnd.random()
    if k<0.6: return "(%s %s %s)"%(a,rnd.choice(["+","-","*"]),b)
    if k<0.8: return "(%s %s %s)"%(a,rnd.choice(["<",">","="]),b)
    return "((%s %s) ' %d)"%(a,b,rnd.choice([0,1]))
def prog():
    n=rnd.randint(1,4); names=[]; lines=[]
    kind=rnd.choice(["val","val","fn","str"])  # 出力を含む定義は std の import が要る。fuzz_effdef.py が受け持つ
    for i in range(n):
        nm="c%d"%i
        lines.append("%s : %s"%(nm,ex(2,names))); names.append(nm)
    if kind=="fn":
        lines.append("f : x ? %s"%ex(2,names+["x"])); last="f %s"%ex(1,names)
    elif kind=="str":
        lines.append("s : `ab`"); last="println s"
    else: last=ex(3,names)
    return "\n".join(lines)+"\n"+last+"\n"
bad=[];n=0;refused={}
for i in range(int(sys.argv[2]) if len(sys.argv)>2 else 300):
    s=prog()
    try: want=interp(s)
    except Exception: continue
    try: got=run_asm(sign_asm.generate(sign_interp.parse_source(s)))
    except sign_asm.AsmError as e: refused[str(e)[:50]]=refused.get(str(e)[:50],0)+1; continue
    except Exception as e: got=("例外",str(e)[:40])
    n+=1
    if got!=want: bad.append((s,want,got))
print("比べた",n,"断り",sum(refused.values()),"食い違い",len(bad))
for k,v in sorted(refused.items(),key=lambda x:-x[1])[:5]: print("  断り",v,k)
for s,w,g in bad[:10]: print(repr(s),"\n   処理系",w,"asm",g)
