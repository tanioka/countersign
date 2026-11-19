import sys,re
def fix(src):
    lines=src.split("\n"); out=[]; cur_def=block=blank=False; bd=0
    def dc(t):
        d=0;ins=False;k=0;col=False
        while k<len(t):
            ch=t[k]
            if ch=="\\" and not ins: k+=2; continue
            if ch=="`": ins=not ins
            elif not ins:
                if ch in "([{": d+=1
                elif ch in ")]}": d-=1
                elif ch==":" and d==0: col=True
            k+=1
        return d,col
    for ln in lines:
        if not ln.strip():
            if block: blank=True
            out.append(ln); continue
        if bd>0: bd+=dc(ln)[0]; out.append(ln); continue
        if ln[0]=="\t":
            if cur_def: block=True; blank=False
            out.append(ln); continue
        if ln[0]==" ": out.append(ln); continue
        if ln.strip().startswith("`") and (ln.strip().find("`",1)==-1 or True) and re.match(r"^`",ln.strip()) and ln.strip().count("`")%2==0 and ln.strip().endswith("`") is False:
            pass
        if cur_def and block and not blank:
            # コメント行の手前に空行を入れる(コメントの行は空行に数えない)
            out.append("")
        d,col=dc(ln.strip()); bd=max(d,0); cur_def=col and d<=0; block=blank=False
        out.append(ln)
    return "\n".join(out)
if __name__=="__main__":
    for p in sys.argv[1:]:
        s=open(p,encoding="utf-8").read(); t=fix(s)
        if t!=s: open(p,"w",encoding="utf-8").write(t); print("fixed",p)
