"""test_fmt.py — sign_fmt.py(Float の十進表記を書く AArch64 ルーチン)の試験。
同じ手順の Python 版(下の ref: Burger–Dybvig の free-format)が、処理系の `repr`(binary64)・`f32_repr`(binary32)と一致するかを
乱数 12 万件で確かめ(--ref)、そのうえで asm のルーチンをエミュレータで動かして Python 版と突き合わせる(既定は端の値と乱数を数百件。
`python3 test_fmt.py 7 250` で 777 件)。"""
import os, random, struct, sys
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from sign_interp import f32_repr
import sign_fmt
_ns = {"__file__": os.path.join(HERE, "test_asm.py")}
exec(compile(open(os.path.join(HERE, "test_asm.py"), encoding="utf-8").read().split("MAX, MIN1 =")[0], "test_asm_head", "exec"), _ns)
Cpu = _ns["Cpu"]
def decompose(bits, f32):
    if f32:
        sign=bits>>31; ex=(bits>>23)&0xFF; fr=bits&0x7FFFFF; P=24; BIAS=150; EMAX=0xFF
    else:
        sign=bits>>63; ex=(bits>>52)&0x7FF; fr=bits&((1<<52)-1); P=53; BIAS=1075; EMAX=0x7FF
    return sign,ex,fr,P,BIAS,EMAX
def shortest(bits, f32):
    sign,ex,fr,P,BIAS,EMAX=decompose(bits,f32)
    if ex==0: f=fr; e=1-BIAS
    else: f=fr|(1<<(P-1)); e=ex-BIAS
    minexp = (ex<=1)
    even = (f&1)==0
    if e>=0:
        if f!=(1<<(P-1)): r=f<<(e+1); s=2; mp=1<<e; mm=1<<e
        else: r=f<<(e+2); s=4; mp=1<<(e+1); mm=1<<e
    else:
        if minexp or f!=(1<<(P-1)): r=f<<1; s=1<<(1-e); mp=1; mm=1
        else: r=f<<2; s=1<<(2-e); mp=2; mm=1
    bl=f.bit_length()
    k=(((e+bl-1)*78913)>>18)   # floor(log10(2^(e+bl-1))) approx (may be off by one low)
    # scale so that value = 0.d... * 10^(k+1)?  start with k as estimate of floor(log10 v)
    if k>=0: s*=10**k
    else:
        t=10**(-k); r*=t; mp*=t; mm*=t
    # fixup: need (r+mp)/s < 1 (or <= if even handled below) ; high = r+mp
    while True:
        hi=r+mp
        if hi>s or (even and hi==s): k+=1; s*=10      # too big -> scale s
        else: break
    # now value*10^-k  in [0.1?,1) after multiply: ensure first digit nonzero
    while True:
        hi=(r+mp)*10
        if hi<s or (not even and hi==s):   # r+mp < s/10 : too small
            k-=1; r*=10; mp*=10; mm*=10
        else: break
    out=[]
    while True:
        r*=10; mp*=10; mm*=10
        d,r=divmod(r,s)
        tc1 = r<mm or (even and r==mm)
        tc2 = r+mp>s or (even and r+mp==s)
        if not tc1 and not tc2: out.append(d); continue
        if tc1 and not tc2: out.append(d)
        elif tc2 and not tc1: out.append(d+1)
        else: out.append(d if (2*r<s or (2*r==s and d%2==0)) else d+1)
        break
    # carry propagate if d+1==10
    i=len(out)-1
    while i>=0 and out[i]==10:
        out[i]=0
        if i==0: out.insert(0,1); k+=1; break
        out[i-1]+=1; i-=1
    # strip trailing zeros? (shortest wont have unless carry)
    while len(out)>1 and out[-1]==0: out.pop()
    return out,k
def fmt(bits,f32):
    sign,ex,fr,P,BIAS,EMAX=decompose(bits,f32)
    sg="-" if sign else ""
    if ex==EMAX: return "nan" if fr else sg+"inf"
    if ex==0 and fr==0: return sg+"0.0"
    ds,k=shortest(bits,f32); n=len(ds); x=k-1; s="".join(map(str,ds))
    if -4<=x<16:
        if x>=0:
            ip=s[:x+1].ljust(x+1,"0"); fp=s[x+1:] or "0"; return sg+ip+"."+fp
        return sg+"0."+"0"*(-x-1)+s
    m=s[0]+("."+s[1:] if n>1 else "")
    return sg+m+"e"+("-" if x<0 else "+")+"%02d"%abs(x)

TEXT = "\t.text\n" + sign_fmt.routine() + sign_fmt.data()
def run_asm_fmt(bits, f32):
    c = Cpu(TEXT); c.r["x0"] = bits; c.r["x1"] = 1 if f32 else 0; c.r["x2"] = 0x400000; c.r["sp"] = 0x7fff0000
    c.run("_sign_fmt_float", limit=20_000_000)
    return bytes(c.mem.get(0x400000 + i, 0) for i in range(c.r["x0"])).decode()

if __name__ == "__main__":
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1; N = int(sys.argv[2]) if len(sys.argv) > 2 else 40
    bad = 0; rnd = random.Random(seed)
    # 1. Python 版 = repr / f32_repr(端の値と乱数)
    for i in range(6000):
        x = struct.unpack("<d", struct.pack("<Q", rnd.getrandbits(64)))[0] if i % 2 else rnd.uniform(-1000, 1000)
        if i % 7 == 0: x = float(rnd.randint(-10 ** 6, 10 ** 6)) / rnd.choice([1, 10, 100, 3, 7])
        b = struct.unpack("<Q", struct.pack("<d", x))[0]
        if repr(x) != fmt(b, False): bad += 1; print("NG ref f64", repr(x), fmt(b, False))
        y = struct.unpack("<f", struct.pack("<I", rnd.getrandbits(32)))[0] if i % 2 else struct.unpack("<f", struct.pack("<f", rnd.uniform(-100, 100)))[0]
        b = struct.unpack("<I", struct.pack("<f", y))[0]
        if f32_repr(y) != fmt(b, True): bad += 1; print("NG ref f32", repr(y), fmt(b, True))
    print("Python 版と repr / f32_repr: 12000 件、不一致", bad)
    # 2. asm のルーチン = Python 版
    cases = [(struct.unpack("<Q", struct.pack("<d", x))[0], False) for x in [0.0, -0.0, 1.0, 0.1, 3.14, 1e22, 1e-5, 5e-324, 1.7976931348623157e308, float("inf"), float("-inf"), float("nan"), 123456789012345678.0, 0.0001, 12345.678, 2.5e-5, 1e16, 9999999999999998.0]]
    cases += [(struct.unpack("<I", struct.pack("<f", x))[0], True) for x in [1.5, 0.1, 0.6666667, 1e-45, 3.4028235e38, 16777216.0, 2617107.25, 1e-5, 123456.79]]
    for _ in range(N):
        cases.append((struct.unpack("<Q", struct.pack("<d", rnd.uniform(-1000, 1000)))[0] if rnd.random() < .5 else rnd.getrandbits(64), False))
        cases.append((struct.unpack("<I", struct.pack("<f", rnd.uniform(-100, 100)))[0], True)); cases.append((rnd.getrandbits(32), True))
    b0 = bad
    for b, f in cases:
        g = run_asm_fmt(b, f); w = fmt(b, f)
        if g != w: bad += 1; print("NG asm", hex(b), f, "得た", g, "期待", w)
    print("asm のルーチンと Python 版: %d 件、不一致 %d" % (len(cases), bad - b0))
    print("全部 ok" if not bad else "%d 件 NG" % bad); sys.exit(1 if bad else 0)
