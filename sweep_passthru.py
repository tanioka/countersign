import sys, random, subprocess, tempfile, os, re
sys.path.insert(0,'/mnt/user-data/outputs')
src=open('/mnt/user-data/outputs/test_asm.py',encoding='utf-8').read()
ns={'__file__':'/mnt/user-data/outputs/test_asm.py','__name__':'emu'}
exec(compile(src[:src.index('# ---------------- 処理系の答え')],'emu','exec'),ns)
import sign_asm, sign_interp
T=[
"a : xs ys acc ?\n\t||ys|| < 2 : acc\n\tb xs (ys ' 1~) (acc~ (xs ' 0) {k})\nb : xs ys acc ?\n\t||ys|| < 2 : acc~ 9\n\ta xs (ys ' 1~) acc\na {xs} {ys} {acc}\n",
"a : xs ys acc ?\n\t||ys|| < 2 : acc\n\tb xs (ys ' 1~) acc\nb : xs ys acc ?\n\t||ys|| < 2 : acc~ 9\n\ta xs (ys ' 2~) (acc~ (xs ' 0) {k})\na {xs} {ys} {acc}\n",
"a : xs ys acc ?\n\t||ys|| < 2 : acc\n\tb xs (ys ' 1~) acc\nb : xs ys acc ?\n\t||ys|| < 2 : acc~ 9\n\tc xs (ys ' 1~) acc\nc : xs ys acc ?\n\t||ys|| < 3 : acc\n\ta xs (ys ' 1~) (acc~ (xs ' 0) {k})\na {xs} {ys} {acc}\n",
"a : s t acc ?\n\t||t|| < 2 : acc\n\tb s (t ' 1~) (acc `{c}`)\nb : s t acc ?\n\t||t|| < 2 : acc `!`\n\ta s (t ' 1~) acc\na `ab` `{t}` `{acc}`\n",
]
random.seed(int(sys.argv[1]) if len(sys.argv)>1 else 1)
bad=0; refused=0; n=0
for t in T:
    for _ in range(8):
        xs=" ".join(str(random.randint(1,9)) for _ in range(random.randint(1,4)))
        ys=" ".join(str(random.randint(1,9)) for _ in range(random.randint(0,9)) ) or "1"
        ys="("+ys+" 5)"
        acc="("+" ".join(str(random.randint(1,9)) for _ in range(random.randint(2,3)))+")"
        k=" ".join(str(random.randint(1,9)) for _ in range(random.randint(1,3)))
        txt=t.format(xs="("+xs+" 7)",ys=ys,acc=acc,k=k,c="x"*random.randint(1,2),t="z"*random.randint(0,8),**{}) if "{t}" in t or "{c}" in t else t.format(xs="("+xs+" 7)",ys=ys,acc=acc,k=k)
        d=tempfile.mkdtemp(); p=os.path.join(d,'t.sn'); open(p,'w').write(txt)
        want=subprocess.run([sys.executable,'/mnt/user-data/outputs/sign.py',p],capture_output=True,text=True).stdout
        try: asm=sign_asm.generate(sign_interp.parse_source(txt),'linux')
        except sign_asm.AsmError as e: refused+=1; continue
        try: got=ns['run_asm'](asm,linux=True)[1]
        except Exception as e: got="EXC "+str(e)
        n+=1
        if got!=want: bad+=1; print("NG",repr(txt),repr(got),repr(want))
print("ok",n,"refused",refused,"bad",bad)
