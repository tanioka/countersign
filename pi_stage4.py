"""Raspberry Pi 実機検証 第四段階: 装置(--real-dev)と並列実行(--par)。
  python3 pi_stage4.py make DIR      DIR に cases/NNN.s ほかと expected.json・run.sh を作る
  python3 pi_stage4.py compare DIR   実機の DIR/out を expected.json と突き合わせる(誤答があれば exit 1)
装置は外に何もつながなくても確かめられるもの(UART・時計・作業メモリ・ファイル・ループバックのネット・SQLite)だけ。
GPIO・I2C・SPI は、装置ファイルの有無を _dev.txt に記録するだけで、ピンは動かさない。
期待値は処理系(仮想装置)の出力。並列は直列の機械語と処理系の答えに合わせ、時間も記録する。"""
import sys, os, re, json, shutil, subprocess, tempfile
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import sign_asm, sign_interp

RUN_SH = r'''#!/bin/sh
# 実機(AArch64 の Linux)で cases/*.s を組んで実行する。out/NNN.out=標準出力, .rc=終了コード, .ms=実行ミリ秒, .fs=作業フォルダの出来上がり
cd "$(dirname "$0")" || exit 1
mkdir -p out build work
uname -m > out/_arch.txt; nproc > out/_nproc.txt 2>/dev/null; uname -r > out/_kernel.txt
( ls -l /dev/gpiochip* /dev/i2c-* /dev/spidev* /dev/fb0 /dev/input/event* 2>&1; ls /usr/include/sqlite3.h 2>&1; which gcc as ld sqlite3 2>&1 ) > out/_dev.txt
n=0
for s in cases/*.s; do
  b=$(basename "$s" .s)
  k=plain; [ -f cases/$b.kind ] && k=$(cat cases/$b.kind)
  rm -f build/$b
  case $k in
    plain) as -o build/$b.o "$s" 2>build/$b.err && ld -o build/$b build/$b.o 2>>build/$b.err ;;
    dev) as -o build/$b.o "$s" 2>build/$b.err && ld -Ttext-segment=0x10000000 -o build/$b build/$b.o 2>>build/$b.err ;;
    db) gcc -O2 -nostartfiles -no-pie -Wl,-Ttext-segment=0x10000000 -o build/$b "$s" sign_db.c -lsqlite3 2>build/$b.err ;;
  esac
  if [ -x build/$b ]; then
    rm -rf work/$b; mkdir -p work/$b
    [ -d cases/$b.files ] && cp -r cases/$b.files/. work/$b/
    inp=/dev/null; [ -f cases/$b.in ] && inp=$PWD/cases/$b.in
    t0=$(date +%s%N)
    ( cd work/$b && ulimit -s 8192; timeout 60 $PWD/../../build/$b < $inp > ../../out/$b.out 2>../../out/$b.err; echo $? > ../../out/$b.rc )
    t1=$(date +%s%N); echo $(( (t1 - t0) / 1000000 )) > out/$b.ms
    ( cd work/$b && for f in *; do [ -f "$f" ] && { echo "== $f"; cat "$f"; echo; }; done ) > out/$b.fs 2>/dev/null
  else echo BUILDFAIL > out/$b.out; echo 255 > out/$b.rc; echo 0 > out/$b.ms; cp build/$b.err out/$b.err 2>/dev/null; fi
  n=$((n+1))
done
echo "$n 件を実行" | tee out/_summary.txt
'''

def fib(n): return n if n < 2 else fib(n - 1) + fib(n - 2)

C = []     # dict(cat, name, src, kind, flags(処理系), par, stdin, files, expect(str | None=処理系に聞く), rx(正規表現で見る), timing, group)
def add(cat, name, src, kind="dev", flags=(), par=None, stdin=b"", files=None, expect=None, rx=None, timing=False, group=None, charset="ascii", norun=False):
    C.append(dict(cat=cat, name=name, src=src, kind=kind, flags=list(flags), par=par, stdin=stdin, files=files or {}, expect=expect, rx=rx, timing=timing, group=group, charset=charset))

def read_sn(n): return open(os.path.join(HERE, n), encoding="utf-8").read()

# ---- test_asm_real.py の字面を、そのまま借りる(装置の番地の使い方は、そちらで処理系と突き合わせ済み) ----
T = open(os.path.join(HERE, "test_asm_real.py"), encoding="utf-8").read().split("\n")
def lines(a, b): return "\n".join(T[a - 1:b])
ns = {"fake_kernel": None, "os": os, "tempfile": tempfile}
exec(lines(68, 68), ns)                                   # s32
s32 = ns["s32"]
_net = []
ns2 = dict(ns); ns2.update(netboth=lambda name, body, kind=None: (_net.append((name, body)), type('K', (), {'waits': None})())[1], NETFL=["--net=local"])
exec(lines(213, 219), ns2); ns2.update(check=lambda *a, **k: None); exec(lines(222, 258), ns2)      # NETH と 4 つの試験(netboth は集めるだけの版)
NETH = ns2["NETH"]
exec(lines(259, 261), ns2)                                # BIG と 3000 バイト
ns2.update(check=lambda *a, **k: None, k=None)
exec(lines(326, 342), ns)                                 # pokes, sysprog(s32 が要る)
ns.update(s32=s32)

# ---- UART・時計 ----
add("UART", "書いた文字が標準出力へ", "U : 0x9000000\nseq3 (U # 0x48) (U # 0x69) (U # 10)\n".replace("seq3", "s3 : a b c ? c\ns3"))
add("UART", "標準入力から 1 バイト", "U : 0x9000000\n@U\n", stdin=b"A")
add("UART", "入力の終わりは __", "U : 0x9000000\n@U\n")
add("UART", "utf32: 幅 4 の書き込みは UTF-8", "U : 4x09000000\nch : 0u3042\ns2 : a b ? b\ns2 (U # ch) (U # 0u000A)\n", charset="utf32")
add("時計", "SLEEP 250+100 ms のあと NOW は約 350", "s3 : a b c ? c\nT : 0x9200000\ns3 ((T + 4) # 250) ((T + 4) # 100) (@T)\n", rx=r"^3[5-9]\d\n$", expect="~")
CON = 'seq2 : a b ? b\nseq3 : a b c ? c\nseq4 : a b c d ? d\nCNT : 0x7C0000\nTM : 0x9200000\nU : 0x9000000\ninit : z ? seq4 (CNT # 0) ((TM + 0x08) # 7) ((TM + 0x10) # 100) ((TM + 0x08) # 9)\non_timer : id ?\n\tid = 7 : seq3 (CNT # ((@CNT) + 1)) (U # (0x30 + (@CNT))) (cont id)\n\t0\ncont : id ?\n\t(@CNT) >= 3 : -1\n\t0\ntick : z ? seq2 (U # 0x2E) 0\n'
add("時計", "アラーム: 100 ms ごとの EVERY がゲーム機と同じ順に鳴る(3 回で終わる)", CON, timing=True, expect="console")
# ---- 作業メモリ(低い番地) ----
add("メモリ", "低い番地(0x500000, 0x7C0000)の書き読み", "s2 : a b ? b\ns2 (0x500000 # 7) (s2 (0x7C0000 # 9) ((@0x500000) * 100 + (@0x7C0000)))\n")
add("メモリ", "作業メモリの端(0x8FFFFF8)", "s2 : a b ? b\ns2 (0x8FFFFF8 # 123) (@0x8FFFFF8)\n")
add("メモリ", "装置でない番地は今までどおり", "s2 : a b ? b\ns2 (0x7C0000 # 5) (@0x7C0000)\n")
add("メモリ", "未対応の装置(0x9B00008)は書きを捨て読みは 0(実機の道の決め。処理系の仮想装置は 5 を返す)", "s2 : a b ? b\ns2 (0x9B00008 # 5) (@0x9B00008)\n", expect="0\n")
# ---- ファイル(sys 装置) ----
SYSA = ns["sysprog"]({"o": "o.txt", "n": "nofile", "e": "../x", "a": "/etc/passwd"},
 "t : z ? seq3 (init 0) (hello 0) (t1 (sc 3 O 5 1))\n"
 "t1 : f ? seq5 (pi (isfd f)) (pi (sc 2 f BUF 5)) (pi (sc 4 f 0 0)) (pi (sc 7 O 5 0)) (t2 (sc 3 O 5 2))\n"
 "t2 : f ? seq6 (pi (isfd f)) (pi (sc 2 f BUF 5)) (pi (sc 4 f 0 0)) (pi (sc 7 O 5 0)) (t3 (sc 3 O 5 0)) 0\n"
 "t3 : f ? seq6 (pi (sc 1 f B2 100)) (pi (@B2)) (pi (@(B2 + 36))) (pi (sc 4 f 0 0)) (pi (sc 4 f 0 0)) (t4 0)\n"
 "t4 : z ? seq9 (pi (sc 3 N 6 0)) (pi (sc 3 E 4 0)) (pi (sc 3 A 11 0)) (pi (sc 3 O 5 3)) (pi (sc 3 O 0 0)) (pi (sc 1 77 B2 5)) (pi (sc 2 0 BUF 5)) (pi (sc 7 N 6 0)) (t5 0)\n"
 "t5 : z ? seq6 (pi (big (sc 5 0 0 0))) (pi (sc 1 0 B2 10)) (pi (sc 2 1 BUF 5)) (pi (sc 99 0 0 0)) (pi (sc 1 1 B2 5)) 0\n"
 "t 0\n")
add("ファイル", "書く・足す・読む・大きさ と エラー(外・無い・mode・fd)", SYSA, files={"seed.txt": b"x"}, flags=["--sys=@DIR"], group="sys")
SYSB = ns["sysprog"]({"o": "big.bin"},
 "fill : i ?\n\ti >= 6000 : 0\n\tseq2 ((BUF + i * 4) # (i % 251)) (fill (i + 1))\n"
 "t : z ? seq3 (init 0) (fill 0) (t1 (sc 3 O 7 1))\n"
 "t1 : f ? seq6 (pi (sc 2 f BUF 6000)) (pi (sc 4 f 0 0)) (pi (sc 7 O 7 0)) (t2 (sc 3 O 7 0)) 0 0\n"
 "t2 : f ? seq5 (pi (sc 1 f B2 6000)) (pi (@(B2 + 5999 * 4))) (pi (@(B2 + 4096 * 4))) (pi (sc 4 f 0 0)) 0\n"
 "t 0\n")
add("ファイル", "6000 バイトの書き読み", SYSB, flags=["--sys=@DIR"], group="sys")
# ---- ネット(ループバック) ----
for name, body in _net:
    add("ネット", name.replace("net: ", ""), NETH + body, flags=["--net=local"])
add("ネット", "3000 バイトの送受信", NETH + ns2["BIG"] + (
 "t : z ? seq3 (host9 0) (fill 0) (t1 (nc 5 0 5 0 0 0 0))\n"
 "t1 : l ? t2 l (nc 12 l 0 0 0 0 0)\n"
 "t2 : l p ? t3 l (nc 1 H 9 p 0 0 0)\n"
 "t3 : l c ? t4 l c (nc 6 l 0 0 0 0 0)\n"
 "t4 : l c a ? seq5 (pi (nc 2 c BUF 3000 0 0 0)) (pi (drain a 0)) (pi (@(B2 + 2999 * 4))) (pi (@(B2 + 1000 * 4))) 0\n"
 "t 0\n"), flags=["--net=local"])
# ---- SQLite ----
add("DB", "sqlite_demo.sn", read_sn("sqlite_demo.sn"), kind="db", flags=["--db=@DIR"])
add("DB", "日本語と 4294967295・ファイルの DB(utf32)", "`sqlite.sn`@~\nseq9x : a b c d e f g h i ? i\n"
    "t : z ? t1 (db_open `jp.db` 0)\n"
    "t1 : h ? seq9x (db_exec h `create table w(id integer primary key, s text, n integer)`) (db_exec h `insert into w(s,n) values ('こんにちは', 4294967295), ('abc', -5)`) (t2 h (db_prep h `select s, n from w order by id`)) 0 0 0 0 0 0\n"
    "t2 : h s ? seq5 (db_step s) (db_print_row s) (db_step s) (db_print_row s) (db_close h)\n"
    "t 0\n", kind="db", flags=["--db=@DIR"], charset="utf32", rx=r"(?s).*", expect="~", group="info")
# ---- 並列 ----
FIB = "fib : n ?\n\tn < 2 : n\n\t(fib (n - 1)) + (fib (n - 2))\n"
PAR = [
    ("fib 30 + fib 31", FIB + "(fib 30) + (fib 31)\n", fib(30) + fib(31)),
    ("fib 32(再帰の中で分ける)", FIB + "fib 32\n", fib(32)),
    ("積 fib 26 * fib 27", FIB + "(fib 26) * (fib 27)\n", fib(26) * fib(27)),
    ("連なり 4 個", FIB + "(fib 28) + (fib 29) + (fib 30) + (fib 27)\n", fib(28) + fib(29) + fib(30) + fib(27)),
    ("2 引数", "g : a b ?\n\ta < 1 : b\n\t(g (a - 1) (b + 1)) + (g (a - 1) (b + 2))\ng 22 0\n", None),
    ("実引数の呼びどうし", FIB + "ad : a b ? a - b\nad (fib 31) (fib 30)\n", fib(31) - fib(30)),
    ("0 で割る(__)", FIB + "z : n ? n - n\n(fib 12) / (z 5)\n", None),
    ("軽い(直列に戻る)", FIB + "(fib 3) + (fib 4)\n", fib(3) + fib(4)),
]
def g2(a, b):    # 2 引数の見本の値
    return b if a < 1 else g2(a - 1, b + 1) + g2(a - 1, b + 2)
for nm, src, want in PAR:
    if nm == "2 引数": want = g2(14, 0); src = src.replace("g 22 0", "g 14 0")
    w = None if want is None else "%d\n" % want
    for par in (None, 2, 4):
        add("並列", "%s [%s]" % (nm, "直列" if par is None else "par=%d" % par), src, kind="plain", par=par, expect=w, group=nm)

def interp_out(c):
    src = c["src"]
    if "seq" in src and "std.sn" not in src and "`sqlite.sn`" not in src: src = "`std.sn`@~\n" + src
    d = tempfile.mkdtemp()
    for f in ("std.sn", "aht25.sn", "mqtt.sn", "sqlite.sn"): os.symlink(os.path.join(HERE, f), os.path.join(d, f))
    for n, b in c["files"].items(): open(os.path.join(d, n), "wb").write(b)
    p = os.path.join(d, "t.sn"); open(p, "w", encoding="utf-8").write(src)
    if c["expect"] == "console":
        r = subprocess.run([sys.executable, os.path.join(HERE, "sign_console.py"), p, "--display=null", "--timer=virtual"], capture_output=True, timeout=120, stdin=subprocess.DEVNULL, cwd=d)
        return r.stdout.decode("utf-8", "replace")
    fl = [f.replace("@DIR", d) for f in c["flags"]]
    r = subprocess.run([sys.executable, os.path.join(HERE, "sign.py"), p] + fl, capture_output=True, timeout=300, input=c["stdin"], cwd=d)
    out = r.stdout.decode("utf-8", "replace")
    files = {n: open(os.path.join(d, n), "rb").read() for n in sorted(os.listdir(d)) if n not in ("std.sn", "aht25.sn", "mqtt.sn", "sqlite.sn", "t.sn") and os.path.isfile(os.path.join(d, n)) and not os.path.islink(os.path.join(d, n))}
    return out, files

def make(d):
    os.makedirs(os.path.join(d, "cases"), exist_ok=True)
    sign_asm.IMPORT_DIR[0] = HERE
    rows = []; bad = []
    for k, c in enumerate(C):
        idx = "%03d" % k; src = c["src"]
        if "seq" in src and "std.sn" not in src and "`sqlite.sn`" not in src: src = "`std.sn`@~\n" + src
        try:
            asm = sign_asm.generate(sign_interp.parse_source(src), "linux", charset=c["charset"], real_dev=c["kind"] in ("dev", "db"), real_db=c["kind"] == "db", par=c["par"])
        except Exception as e:
            bad.append((idx, c["name"], "生成が断る: " + str(e)[:80])); continue
        open(os.path.join(d, "cases", idx + ".s"), "w", encoding="utf-8").write(asm)
        open(os.path.join(d, "cases", idx + ".kind"), "w").write(c["kind"])
        if c["stdin"]: open(os.path.join(d, "cases", idx + ".in"), "wb").write(c["stdin"])
        if c["files"]:
            os.makedirs(os.path.join(d, "cases", idx + ".files"), exist_ok=True)
            for n, b in c["files"].items(): open(os.path.join(d, "cases", idx + ".files", n), "wb").write(b)
        exp, files = c["expect"], None
        if exp is None or exp in ("console",):
            r = interp_out(c)
            if isinstance(r, tuple): exp, files = r
            else: exp = r
        elif exp == "~": pass
        want_fs = None if files is None else {n: b.decode("latin-1") for n, b in files.items()}
        rows.append(dict(idx=idx, cat=c["cat"], name=c["name"], kind=c["kind"], expect=exp, rx=c["rx"], timing=c["timing"], group=c["group"], par=c["par"], fs=want_fs,
                         strip_zero=(c["expect"] == "console")))
    json.dump(rows, open(os.path.join(d, "expected.json"), "w"), ensure_ascii=False, indent=1)
    open(os.path.join(d, "run.sh"), "w", newline="\n").write(RUN_SH)
    shutil.copy(os.path.join(HERE, "sign_db.c"), os.path.join(d, "sign_db.c"))
    print("%d 件を %s に作りました。生成が断ったもの: %d 件" % (len(rows), d, len(bad)))
    for b in bad: print("  ", b)

def compare(d):
    rows = json.load(open(os.path.join(d, "expected.json")))
    out = os.path.join(d, "out")
    rd = lambda n, m="r": open(os.path.join(out, n), m, encoding="utf-8", errors="replace").read() if os.path.exists(os.path.join(out, n)) else ""
    res = {}; ms = {}; detail = []
    for r in rows:
        i = r["idx"]; got = rd(i + ".out"); rc = int(rd(i + ".rc").strip() or 255); t = int(rd(i + ".ms").strip() or 0); ms[i] = t
        if got.startswith("BUILDFAIL"): st = "組めず"
        elif rc == 124: st = "時間切れ"
        elif rc > 128: st = "異常終了"
        else:
            want = r["expect"]
            if r["strip_zero"] and got.endswith("0\n"): got = got[:-2]
            ok = bool(re.search(r["rx"], got)) if r["rx"] else got == want
            if ok and r["fs"] is not None:
                fsout = rd(i + ".fs")
                ok = all(("== %s\n%s\n" % (n, b)) in fsout for n, b in r["fs"].items()) if r["fs"] else True
            st = "一致" if ok else ("差(時間)" if r["timing"] else "誤答")
            if not ok: detail.append((i, r["name"], rc, repr(want)[:200], repr(got)[:200]))
        if r["group"] == "info": detail.append((i, r["name"], "出力(参考)", repr(got)[:200]))
        res.setdefault(r["cat"], {}).setdefault(st, 0); res[r["cat"]][st] += 1
        if st not in ("一致",): detail.append((i, r["cat"], r["name"], st, rc, rd(i + ".err")[:160]))
    tot = {}
    for c_, m in res.items():
        for s, n in m.items(): tot[s] = tot.get(s, 0) + n
    print(tot)
    for c_, m in res.items(): print("  %s: %s" % (c_, m))
    for x in detail: print("  詳細:", x)
    print("\n並列(ミリ秒。直列 → par=2 → par=4。実機 nproc=%s)" % rd("_nproc.txt").strip())
    g = {}
    for r in rows:
        if r["cat"] == "並列": g.setdefault(r["group"], {})[r["par"]] = ms[r["idx"]]
    for nm, v in g.items():
        s = v.get(None, 0); print("  %-28s %6d → %6d → %6d  (par=2 %.2f 倍, par=4 %.2f 倍)" % (nm, s, v.get(2, 0), v.get(4, 0), s / max(v.get(2, 1), 1), s / max(v.get(4, 1), 1)))
    print("\n装置ファイル:\n" + rd("_dev.txt"))
    wrong = tot.get("誤答", 0)
    print("誤答: %d" % wrong); return 1 if wrong else 0

if __name__ == "__main__":
    if len(sys.argv) >= 3 and sys.argv[1] == "make": make(sys.argv[2])
    elif len(sys.argv) >= 3 and sys.argv[1] == "compare": sys.exit(compare(sys.argv[2]))
    else: print(__doc__)
