"""第三段階: AArch64 実機検証。整数オーバーフロー・関数呼出し・メモリ境界・末尾再帰の最小プログラム。
  python3 pi_stage3.py make DIR        DIR に cases/NNN.s・expected.tsv・run.sh を作る(作る前に strict 評価器とエミュレータでも照合する)
  python3 pi_stage3.py compare DIR     実機の出力(DIR/out)を期待値と突き合わせる
期待値: 整数の算術は Python の厳密な計算から(値域 ±(2^63-1) の外なら罠)、そのほかは strict 評価器の答え。
重い形(百万〜千万回の末尾再帰など)は、評価器・エミュレータでは重いので、同じ形の小さな回数で 3 者(期待値・評価器・エミュレータ)を確かめ、実機は閉じた式の期待値と照らす。
分類: 一致 / 罠(wfi。実機ではタイムアウトで見える。期待値が罠なら一致) / 異常終了(スタック溢れなどの signal。答えを出さないので許容、ただし記録) / 誤答。"""
import sys, os, json
import sign_interp as S, sign_asm, fuzz_sir as F
from fixblank import fix
MAX = 2 ** 63 - 1

def arith(op, a, b):
    r = {"+": a + b, "-": a - b, "*": a * b}[op]
    return ("trap",) if abs(r) > MAX else ("val", r)

C = []   # (category, name, source, expected or None(=評価器が答え), heavy?, mode "s"=strict / "d"=既定, noeval=評価器と比べない)
def add(cat, name, src, exp=None, heavy=False, mode="s", noeval=False): C.append((cat, name, src, exp, heavy, mode, noeval))

# --- 整数オーバーフロー(値域 ±(2^63-1): 内側は答え、外側は罠)
for nm, op, a, b in [
    ("最大 + 0", "+", MAX, 0), ("最大 - 1 + 1", "+", MAX - 1, 1), ("最大 + 1", "+", MAX, 1), ("最大 + 最大", "+", MAX, MAX),
    ("最小 - 0", "-", -MAX, 0), ("最小 + 1 - 1", "-", -MAX + 1, 1), ("最小 - 1", "-", -MAX, 1), ("最小 - 最大", "-", -MAX, MAX),
    ("2^62 * 2", "*", 2 ** 62, 2), ("2^62 * 1", "*", 2 ** 62, 1), ("3037000499^2", "*", 3037000499, 3037000499), ("3037000500^2", "*", 3037000500, 3037000500),
    ("最大 * 1", "*", MAX, 1), ("最大 * -1", "*", MAX, -1), ("最小 * -1", "*", -MAX, -1), ("最大 * 最大", "*", MAX, MAX), ("最大 * 0", "*", MAX, 0),
]:
    sa = f"({a})" if a < 0 else str(a); sb = f"({b})" if b < 0 else str(b)
    add("整数", nm, f"{sa} {op} {sb}\n", arith(op, a, b))
add("整数", "符号反転(最大)", f"g : x ? -x\ng {MAX}\n", ("val", -MAX))
add("整数", "符号反転(最小)", f"g : x ? -x\ng {-MAX}\n", ("val", MAX))
add("整数", "除算 0 は void", "7 / 0\n", ("void",))
add("整数", "剰余 0 は void", "7 % 0\n", ("void",))
add("整数", "最大 / 2", f"{MAX} / 2\n")
add("整数", "負の除算", "(0 - 7) / 2\n")
add("整数", "負の剰余", "(0 - 7) % 3\n")
add("整数", "累積で溢れる(3^39 まで)", "p : n acc ?\n\tn = 0 : acc\n\tp (n - 1) (acc * 3)\np 39 1\n", ("val", 3 ** 39))
add("整数", "累積で溢れる(3^40)", "p : n acc ?\n\tn = 0 : acc\n\tp (n - 1) (acc * 3)\np 40 1\n", ("trap",) if 3 ** 40 > MAX else ("val", 3 ** 40))
add("整数", "累積で溢れる(3^41)", "p : n acc ?\n\tn = 0 : acc\n\tp (n - 1) (acc * 3)\np 41 1\n", ("trap",))
add("整数", "関数の中で溢れる", f"f : x ? x + x\nf {MAX}\n", ("trap",))
add("整数", "関数の中で溢れない", f"f : x ? x + x\nf {MAX // 2}\n", ("val", (MAX // 2) * 2))
# --- 関数呼出し
add("呼出し", "実引数 8 個(レジスタ)", "f : a b c d e g h i ? a + b * 2 + c * 3 + d * 4 + e * 5 + g * 6 + h * 7 + i * 8\nf 1 2 3 4 5 6 7 8\n", ("val", 1 + 4 + 9 + 16 + 25 + 36 + 49 + 64))
add("呼出し", "実引数 9 個(スタックへ溢れる)", "f : a b c d e g h i j ? a + b * 2 + c * 3 + d * 4 + e * 5 + g * 6 + h * 7 + i * 8 + j * 9\nf 1 2 3 4 5 6 7 8 9\n", ("val", sum(i * i for i in range(1, 10))))
add("呼出し", "実引数 12 個", "f : a b c d e g h i j k l m ? a + b + c + d + e + g + h + i + j + k + l + m\nf 1 2 3 4 5 6 7 8 9 10 11 12\n", ("val", 78))
add("呼出し", "入れ子の呼び(実引数が呼び)", "g : x ? x * 2\nh : x y ? x - y\nh (g 10) (g (g 3))\n", ("val", 20 - 12))
add("呼出し", "呼びの値を使い回す", "g : x ? x + 1\nf : a ? (g a) * (g a) + (g (a + 1))\nf 5\n", ("val", 36 + 7))
add("呼出し", "相互再帰(偶奇、深さ 1000)", "ev : n ?\n\tn = 0 : 1\n\tod (n - 1)\nod : n ?\n\tn = 0 : 0\n\tev (n - 1)\nev 1000\n", ("val", 1))
add("呼出し", "フィボナッチ 20", "fib : n ?\n\tn < 2 : n\n\t(fib (n - 1)) + (fib (n - 2))\nfib 20\n", ("val", 6765))
add("呼出し", "アッカーマン (2, 3)", "ack : m n ?\n\tm = 0 : n + 1\n\tn = 0 : ack (m - 1) 1\n\tack (m - 1) (ack m (n - 1))\nack 2 3\n", ("val", 9))
add("呼出し", "アッカーマン (3, 3)", "ack : m n ?\n\tm = 0 : n + 1\n\tn = 0 : ack (m - 1) 1\n\tack (m - 1) (ack m (n - 1))\nack 3 3\n", ("val", 61))
add("呼出し", "深い非末尾再帰 10000", "s : n ?\n\tn = 0 : 0\n\tn + (s (n - 1))\ns 10000\n", ("val", 10000 * 10001 // 2), noeval=True)
add("呼出し", "深い非末尾再帰 100000", "s : n ?\n\tn = 0 : 0\n\tn + (s (n - 1))\ns 100000\n", ("val", 100000 * 100001 // 2), heavy=True, noeval=True)
add("呼出し", "深い非末尾再帰 1000000", "s : n ?\n\tn = 0 : 0\n\tn + (s (n - 1))\ns 1000000\n", ("val", 1000000 * 1000001 // 2), heavy=True, noeval=True)
add("呼出し", "深い非末尾再帰 100000000", "s : n ?\n\tn = 0 : 0\n\tn + (s (n - 1))\ns 100000000\n", ("val", 100000000 * 100000001 // 2), heavy=True, noeval=True)
# --- メモリ境界(リストの添字・長さ・切り出し)
L10 = "l : 10 20 30 40 50\n"
for nm, ex, exp in [("先頭", "l ' 0", ("val", 10)), ("最後", "l ' 4", ("val", 50)), ("範囲の外(5)", "l ' 5", ("void",)), ("負の最後(-1)", "l ' -1", ("val", 50)), ("負の先頭(-5)", "l ' -5", ("val", 10)), ("負の外(-6)", "l ' -6", ("void",)), ("大きな添字", "l ' 1000000", ("void",)), ("長さ", "||l||", ("val", 5))]:
    add("メモリ", "リスト " + nm, L10 + ex + "\n", exp, mode="d")
add("メモリ", "切り出し(先頭から 2 個)", L10 + "||(l ' [0 ~ 1])||\n", ("val", 2), mode="d")
add("メモリ", "切り出し(範囲が末尾を越える)", L10 + "||(l ' [3 ~ 10])||\n", mode="d")
add("メモリ", "切り出し(全部の外)", L10 + "||(l ' [7 ~ 9])||\n", mode="d")
add("メモリ", "計算した添字(外)", L10 + "g : i ? l ' (i * 2)\ng 3\n", ("void",), mode="d")
add("メモリ", "計算した添字(中)", L10 + "g : i ? l ' (i * 2)\ng 2\n", ("val", 50), mode="d")
add("メモリ", "大きなリストの合計(1000 個)", "l : " + " ".join(str(i) for i in range(1, 1001)) + "\nsum : xs i acc ?\n\ti >= ||xs|| : acc\n\tsum xs (i + 1) (acc + (xs ' i))\nsum l 0 0\n", ("val", 500500), mode="d")
add("メモリ", "大きなリストの最後の添字", "l : " + " ".join(str(i) for i in range(1, 1001)) + "\nl ' 999\n", ("val", 1000), mode="d")
add("メモリ", "大きなリストの外の添字", "l : " + " ".join(str(i) for i in range(1, 1001)) + "\nl ' 1000\n", ("void",), mode="d")
# --- 末尾再帰(小さな回数は 3 者で、大きな回数は実機で閉じた式と)
for n, heavy in [(1000, False), (100000, True), (1000000, True), (10000000, True), (100000000, True)]:
    add("末尾再帰", f"和 {n}", f"sum : n acc ?\n\tn = 0 : acc\n\tsum (n - 1) (acc + n)\nsum {n} 0\n", ("val", n * (n + 1) // 2), heavy=heavy)
add("末尾再帰", "2 つの累積 1000000", "f : n a b ?\n\tn = 0 : a - b\n\tf (n - 1) (a + 2) (b + 1)\nf 1000000 0 0\n", ("val", 1000000), heavy=True)
add("末尾再帰", "枝の中の末尾 1000000", "f : n acc ?\n\tn = 0 : acc\n\tn % 2 = 0 : f (n - 1) (acc + 1)\n\tf (n - 1) acc\nf 1000000 0\n", ("val", 500000), heavy=True)
add("末尾再帰", "相互の末尾呼び 1000(小)", "ev : n ?\n\tn = 0 : 1\n\tod (n - 1)\nod : n ?\n\tn = 0 : 0\n\tev (n - 1)\nev 1000\n", ("val", 1))
add("末尾再帰", "相互の末尾呼び 1000000", "ev : n ?\n\tn = 0 : 1\n\tod (n - 1)\nod : n ?\n\tn = 0 : 0\n\tev (n - 1)\nev 1000000\n", ("val", 1), heavy=True)
add("末尾再帰", "相互の末尾呼び 100000000", "ev : n ?\n\tn = 0 : 1\n\tod (n - 1)\nod : n ?\n\tn = 0 : 0\n\tev (n - 1)\nev 100000000\n", ("val", 1), heavy=True)
add("末尾再帰", "リストを持ち回る末尾 100000 回(添字)", "l : 1 2 3\nf : i acc ?\n\ti = 0 : acc\n\tf (i - 1) (acc + (l ' (i % 3)))\nf 100000 0\n", ("val", sum([1, 2, 3][i % 3] for i in range(1, 100001))), heavy=True, mode="d")

RUN_SH = r'''#!/bin/sh
# 実機(AArch64 の Linux)で cases/*.s を組んで実行する。out/NNN.out に標準出力、NNN.rc に終了コード(124=タイムアウト=罠の wfi、139=SIGSEGV など)、NNN.ms に実行ミリ秒
cd "$(dirname "$0")" || exit 1
mkdir -p out build
uname -m > out/_arch.txt; nproc > out/_nproc.txt 2>/dev/null
if command -v as >/dev/null 2>&1 && command -v ld >/dev/null 2>&1; then B=asld; elif command -v gcc >/dev/null 2>&1; then B=gcc; else echo "as/ld も gcc も無い" >&2; exit 2; fi
n=0
for s in cases/*.s; do
  b=$(basename "$s" .s)
  rm -f build/$b
  if [ "$B" = asld ]; then as -o build/$b.o "$s" 2>build/$b.err && ld -o build/$b build/$b.o 2>>build/$b.err; else gcc -nostdlib -static -o build/$b "$s" 2>build/$b.err; fi
  if [ -x build/$b ]; then
    t0=$(date +%s%N)
    ( ulimit -s 8192; timeout 20 ./build/$b > out/$b.out 2>out/$b.err; echo $? > out/$b.rc )
    t1=$(date +%s%N); echo $(( (t1 - t0) / 1000000 )) > out/$b.ms
  else echo BUILDFAIL > out/$b.out; echo 255 > out/$b.rc; echo 0 > out/$b.ms; fi
  n=$((n+1))
done
echo "$n 件を実行" | tee out/_summary.txt
'''

def obs_default(t):
    """既定の読み(strict でない)の評価器の観測"""
    import io
    S.STRICT_GATES = False
    try:
        S.MEMORY.clear(); S.WARNINGS.clear(); old = sys.stdout; sys.stdout = io.StringIO()
        try: r = S.run(t)
        finally: sys.stdout = old
        v = S.show(r[-1]) if r else "!_"
    except BaseException as e: return ("refuse", type(e).__name__)
    return ("void",) if v == "!_" else (("val", int(v)) if v.lstrip("-").isdigit() else ("other", v[:20]))

def emu_default(t):
    F.obs_asm("0\n")                                                 # エミュレータの準備
    sign_asm.STRICT[0] = False
    try:
        got = F._ns["run_asm"](sign_asm.generate(S.parse_source(t), "linux"), linux=True)
    except (sign_asm.AsmError, sign_asm.StrictRefusal) as e: return ("refuse", str(e)[:30])
    except Exception as e: return ("refuse", "例外 " + type(e).__name__)
    finally: sign_asm.STRICT[0] = True
    return F._got(got)

def make(d):
    os.makedirs(os.path.join(d, "cases"), exist_ok=True)
    rows = []; flags = []
    for k, (cat, nm, src, exp, heavy, mode, noeval) in enumerate(C):
        t = fix(src); idx = "%03d" % k
        a = F.obs_strict(t) if mode == "s" else obs_default(t)
        ws = sorted({k[0] for k in S.WARNINGS}) if a[0] != "refuse" else []        # 評価器が出した知らせの名前(観測の組の4つ目)
        try:
            if mode == "s":
                sign_asm.STRICT[0] = True
                tree, rest = sign_asm.strict_rewrite(S.parse_source(t))
                if rest: flags.append((idx, nm, "strict_rewrite が断る")); continue
                asm = sign_asm.generate(tree, "linux")
            else:
                sign_asm.STRICT[0] = False
                asm = sign_asm.generate(S.parse_source(t), "linux")
        except BaseException as e: flags.append((idx, nm, "生成が断る " + type(e).__name__ + str(e)[:50])); continue
        finally: sign_asm.STRICT[0] = True
        e = ("skip",) if heavy else (F.obs_asm(t, linux=True) if mode == "s" else emu_default(t))
        want = exp if exp is not None else (a if a[0] in ("val", "void") else None)
        if not noeval and not heavy and exp is not None and a[0] in ("val", "void") and a != exp:
            if not (exp == ("trap",) and a[0] in ("void", "val")): flags.append((idx, nm, f"[{mode}] 期待値 {exp} と評価器 {a} が食い違う"))
        if e[0] != "skip" and want is not None and e != want and not (want == ("trap",) and e[0] == "trap"):
            flags.append((idx, nm, f"[{mode}] 期待値 {want} とエミュレータ {e} が食い違う"))
        open(os.path.join(d, "cases", idx + ".s"), "w", encoding="utf-8").write(asm)
        rows.append([idx, cat, nm, json.dumps(want if want else ["refuse"]), json.dumps(a), json.dumps(e), "1" if heavy else "0", json.dumps(ws)])
    with open(os.path.join(d, "expected.tsv"), "w", encoding="utf-8") as f:
        for r in rows: f.write("\t".join(x.replace("\t", " ").replace("\n", " ") for x in r) + "\n")
    open(os.path.join(d, "run.sh"), "w", newline="\n").write(RUN_SH)
    print(f"{len(rows)} 件を {d} に作りました。実機の前に見つかった食い違い: {len(flags)} 件")
    for fl in flags: print("  ", fl)

def compare(d):
    from collections import Counter
    ob = Counter(); tot = Counter(); wrong = []; crash = []; slow = []; byc = {}
    norm = lambda x: tuple(tuple(y) if isinstance(y, list) else y for y in json.loads(x))
    for line in open(os.path.join(d, "expected.tsv"), encoding="utf-8"):
        cols = line.rstrip("\n").split("\t"); idx, cat, nm, want, a, e, heavy = cols[:7]
        ws = json.loads(cols[7]) if len(cols) > 7 else []
        want = norm(want)
        po = os.path.join(d, "out", idx + ".out")
        if not os.path.exists(po): tot["出力なし"] += 1; continue
        out = open(po, encoding="utf-8", errors="replace").read()
        rc = int(open(os.path.join(d, "out", idx + ".rc")).read().strip() or 0)
        ms = int(open(os.path.join(d, "out", idx + ".ms")).read().strip() or 0)
        if out.startswith("BUILDFAIL"): tot["組めず"] += 1; wrong.append((idx, cat, nm, "組めず")); continue
        if rc == 124: got, kind = ("trap",), "罠/タイムアウト"
        elif rc in (139, 138, 135, 134, 136) or rc > 128: got, kind = None, f"異常終了(rc={rc})"
        else:
            got = F._got(("exit", out)); kind = "答え"
        res = "一致"
        if got is None: res = "異常終了"; crash.append((idx, cat, nm, rc, ms))
        elif got[0] == "refuse": res = "断り"
        elif want == ("refuse",): res = "期待なし"
        elif got == want or (got[0] == "void" and want[0] == "void"): res = "一致"
        elif want == ("trap",) and got[0] == "trap": res = "一致"
        else: res = "誤答"; wrong.append((idx, cat, nm, f"期待 {want} / 実機 {got}(rc={rc})"))
        tot[res] += 1; byc.setdefault(cat, Counter())[res] += 1
        pe = os.path.join(d, "out", idx + ".err"); err = open(pe, encoding="utf-8", errors="replace").read() if os.path.exists(pe) else None
        if err is not None:                                          # 観測の4つ目(知らせ): 機械語が出せるのは溢れの information だけ。評価器の知らせは別に数える
            ov_e, ov_m = "int-overflow" in ws, "int-overflow" in err
            ob["溢れの知らせ 評価器あり・実機あり" if ov_e and ov_m else "溢れの知らせ 評価器あり・実機なし(A3 未決)" if ov_e else "溢れの知らせ 評価器なし・実機あり" if ov_m else "溢れの知らせ 両方なし"] += 1
            other = [w for w in ws if w != "int-overflow"]
            if other: ob["評価器だけの知らせ(機械語に出口なし)"] += 1
        if ms > 1000: slow.append((idx, nm, ms))
    print(dict(tot))
    if ob: print("観測の組(知らせ):", dict(ob))
    for c, k in byc.items(): print(f"  {c}: {dict(k)}")
    for c in crash: print("異常終了:", c)
    for w in wrong: print("誤答:", w)
    for s in slow: print("遅い(>1s):", s)
    print("誤答:", len([w for w in wrong]))
    return 1 if wrong else 0

if __name__ == "__main__":
    if sys.argv[1] == "make": make(sys.argv[2])
    elif sys.argv[1] == "compare": raise SystemExit(compare(sys.argv[2]))
