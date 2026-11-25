"""第二段階: strict の評価器・SIR の評価・生成した機械語(エミュレータ)の 3 者の観測を照合する。
観測(obs): ("val", 整数) / ("void",) / ("trap",) / ("refuse", 理由) / ("unsup", 理由)。
照合の問い 2 つ:
  前段 評価器 = SIR: SIR の下げ・評価が、strict の評価器と同じ答えか(SIR が意味を保存している証拠)
  後段 SIR = 機械語: 機械語が SIR と同じ答えか。断り・罠は許す(合っていない答えより良い)。答えを出して違えば「誤答」
使い方: python3 diff_observe.py [-v]      終了コード: 誤答があれば 1"""
import sys, os, io, collections
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); sys.setrecursionlimit(20000)
src = open(os.path.join(HERE, "test_asm.py"), encoding="utf-8").read()
ns = {"__file__": os.path.join(HERE, "test_asm.py"), "__name__": "emu"}
exec(compile(src[:src.index("# ---------------- 処理系の答え")], "emu", "exec"), ns)
import sign_asm, sign_interp as S, sign_sir as R
from fixblank import fix
sign_asm.STRICT[0] = True
verbose = "-v" in sys.argv

def obs_strict(t):
    S.STRICT_GATES = True
    try:
        S.MEMORY.clear(); S.WARNINGS.clear()
        old = sys.stdout; sys.stdout = io.StringIO()
        try: r = S.run(t)
        finally: sys.stdout = old
        v = S.show(r[-1]) if r else "!_"
    except BaseException as e: return ("refuse", type(e).__name__)
    finally: S.STRICT_GATES = False
    if v == "!_": return ("void",)
    if v.lstrip("-").isdigit(): return ("val", int(v))
    if len(v) >= 3 and v[0] == v[-1] == "`" and v[1:-1].isascii(): return ("str", v[1:-1])           # 文字列は `abc`
    if len(v) == 2 and v[0] == "\\" and v[1].isalnum() and v[1].isascii(): return ("chr", ord(v[1]))   # 文字は \a(英数字だけ見る)
    return ("unsup", "値 " + v[:20])

def obs_sir(t):
    try:
        f, top = R.lower(S.parse_source(t))
        if top is None: return ("unsup", "最後の行が無い")
        return R.evaluate(f, top) if False else (lambda r: ("unsup", "fuel") if r == ("fuel",) else r)(R.evaluate(f, top))
    except R.Unsup as e: return ("unsup", str(e))

def parse_exit(got):
    """linux 目標の実機の印字を観測にする。文字列・文字の答えは bare の戻り値(x0 の生の値)では読めない(Char の `__` は U+0000、文字列は番地)ので、印字を読む"""
    v = got[1].strip()
    if v == "__": return ("void",)
    if v.lstrip("-").isdigit(): return ("val", int(v))
    if len(v) >= 3 and v[0] == v[-1] == "`": return ("str", v[1:-1])
    if len(v) == 2 and v[0] == "\\" and v[1].isalnum(): return ("chr", ord(v[1]))
    return ("refuse", "印字 " + v[:20])

def obs_asm_sir(t, lin=False):
    """SIR を旧 AST に戻し、strict_rewrite を通さずに generate へ(段階 C の試作)。"""
    try:
        f, top = R.lower(S.parse_source(t)); nodes = R.raise_ast(f, top)
    except R.Unsup as e: return ("unsup", str(e)[:30])
    try: got = ns["run_asm"](sign_asm.generate(nodes, "linux"), linux=True) if lin else ns["run_asm"](sign_asm.generate(nodes))
    except sign_asm.AsmError as e: return ("refuse", str(e)[:40])
    except Exception as e: return ("refuse", "例外 " + str(e)[:30])
    if got[0] == "exit": return parse_exit(got)
    if got[0] == "trap": return ("trap",)
    if got[0] != "ok": return ("refuse", str(got)[:30])
    return ("void",) if got[1] == "__" else ("val", got[1])

def obs_asm(t, lin=False):
    try:
        tree, rest = sign_asm.strict_rewrite(S.parse_source(t))
        if rest: return ("refuse", "strict_rewrite: " + rest[0][1][:30])
        got = ns["run_asm"](sign_asm.generate(tree, "linux"), linux=True) if lin else ns["run_asm"](sign_asm.generate(tree))
    except sign_asm.AsmError as e: return ("refuse", str(e)[:40])
    except Exception as e: return ("refuse", "例外 " + str(e)[:30])
    if got[0] == "exit": return parse_exit(got)
    if got[0] == "trap": return ("trap",)
    if got[0] != "ok": return ("refuse", str(got)[:30])
    return ("void",) if got[1] == "__" else ("val", got[1])

i_ = src.index("MAX, MIN1 = "); j_ = src.index("\n]\n", src.index("CASES = [")) + 3
exec(src[i_:j_], ns)
via = collections.Counter(); front = collections.Counter(); back = collections.Counter(); unsup = collections.Counter(); bad = []
# SIR だけが広げた形の見本(test_asm.py の CASES は旧経路の試験なので、そこには足さずここに置く)。strict が断る・SIR が断る形も、断りとして数える。
EXTRA = [
    ("絶対値: 負", "|-5|\n"), ("絶対値: 正", "|5|\n"), ("絶対値: 0", "|0|\n"), ("絶対値: 単位", "|__|\n"),
    ("絶対値: 範囲の端", "|-9223372036854775807|\n"), ("絶対値: 式", "|3 - 8|\n"), ("絶対値: 外れた比べ", "|(3 < 2)|\n"),
    ("絶対値: 仮引数", "f : x ? |x|\nf -7\n"), ("絶対値: 仮引数に単位", "f : x ? |x|\nf (3 < 2)\n"),
    ("絶対値: 名前", "x : -4\n|x|\n"), ("絶対値: 溢れた式", "|9223372036854775807 + 1|\n"),
    ("絶対値: 呼びを含む", "g : x ? x - 9\n|g 4|\n"), ("絶対値: 絶対値の中の絶対値", "|(|-3| - 8)|\n"),
    ("絶対値: リスト", "l : 1 -2\n|l|\n"),
    ("未定義の名前", "zz\n"), ("未定義の名前: 足す", "1 + zz\n"), ("未定義の名前: 関数の本体", "f : x ? x + zz\n(f 1) + 2\n"), ("未定義の名前: 本体の値", "f : x ? zz\nf 1\n"),
    ("未定義の名前: 呼びの実引数", "inc : x ? x + 1\ninc zz\n"), ("未定義の名前: 余りの実引数", "inc : x ? x + 1\ninc 2 zz\n"), ("未定義の名前: 値の定義", "a : zz\na + 3\n"),
    ("未定義の名前: & の右", "5 & zz\n"), ("未定義の名前: | の右", "zz | 5\n"), ("未定義の名前: ノルム", "||zz||\n"), ("未定義の名前: 畳み", "[>] 1 zz 3\n"),
    ("未定義の名前: 行の中は断る", "f : x ?\n\tzz & 3\n\tx\n\nf 5\n"),
    ("行の値が部分適用: 最後の行", "add : a b ? a + b\nf : x ?\n\tx < 0 : 4\n\tadd (3 < 2)\n\nf 5\n"),
    ("行の値が部分適用: 途中の枝は次へ", "add : a b ? a + b\nf : x ?\n\tx > 0 : add (3 < 2)\n\tx\n\nf 5\n"),
    ("行の値が部分適用: 口が足りない枝", "add : a b ? a + b\nf : x ?\n\tx > 0 : add 1\n\t100\n\nf 5\n"),
    ("行の値が部分適用: 最後の枝だけ", "add : a b ? a + b\nf : x ?\n\tx > 0 : add (3 < 2)\n\nf 5\n"),
    ("文字列: 長さ", "s : `abc`\n||s||\n"), ("文字列: 字面の長さ", "||`abcd`||\n"), ("文字列: 長さに足す", "||`abc`|| + 2\n"), ("文字列: 1文字", "||`a`||\n"),
    ("文字列: 長さの計算", "s : `hello`\n||s|| * 2 - 1\n"), ("文字列: 長さを関数へ", "f : n ? n + 1\nf ||`abc`||\n"), ("文字列: 長さを行の条件", "s : `abc`\nf : x ?\n\t||s|| > x : 1\n\t0\n\nf 2\n"),
    ("文字列: 答えにする", "s : `abc`\ns\n"), ("文字列: 添字", "s : `abc`\ns ' 1\n"), ("文字列: 範囲外の添字", "s : `abc`\ns ' 5\n"), ("文字列: 足す", "s : `abc`\ns + 1\n"),
    ("文字列: 関数へ渡す", "f : x ? ||x||\nf `ab`\n"), ("文字列: 比べ", "`a` = `a`\n"), ("文字列: 非 ASCII", "s : `héllo`\n||s||\n"),
    ("文字列: 負の添字", "s : `abc`\ns ' -1\n"), ("文字列: 負の端", "s : `abc`\ns ' -3\n"), ("文字列: 負の外", "s : `abc`\ns ' -4\n"), ("文字列: 長さの添字", "s : `abc`\ns ' 3\n"),
    ("文字列: 巨大な添字", "s : `abc`\ns ' 9223372036854775807\n"), ("文字列: 単位の添字", "s : `abc`\ns ' __\n"), ("文字列: 式の添字", "s : `abc`\ns ' (2 - 5)\n"),
    ("文字列: 名前の鍵は欄(R64)", "s : `abc`\nk : 1\ns ' k\n"), ("文字列: 添字の長さ", "s : `abc`\n||s ' 1||\n"), ("文字列: 添字の名前", "s : `abc`\nt : s ' 0\nt\n"), ("文字列: 外れた添字の名前", "s : `abc`\nt : s ' 7\nt\n"),
    ("文字列: 添字を | の左", "s : `abc`\n(s ' 9) | 7\n"), ("文字列: 添字を & の右", "s : `abc`\n3 & (s ' 1)\n"), ("文字列: 文字の足し算", "s : `abc`\n(s ' 1) + 1\n"),
    ("文字列: 1 + s", "s : `abc`\n1 + s\n"), ("文字列: s - s", "s : `abc`\ns - s\n"), ("文字列: s / 2", "s : `abc`\ns / 2\n"), ("文字列: 外の足し算で消える", "s : `abc`\n5 + (s + 1)\n"),
    ("文字列: 絶対値", "s : `abc`\n|s|\n"), ("文字列: 符号", "s : `abc`\n-s\n"), ("文字列: 繰り返し", "s : `abc`\ns * 2\n"), ("文字列: 長さ(足し算)", "s : `abc`\n||s + 1||\n"),
    ("文字列: 同じ", "s : `abc`\nt : `abc`\ns = t\n"), ("文字列: 違う", "s : `abc`\nt : `abd`\ns = t\n"), ("文字列: == 違う", "s : `abc`\nt : `abd`\ns == t\n"),
    ("文字列を渡す: 長さ", "f : x ? ||x||\nf `abcd`\n"), ("文字列を渡す: そのまま返す", "f : x ? x\nf `abc`\n"), ("文字列を渡す: 添字", "f : x ? x ' 1\nf `abc`\n"), ("文字列を渡す: 範囲外", "f : x ? x ' 7\nf `abc`\n"),
    ("文字列を渡す: 名前", "s : `abc`\nf : x ? ||x||\nf s\n"), ("文字列を渡す: 添字を渡す", "f : x ? x\nf (`abc` ' 1)\n"), ("文字列を渡す: 2 つ", "f : x y ? ||x|| + ||y||\nf `ab` `cde`\n"),
    ("文字列を渡す: 足す", "f : x ? x + 1\nf `abc`\n"), ("文字列を渡す: 行の条件", "f : x ?\n\t||x|| > 2 : 1\n\t0\n\nf `abc`\n"), ("文字列を渡す: 2 段", "g : s ? s\nf : x ? ||g x||\nf `abc`\n"),
    ("文字列を渡す: 文字を渡す", "f : x ? x\nf \\a\n"), ("文字列を渡す: 数と混ぜる", "f : x ? ||x||\nf `ab`\nf 5\n"), ("文字列を渡す: 単位", "f : x ? ||x||\nf __\n"),
    ("文字: 答え", "\\a\n"), ("文字: 名前", "c : \\a\nc\n"), ("文字: 長さ", "||\\a||\n"), ("文字: 足す", "\\a + 1\n"), ("文字: 比べ", "\\a < \\b\n"),
    ("文字: & の右", "5 & \\a\n"), ("文字: | の右", "zz | \\a\n"), ("文字: & の左", "\\a & 5\n"), ("文字: 関数の本体", "f : x ? \\a\nf 1\n"), ("文字: 行の値", "f : x ?\n\tx > 0 : \\a\n\t\\b\n\nf 1\n"),
    ("ノルム: 余った関数は !_", "g : x y ? x + y\n||g 1||\n"), ("ノルム: 単位の実引数で余った関数", "g : x ? x\n||g (3 < 2)||\n"), ("ノルム: 文字列の添字が外れた実引数", "g : x ? ||x||\n||g (`f` ' 1)||\n"),
    ("ノルム: 単位は 0", "||__||\n"), ("ノルム: 外れた比べは 0", "3 + ||(3 < 2)||\n"),
    ("既定値: 省く", "gq :\n\t\tx\n\t\ty : 1\n\t? x + y\n\ngq 5\n"),
    ("既定値: 与える", "gq :\n\t\tx\n\t\ty : 1\n\t? x + y\n\ngq 5 7\n"),
    ("既定値: 単位は既定値", "gq :\n\t\tx\n\t\ty : 1\n\t? x + y\n\ngq 5 (3 < 2)\n"),
    ("既定値: 必須が単位", "gq :\n\t\tx\n\t\ty : 1\n\t? x + y\n\ngq (3 < 2)\n"),
    ("既定値: 被演算子", "gq :\n\t\tx\n\t\ty : 1\n\t? x + y\n\n(gq 5) + 1\n"),
    ("既定値: 呼びの実引数", "gq :\n\t\tx\n\t\ty : 1\n\t? x + y\n\ngq (3 - 1) (gq 4)\n"),
    ("既定値: 負の値", "gq :\n\t\tx\n\t\ty : 1\n\t? x + y\n\ngq 5 -4\n"),
    ("既定値: 溢れ", "gq :\n\t\tx\n\t\ty : 1\n\t? x + y\n\ngq 9223372036854775807\n"),
    ("既定値: 2 つ", "gz :\n\t\tx\n\t\ty : 2\n\t\tz : 3\n\t? x * y + z\n\ngz 4\n"),
    ("既定値: 2 つと上書き", "gz :\n\t\tx\n\t\ty : 2\n\t\tz : 3\n\t? x * y + z\n\ngz 4 5\n"),
]
for name, t in ns["CASES"] + EXTRA:
    t2 = fix(t)
    a, b = obs_strict(t2), obs_sir(t2)
    if b[0] == "unsup": front["SIR 未対応"] += 1; unsup[b[1][:24]] += 1; continue
    if a == b: front["一致"] += 1
    elif a[0] == "void" and b[0] == "void": front["一致"] += 1
    elif a[0] == "refuse": front["評価器が断る"] += 1
    elif b == ("partial",): front["SIR: 部分適用(実引数が void)"] += 1
    else: front["食い違い"] += 1; bad.append(("前段", name, a, b))
    lin = "`" in t2 or "\\" in t2                                      # 文字列・文字を含む見本は、実機の印字(linux)で見る(bare の戻り値は Char の `__` が 0、文字列が番地になる)
    c = obs_asm(t2, lin)
    if b not in (("partial",),):
        d = obs_asm_sir(t2, lin)
        k2 = "戻せない" if d[0] == "unsup" else "一致" if d == b else "断り" if d[0] == "refuse" else "罠" if d[0] == "trap" else "誤答"
        via[k2] += 1
        if k2 == "誤答": bad.append(("SIR経由", name, b, d))
    if b in (("partial",),): continue
    if c == b: back["一致"] += 1
    elif c[0] == "refuse": back["機械語が断る"] += 1
    elif c[0] == "trap": back["機械語が罠(溢れ・部分適用)"] += 1
    else: back["誤答"] += 1; bad.append(("後段", name, b, c))
print("前段(評価器 = SIR):", dict(front)); print("後段(SIR = 機械語):", dict(back))
print("SIR 経由の機械語(strict_rewrite なし):", dict(via))
print("SIR に下げられない形(上位):", unsup.most_common(8))
for x in bad: print("NG", *x)
sys.exit(1 if [x for x in bad] else 0)
