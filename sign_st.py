"""sign_st.py — `.st`(型シグネチャファイル)の書き出し【拡張】。使い方: python sign.py --emit-st 〈プログラム.sn〉 [-o 出力.st]

documents(type_system.md §6・compiler_pipeline.md §4)の `.st` は、`#` で export した識別子だけを、ビルド成果物としてディスクへ書く。
この道具はその最初の一歩で、**データだけの公開定義**(`#pi : 3.14`・`#greeting : `hello``・`#p : [x : 1  y : 2]` など)を `型=値` で書き出す。
- 値はインタープリタで走らせて得る(関数は走らせても署名にならない)。
- 関数の署名(`Int -> Int`)は、観測(compiler_pipeline.md §6)が要るので、まだ書かない。コメントの行で「ここは書いていません」と言う。
- 器(`List(T)`)の中身は、documents も載せ方が未決なので、型で止める。
- `0x` の字面が生む値は `Address`(Int と統合しない。type_system.md §3.6)。値は `0x…` で書く。
- `##`・`###` はこの実装の構文がまだ読まないので、`#` だけ。
"""
import os, sys, io, math

def kind_name(v, SI):
    if v is SI.UNIT or SI.is_unit(v): return "Unit"
    if isinstance(v, bool): return None
    if isinstance(v, SI.Addr): return "Address"      # 0x の字面が生む値。Int・UInt とは溢れ方が違うので統合しない(type_system.md §3.6)
    if isinstance(v, int): return "Int"
    if isinstance(v, float): return "Float"
    if isinstance(v, SI.Char): return "Char"
    if isinstance(v, str): return "String"
    if isinstance(v, SI.Struct): return "Struct"
    if isinstance(v, list): return "List"
    return None

def quoted(s):
    return None if ("`" in s or "\n" in s or "\r" in s) else "`" + s + "`"

def leaf(v, SI):
    """(綴り, 理由)。書けない値は (None, 理由)。"""
    k = kind_name(v, SI)
    if k is None: return None, "データではない値です(関数・参照など)"
    if k == "Unit": return "Unit", None
    if k == "Int": return "Int=%d" % int(v), None
    if k == "Address": return "Address=0x%X" % int(v), None
    if k == "Float":
        if math.isnan(v) or math.isinf(v): return None, "Float の nan・inf は字面で書けません"
        return "Float=%r" % float(v), None
    if k in ("Char", "String"):
        q = quoted(str(v))
        return (None, "%s の値にバッククォートか改行があり、`.st` の字面で囲めません" % k) if q is None else ("%s=%s" % (k, q), None)
    if k == "List":
        ks = {kind_name(x, SI) for x in v}
        if not v: return "List", None
        if len(ks) == 1 and None not in ks:
            e = ks.pop()
            if e == "List":
                inner = {leaf(x, SI)[0] and leaf(x, SI)[0].split("=")[0] for x in v}
                return ("List(%s)" % inner.pop() if len(inner) == 1 and None not in inner else "List"), None
            if e == "Struct": return "List(Struct)", None
            return "List(%s)" % e, None
        return "List", None
    # Struct: 鍵を名前順に並べ、連番は書いた順(並び＝物理配置。type_system.md §6 の「器と構造体の書き方」)
    slots = []
    for i, (key, x) in enumerate(v.items()):
        s, why = leaf(x, SI)
        if s is None: return None, "欄 `%s`: %s" % (key, why)
        kq = quoted(str(key))
        if kq is None: return None, "欄の名前にバッククォートか改行があり、囲めません"
        slots.append((str(key), "%s : %s , %d" % (kq, s, i)))
    return "Struct{" + "  ".join(t for _, t in sorted(slots, key=lambda p: p[0])) + "}", None

def render(path, SI):
    src = open(path, encoding="utf-8").read()
    env = SI.Env()
    old_out, old_in = sys.stdout, sys.stdin
    sys.stdout, sys.stdin = io.StringIO(), io.StringIO("")        # 走らせる間の出力は捨てる(.st は公開定義だけ)
    try: SI.run(src, env)
    finally: sys.stdout, sys.stdin = old_out, old_in
    lines = ["` SignType (st) — 公開(#)の定義のうち、データだけを書き写したもの(sign_st.py)", "` source: %s" % os.path.basename(path), ""]
    skipped = []
    for name, v in env.exports.items():
        if isinstance(v, SI.Closure):
            lines.append("` #%s : 関数。署名は観測(compiler_pipeline.md §6)が要るので、まだ書きません" % name); skipped.append(name); continue
        s, why = leaf(v, SI)
        if s is None:
            lines.append("` #%s : 書けません(%s)" % (name, why)); skipped.append(name); continue
        lines.append("#%s : %s" % (name, s))
    return "\n".join(lines) + "\n", skipped

def main(argv):
    args = list(argv); out = None
    if "-o" in args:
        i = args.index("-o")
        if i + 1 >= len(args): print("エラー: -o の後に出力のファイル名がありません", file=sys.stderr); return 1
        out = args[i + 1]; del args[i:i + 2]
    if len(args) != 1:
        print("使い方: python sign.py --emit-st 〈プログラム.sn〉 [-o 出力.st]", file=sys.stderr); return 1
    path = args[0]
    import sign_interp as SI
    try:
        text, skipped = render(path, SI)
    except OSError as e:
        print("エラー: %s を読めません(%s)" % (path, e), file=sys.stderr); return 1
    except Exception as e:                          # 走らせて落ちた・断られた: 理由を言って終わる
        print("%s: .st を書けません(%s): %s" % (path, type(e).__name__, e), file=sys.stderr); return 1
    out = out or os.path.splitext(path)[0] + ".st"
    try:
        with open(out, "w", encoding="utf-8") as fh: fh.write(text)
    except OSError as e:
        print("エラー: %s を書けません(%s)" % (out, e), file=sys.stderr); return 1
    print("書きました: %s" % out)
    if skipped: print("  書かなかった公開の名前: %s(関数・書けない値)" % " ".join(skipped), file=sys.stderr)
    return 0

if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
