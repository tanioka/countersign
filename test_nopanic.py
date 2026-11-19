#!/usr/bin/env python3
"""処理系は入力の如何によって異常終了(Python の例外・OS による強制終了)してはならない。
続けられない事由があれば、その旨を表示して正常に終了する(終了コード 0 か 1。Traceback を出さない)。
  python test_nopanic.py
仕様が黙っている入力の扱い(`_` を返すか、実装の上限で断るか)は【実装】の決めで、仕様の答えではない。"""
import os, subprocess, sys, tempfile
HERE = os.path.dirname(os.path.abspath(__file__))
PRE = "fs : $inc , $double , 3\nvs : 1 , 2 , 3\ninc : x ? x + 1\ndouble : x ? x * 2\n"
# (題, ソース(bytes か str), 期待: 出力に含まれる文字列 or None)
CASES = [
    ("添字の並びに関数", PRE + "3 ' fs~", "__"),
    ("添字の並びに関数(括り)", PRE + "3 ' (inc , double)", "__"),
    ("巨大な範囲", "v : [0 ~ 999999999]\nv\n", "長すぎます"),
    ("巨大な刻み付き範囲", "[0 ~+ 1 ~ 999999999999] ' 5\n", "長すぎます"),
    ("巨大な繰り返し(List)", "v : [1 2 3]\nw : v * 99999999\nw\n", "大きすぎます"),
    ("巨大な繰り返し(Char)", "x : \\a * 99999999999\nx\n", "大きすぎます"),
    ("巨大な冪", "3 ^ 99999999\n", "大きすぎます"),
    ("巨大なシフト", "1 << 99999999999\n", "大きすぎます"),
    ("巨大な階乗", "99999999999999999999!\n", "大きすぎます"),
    ("0 の負の冪", "0 ^ (0 - 1)\n", "__"),
    ("小数の桁あふれ", "10.0 ^ 400\n", "inf"),
    ("負の数の小数冪", "(0 - 8) ^ 0.5\n", "nan"),
    ("UTF-8 でないファイル", bytes(range(128, 256)) * 3, "UTF-8"),
    ("NUL を含むファイル", b"a : 1\x00\nb\n", "解釈できないトークン"),
    ("鍵の前置 @ に並び", "l : [10 20 30]\nvs : [1 2]\nl ' @vs\n", "単値の鍵"),
    ("空のファイル", "", None),
    ("深い入れ子", "(" * 5000 + "1" + ")" * 5000 + "\n", "1"),
    ("閉じない括り", "((((1\n", "エラー"),
    ("対応しない閉じ", "1))]]\n", "エラー"),
]
bad = 0
with tempfile.TemporaryDirectory() as d:
    for i, (title, src, want) in enumerate(CASES):
        for flags in ([], ["--strict"]):
            p = os.path.join(d, f"c{i}.sn")
            with open(p, "wb") as f: f.write(src if isinstance(src, bytes) else src.encode("utf-8"))
            try:
                r = subprocess.run([sys.executable, os.path.join(HERE, "sign.py"), *flags, p], capture_output=True, timeout=120)
            except subprocess.TimeoutExpired:
                print(f"NG  {title} {flags}: 120 秒で終わらない"); bad += 1; continue
            out = (r.stdout + r.stderr).decode("utf-8", "replace")
            ok = r.returncode in (0, 1) and "Traceback" not in out and (want is None or want in out or (bool(flags) and r.returncode == 0 and r.stdout == b""))      # --strict はファイルの行の値を捨てる(V9)ので、値の期待は既定の道だけで見る
            if not ok:
                bad += 1; print(f"NG  {title} {flags}: 終了コード {r.returncode}: {out[:200]!r}")
        else:
            if bad == 0: print(f"ok  {title}")
# --check-int(仕様どおりの Int の値域の検査。既定は Python の整数)。溢れは罠として知らせて止まる(Traceback を出さない)
CHECK_INT = [("加算の溢れ", "9223372036854775807 + 1\n", "Int の溢れ"), ("冪の溢れ", "2 ^ 63\n", "Int の溢れ"), ("積の溢れ", "3037000500 * 3037000500\n", "Int の溢れ"),
             ("niche に着く差", "-9223372036854775807 - 1\n", "Int の溢れ"), ("反転の溢れ", "!!9223372036854775807\n", "Int の溢れ"), ("階乗風の溢れ", "f : n ? n = 0 & 1 | n * (f (n - 1))\nf 25\n", "Int の溢れ"),
             ("範囲外の字面", "9223372036854775808\n", "字面"), ("負の範囲外の字面", "-9223372036854775808\n", "字面"), ("値域の端は通る", "9223372036854775807\n", "9223372036854775807"),
             ("番地は別の域", "0x1000 + 8\n", "4104"), ("__ との和", "9223372036854775807 + __\n", "9223372036854775807")]
with tempfile.TemporaryDirectory() as d:
    for i, (title, src, want) in enumerate(CHECK_INT):
        p = os.path.join(d, f"i{i}.sn"); open(p, "w", encoding="utf-8").write(src)
        r = subprocess.run([sys.executable, os.path.join(HERE, "sign.py"), "--check-int", p], capture_output=True, timeout=120)
        out = (r.stdout + r.stderr).decode("utf-8", "replace")
        if not (r.returncode in (0, 1) and "Traceback" not in out and want in out): bad += 1; print(f"NG  --check-int {title}: 終了コード {r.returncode}: {out[:200]!r}")
        else: print(f"ok  --check-int {title}")
# --check-f32(Vector のレーンを 32 ビット精度に丸める。既定は 64 ビット)
F32C = [("レーンの積", "v : [0.1 0.2 0.3 0.4]\nv * 3.0\n", "[0.3 0.6 0.90000004 1.2]"), ("2^24 を超える加算", "v : [16777216.0 1.0 2.0 3.0]\nv + 1.0\n", "[16777216.0 2.0 3.0 4.0]"),
        ("レーンの読み", "v : [0.1 0.2 0.3 0.4]\nv ' 0\n", "0.10000000149011612")]
with tempfile.TemporaryDirectory() as d:
    for i, (title, src, want) in enumerate(F32C):
        p = os.path.join(d, f"f{i}.sn"); open(p, "w", encoding="utf-8").write(src)
        for flags, w in ((["--layer", "3", "--check-f32"], want), (["--layer", "3"], None)):
            r = subprocess.run([sys.executable, os.path.join(HERE, "sign.py"), *flags, p], capture_output=True, timeout=120)
            out = (r.stdout + r.stderr).decode("utf-8", "replace")
            if not (r.returncode in (0, 1) and "Traceback" not in out and (w is None or w in out)): bad += 1; print(f"NG  --check-f32 {title} {flags}: {out[:200]!r}")
        else: print(f"ok  --check-f32 {title}")
print("全部通った" if bad == 0 else f"失敗 {bad}")
sys.exit(1 if bad else 0)
