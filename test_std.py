#!/usr/bin/env python3
"""標準ライブラリ(std.sn)の試験。Sign の小さな式を書いて本物の処理系で動かし、出力を確かめる。python test_std.py"""
import os, subprocess, sys, tempfile, time
HERE = os.path.dirname(os.path.abspath(__file__))
STD = os.path.join(HERE, "std.sn")
WORK = tempfile.mkdtemp()
A, B, C = "0x500000", "0x510000", "0x520000"

bad = 0
def check(name, got, want):
    global bad
    ok = got == want; bad += not ok
    print(("ok  " if ok else "NG  ") + name + ("" if ok else f"\n    得た: {got!r}\n    期待: {want!r}"))

def run(body, data="", sys_dev=False, cwd=None, strict=False):
    d = cwd or WORK
    p = os.path.join(d, "t.sn")
    open(p, "w", encoding="utf-8").write(f"`{STD}`@~\n" + body + "\n")
    args = [sys.executable, os.path.join(HERE, "sign.py"), p] + (["--sys"] if sys_dev else []) + (["--strict"] if strict else [])
    r = subprocess.run(args, input=data.encode(), capture_output=True, cwd=d, timeout=120)
    return r.stdout.decode().strip(), r.stderr.decode().strip()
def val(body, **kw):                                    # 値(最後の式)。エラーがあれば " ! エラー" をつける
    out, err = run(body, **kw)
    return out if not err else out + " ! " + err[:200]
g = lambda p, i: f"arr_get {p} {i}"
def seq(*parts): return f"seq{len(parts)} " + " ".join(f"({x})" if " " in x else x for x in parts)
def arr_list(p, n): return "(" + " , ".join(g(p, i) for i in range(n)) + ")"
def setarr(p, xs): return [f"arr_set {p} {i} {x}" for i, x in enumerate(xs)]
put = lambda p, s: f"str_put {p} `{s}`"
neg = lambda n: f"(0 - {-n})" if n < 0 else str(n)

# --- 数 ---
for e, w in [("abs (0 - 5)", "5"), ("abs 7", "7"), ("min 3 2", "2"), ("max 3 2", "3"), ("max 4 4", "4"), ("clamp 15 0 10", "10"), ("clamp (0 - 3) 0 10", "0"), ("clamp 5 0 10", "5"),
             ("sign (0 - 9)", "-1"), ("sign 0", "0"), ("sign 8", "1"), ("gcd 12 18", "6"), ("gcd 0 5", "5"), ("gcd (0 - 12) 18", "6"), ("lcm 4 6", "12"), ("lcm 0 6", "0"),
             ("isqrt 0", "0"), ("isqrt 1", "1"), ("isqrt 99", "9"), ("isqrt 100", "10"), ("isqrt 1000000", "1000"), ("isqrt (0 - 4)", "-1"),
             ("fdiv (0 - 7) 2", "-4"), ("fdiv 7 2", "3"), ("fdiv 7 (0 - 2)", "-4"), ("fdiv (0 - 8) 2", "-4"), ("fmod (0 - 7) 3", "2"), ("fmod 7 3", "1"),
             ("even 4", "1"), ("even 3", "0"), ("odd 3", "1"), ("odd 4", "0"), ("ipow 2 10", "1024"), ("ipow 5 0", "1"), ("ipow 3 4", "81")]:
    check(f"数: {e}", val(e), w)
# --- 乱数 ---
three = lambda s: val(f"seq4 (rand_seed {s}) (arr_set {A} 0 (rand_int 100000)) (arr_set {A} 1 (rand_int 100000)) ({g(A, 0)} , {g(A, 1)})")
check("乱数: 同じ種なら同じ並び", three(42), three(42))
check("乱数: 違う種なら違う並び", three(42) != three(43), True)
rf = lambda n, k: (f"rf : i n k ?\n\ti >= n : 0\n\t(arr_set {A} i (rand_int k)) : rf (i + 1) n k\n"
                   f"seq3 (rand_seed 5) (rf 0 {n} {k}) ({' , '.join(g(A, i) for i in range(n))})")
xs = eval(val(rf(30, 6)))
check("乱数: 30 回の値が 0〜5 に収まり、5 種類以上出る", (all(0 <= x < 6 for x in xs), len(set(xs)) >= 5), (True, True))
check("乱数: n が 1 なら 0", val("seq2 (rand_seed 1) (rand_int 1)"), "0")
check("乱数: rand_range は lo 以上 hi 未満", all(5 <= int(val(f"seq2 (rand_seed {s}) (rand_range 5 8)")) < 8 for s in range(1, 8)), True)
# --- 整数の並び ---
check("並び: fill と sum", val(f"seq3 (arr_fill {A} 5 3) (arr_set {A} 2 10) (arr_sum {A} 5)"), "22")
check("並び: n が 0 の sum", val(f"arr_sum {A} 0"), "0")
check("並び: sort", val(seq(*setarr(A, [5, 2, 9, 1, 7]), f"arr_sort {A} 5", arr_list(A, 5))), "[1, 2, 5, 7, 9]")
check("並び: sort(重複)", val(seq(*setarr(A, [3, 3, 1, 3, 2]), f"arr_sort {A} 5", arr_list(A, 5))), "[1, 2, 3, 3, 3]")
check("並び: sort(負の数)", val(seq(*setarr(A, [neg(-5), 3, neg(-1), 0]), f"arr_sort {A} 4", arr_list(A, 4))), "[-5, -1, 0, 3]")
check("並び: sort(1 個・0 個)", val(seq(f"arr_set {A} 0 4", f"arr_sort {A} 1", g(A, 0))) + val(f"arr_sort {A} 0"), "40")
check("並び: sort(逆順)", val(seq(*setarr(A, [5, 4, 3, 2, 1]), f"arr_sort {A} 5", arr_list(A, 5))), "[1, 2, 3, 4, 5]")
ld = f"ld : i n ?\n\ti >= n : 0\n\t(arr_set {A} i (n - i)) : ld (i + 1) n\n"
check("並び: sort(300 個の逆順)", val(ld + f"seq3 (ld 0 300) (arr_sort {A} 300) (arr_sorted {A} 300 , {g(A, 0)} , {g(A, 299)})"), "[1, 1, 300]")
check("並び: max min find count", val(seq(*setarr(A, [5, 2, 9, 2]), "(" + f"arr_max {A} 4 , arr_min {A} 4 , arr_find {A} 4 9 , arr_find {A} 4 77 , arr_count {A} 4 2" + ")")), "[9, 2, 2, -1, 2]")
check("並び: reverse(偶数・奇数)", val(seq(*setarr(A, [1, 2, 3, 4]), f"arr_reverse {A} 4", arr_list(A, 4))) + val(seq(*setarr(B, [1, 2, 3]), f"arr_reverse {B} 3", arr_list(B, 3))), "[4, 3, 2, 1][3, 2, 1]")
check("並び: swap", val(seq(f"arr_set {A} 0 1", f"arr_set {A} 1 2", f"arr_swap {A} 0 1", f"({g(A, 0)} , {g(A, 1)})")), "[2, 1]")
check("並び: bsearch と sorted", val(seq(*setarr(A, [1, 3, 5, 7]), f"(arr_bsearch {A} 4 5 , arr_bsearch {A} 4 1 , arr_bsearch {A} 4 7 , arr_bsearch {A} 4 4 , arr_sorted {A} 4)")), "[2, 0, 3, -1, 1]")
check("並び: sorted(崩れている)", val(seq(*setarr(A, [1, 3, 2]), f"arr_sorted {A} 3")), "0")
check("並び: copy", val(seq(f"arr_fill {A} 3 7", f"arr_copy {B} {A} 3", f"arr_set {B} 1 9", f"(arr_sum {B} 3 , arr_sum {A} 3)")), "[23, 21]")
check("並び: 10000 個の fill と sum(深さの限りなし)", val(f"seq2 (arr_fill {A} 10000 2) (arr_sum {A} 10000)"), "20000")
# --- メモリの文字列 ---
check("文字列: put は長さを返す", val(put(A, "hello")), "5")
# 空文字列 `` は `!_` と同じ値で、値の口の実引数では消える(type_system.md §空文字列・string_and_comment.md)。`str_put A ``` は実引数が足りない部分適用になるので、
# 空の文字列は終端の 0 だけを書いて作る。
check("文字列: 空(終端だけ)の長さは 0", val(seq(f"({A} # 0)", f"str_len {A}")), "0")
check("文字列: len", val(seq(put(A, "hello"), f"str_len {A}")), "5")
check("文字列: 0 で終わる(次の語が 0)", val(seq(put(A, "ab"), f"(@({A} + 8))")), "0")
check("文字列: cpy", val(seq(put(A, "copy me"), f"str_cpy {B} {A}", f"(str_len {B} , str_eq {A} {B})")), "[7, 1]")
check("文字列: cat は全体の長さを返す", val(seq(put(A, "foo"), put(B, "bar"), f"str_cat {A} {B}")), "6")
check("文字列: cat の中身", val(seq(put(A, "foo"), put(B, "bar"), f"str_cat {A} {B}", put(C, "foobar"), f"str_eq {A} {C}")), "1")
check("文字列: cmp", val(seq(put(A, "abc"), put(B, "abd"), f"(str_cmp {A} {B} , str_cmp {B} {A} , str_cmp {A} {A})")), "[-1, 1, 0]")
check("文字列: cmp(接頭辞は短い方が小さい)", val(seq(put(A, "ab"), put(B, "abc"), f"(str_cmp {A} {B} , str_cmp {B} {A})")), "[-1, 1]")
check("文字列: eq", val(seq(put(A, "x"), put(B, "x"), put(C, "y"), f"(str_eq {A} {B} , str_eq {A} {C})")), "[1, 0]")
check("文字列: chr", val(seq(put(A, "hello world"), f"(str_chr {A} 119 , str_chr {A} 104 , str_chr {A} 122)")), "[6, 0, -1]")
check("文字列: find", val(seq(put(A, "hello world"), put(B, "o w"), put(C, "zz"), f"(str_find {A} {B} , str_find {A} {C} , str_find {A} {A} , str_find {B} {A})")), "[4, -1, 0, -1]")
check("文字列: find(空の needle は 0、末尾で一致)", val(seq(put(A, "abcabc"), f"({B} # 0)", put(C, "bc"), f"(str_find {A} {B} , str_find {A} {C})")), "[0, 1]")
check("文字列: starts と ends", val(seq(put(A, "hello.sn"), put(B, ".sn"), f"(str_starts {A} {A} , str_ends {A} {B} , str_ends {B} {A} , str_starts {A} {B})")), "[1, 1, 0, 0]")
check("文字列: sub", val(seq(put(A, "Hello World"), f"str_sub {B} {A} 6 5", put(C, "World"), f"str_eq {B} {C}")), "1")
check("文字列: sub(足りなければ手前まで)", val(seq(put(A, "abc"), f"str_sub {B} {A} 1 99", f"str_len {B}")), "2")
check("文字列: upper", val(seq(put(A, "Hello, World 42!"), f"str_upper {A}", put(C, "HELLO, WORLD 42!"), f"str_eq {A} {C}")), "1")
check("文字列: lower", val(seq(put(A, "Hello, World 42!"), f"str_lower {A}", put(C, "hello, world 42!"), f"str_eq {A} {C}")), "1")
check("文字列: trim", val(seq(put(A, "  hi there \t"), f"str_trim {A}", put(C, "hi there"), f"(str_len {A} , str_eq {A} {C})")), "[8, 1]")
check("文字列: trim(空白だけ・空)", val(seq(put(A, "   "), f"str_trim {A}", f"str_len {A}")) + val(seq(f"({B} # 0)", f"str_trim {B}")), "00")
check("文字列: reverse", val(seq(put(A, "abc"), f"str_reverse {A}", put(B, "cba"), f"str_eq {A} {B}")), "1")
check("文字列: split の欄の数", val(seq(put(A, "a,bb,,ccc"), f"str_split {A} 44 {B} 10")), "4")
check("文字列: split の欄の数(区切りなし・空・max で切る)", val(seq(put(A, "abc"), f"str_split {A} 44 {B} 10")) + val(seq(f"({A} # 0)", f"str_split {A} 44 {B} 10")) + val(seq(put(A, "a,b,c,d"), f"str_split {A} 44 {B} 2")), "112")
sl = "sl : p ? str_len p\n"
check("文字列: split の中身(欄ごとの長さ)", val(sl + seq(put(A, "a,bb,,ccc"), f"str_split {A} 44 {B} 10", f"(sl (arr_get {B} 0) , sl (arr_get {B} 1) , sl (arr_get {B} 2) , sl (arr_get {B} 3))")), "[1, 2, 0, 3]")
# --- 数値と文字列 ---
for n in (0, 7, 10, 99, 100, 1204, 2147483647, -1, -1204, 123456789):
    check(f"変換: str_int {n}", val(seq(f"str_int {A} {neg(n)}", f"(str_len {A} , str_to_int {A})")), f"[{len(str(n))}, {n}]")
check("変換: to_int は数字でない所で止まる", val(seq(put(A, "-1204xyz"), put(B, "12a"), f"(str_to_int {A} , str_to_int {B})")), "[-1204, 12]")
check("変換: to_int(+ 符号・数字なし)", val(seq(put(A, "+5"), put(B, "abc"), f"(str_to_int {A} , str_to_int {B})")), "[5, 0]")
check("変換: is_int", val(seq(put(A, "-42"), put(B, "12a"), f"({C} # 0)", f"(str_is_int {A} , str_is_int {B} , str_is_int {C})")), "[1, 0, 0]")
check("変換: is_int(符号だけ・+ つき)", val(seq(put(A, "-"), put(B, "+7"), f"(str_is_int {A} , str_is_int {B})")), "[0, 1]")
for n, w in ((0, "0"), (255, "ff"), (4096, "1000"), (3735928559, "deadbeef"), (-1, "ffffffff")):
    check(f"変換: str_hex {n}", run(seq(f"str_hex {A} {neg(n)}", f"print_mem {A}"))[0], w + "0")
# --- 出す・読む ---
check("出力: print と println", run("seq3 (print `ab`) (println `cd`) (println `ef`)")[0], "abcd\nef\n0")
check("出力: print_int(負の数)", run("seq3 (print_int (0 - 305)) (newline 0) (println_int 42)")[0], "-305\n42\n0")
check("出力: println_mem", run(seq(put(A, "mem"), f"println_mem {A}"))[0], "mem\n0")
check("入力: read_line(1 行目と 2 行目)", run(seq(f"read_line {A} 100", f"print_mem {A}", f"read_line {A} 100", f"print_mem {A}"), data="hello\nworld\n")[0], "helloworld0")
check("入力: read_line の戻り値(長さ・空行・終わり)", val(seq(f"arr_set {A} 0 (read_line {B} 100)", f"arr_set {A} 1 (read_line {B} 100)", f"arr_set {A} 2 (read_line {B} 100)", arr_list(A, 3)), data="hello\n\n"), "[5, 0, -1]")
check("入力: CRLF の CR は入れない", val(seq(f"read_line {A} 100", f"str_len {A}"), data="abc\r\n"), "3")
check("入力: 改行なしで終わっても読める", val(seq(f"read_line {A} 100", f"str_len {A}"), data="abc"), "3")
check("入力: 長い行は max - 1 で切り、残りは次へ", val(seq(f"read_line {A} 4", f"read_line {B} 100", f"(str_len {A} , str_len {B})"), data="abcdefg\n"), "[3, 4]")
check("入力: read_all", val(seq(f"read_all {A} 100", f"str_len {A}"), data="abc\ndef\n"), "8")
check("入力: read_all(max で切る)", val(seq(f"read_all {A} 4", f"str_len {A}"), data="abcdefg"), "3")
# --- ファイルと時刻(--sys) ---
d = tempfile.mkdtemp(); S = dict(sys_dev=True, cwd=d)
check("ファイル: write_file は書いたバイト数", val(f"seq3 (str_put {A} `data.txt`) (str_put {B} `hello file`) (write_file {A} {B} 10)", **S), "10")
check("ファイル: 本物のファイルができる", open(os.path.join(d, "data.txt"), "rb").read(), b"hello file")
check("ファイル: read_file は読んだバイト数", val(f"seq2 (str_put {A} `data.txt`) (read_file {A} {C} 100)", **S), "10")
check("ファイル: 読んだ中身", val(f"seq4 (str_put {A} `data.txt`) (read_file {A} {C} 100) (str_put {B} `hello file`) (str_eq {B} {C})", **S), "1")
check("ファイル: append_file で足す", val(f"seq4 (str_put {A} `data.txt`) (str_put {B} `!!`) (append_file {A} {B} 2) (read_file {A} {C} 100)", **S), "12")
check("ファイル: size と exists", val(f"seq2 (str_put {A} `data.txt`) (file_size {A} , file_exists {A})", **S), "[12, 1]")
check("ファイル: 無いファイルは ENOENT・exists は 0", val(f"seq2 (str_put {A} `no.txt`) (read_file {A} {C} 100 , file_exists {A})", **S), "[-2, 0]")
check("ファイル: 作業フォルダの外は EACCES", val(f"seq3 (str_put {A} `../evil.txt`) (str_put {B} `x`) (write_file {A} {B} 1)", **S), "-13")
check("ファイル: 外へは書かれていない", os.path.exists(os.path.join(os.path.dirname(d), "evil.txt")), False)
check("ファイル: max で切って読む", val(f"seq2 (str_put {A} `data.txt`) (read_file {A} {C} 5)", **S), "4")
check("ファイル: open → read → close(104 = 'h')", val(f"seq5 (str_put {A} `data.txt`) (arr_set {B} 0 (file_open {A} 0)) (file_read (arr_get {B} 0) {C} 3) (file_close (arr_get {B} 0)) (@{C})", **S), "104")
ts, tm = eval(val("(time_s 0 , time_ms 0)", sys_dev=True))
check("時刻: 今の秒とミリ秒", (abs(ts - time.time()) < 5, abs(tm - time.time() * 1000) < 5000), (True, True))
check("--sys が無くても落ちない(ファイルの関数は __)", run(f"seq2 (str_put {A} `data.txt`) (file_size {A})", cwd=d)[1], "")
# --- 見本 ---
r = subprocess.run([sys.executable, os.path.join(HERE, "sign.py"), os.path.join(HERE, "std_demo.sn")], input=b"5\n3\n8\nabc\n 10 \n-2\n", capture_output=True, cwd=HERE, timeout=60)
check("見本 std_demo.sn: 統計を出す", (r.stdout.decode().splitlines()[:6], r.stderr.decode()), (["個数    : 5", "合計    : 24", "平均    : 4", "最小    : -2", "最大    : 10", "中央値  : 5"], ""))
r = subprocess.run([sys.executable, os.path.join(HERE, "sign.py"), os.path.join(HERE, "std_demo.sn")], input=b"", capture_output=True, cwd=HERE, timeout=60)
check("見本 std_demo.sn: 空の入力", r.stdout.decode().splitlines()[0], "数がありません")
check("出力: println_int に List を渡すと止まらず、何も出さず __", run("println_int [2 1]")[0], "__")
check("出力: print_int に List を渡すと何も出さない", run("seq2 (print_int [2 1]) (println_int 7)")[0], "7\n__")
check("出力: println_int_list", run("seq3 (println_int_list [2 1]) (println_int_list [5]) (println_int_list [0 - 3 10 200 0])")[0].startswith("[2 1]\n[5]\n[-3 10 200 0]\n"), True)
check("出力: print_int_list は改行なし", run("seq2 (print_int_list [1 2 3]) (print_int_list [4])")[0].startswith("[1 2 3][4]"), True)
check("出力: println_int_list に小数・入れ子が混ざると何も出さず __", run("seq3 (println_int_list [1 2.5]) (println_int_list [[1 2] 3]) (println_int 9)")[0], "9\n__")
check("出力: println_int に小数を渡すと何も出さない", run("seq2 (println_int 2.5) (println_int 3)")[0], "3\n__")
# --- --strict(仕様 R62: 番地と素の数は混ぜられない。STD_W4 の `(0x4 * 1) | 4` が両モードで番地の幅になる)。strict ではファイルの値は捨てるので、出力だけを比べる ---
for body, w in [("println_int 42", "42"), ("println_int (0 - 305)", "-305"), (f"seq2 (str_put {A} `hello`) (println_mem {A})", "hello"), (f"seq2 (str_hex {A} 255) (println_mem {A})", "ff"),
                (f"seq4 (arr_set {B} 0 5) (arr_set {B} 1 2) (arr_sort {B} 2) (println_int (arr_get {B} 0))", "2"), ("println_int_list [3 1 2]", "[3 1 2]"),
                (f"seq4 (str_put {A} `ab`) (str_put {B} `cd`) (str_cat {A} {B}) (println_mem {A})", "abcd")]:
    out_d, _ = run(body); out_s, _ = run(body, strict=True)
    check(f"strict: {body[:40]}", (out_s, out_d.split("\n")[0]), (w, w))
print("\n" + ("全部通った" if not bad else f"{bad} 件 食い違い")); sys.exit(1 if bad else 0)
