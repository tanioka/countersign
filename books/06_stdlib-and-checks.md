# 第6巻 標準ライブラリと確かめる道具

<!-- nav -->
[← 前: 第5巻 ブロックでゲーム](05_blocks-game.md) | [目次](README.md) | [次: 第7巻 大きなゲームを読む →](07_reading-suika.md)
<!-- /nav -->

Nov 3, 2026 · @たににゃん

**目次**

- はじめに
- 第1章 標準ライブラリ std.sn
  - レシピ1 数のこまごま
  - レシピ2 乱数を振る
  - レシピ3 並びを求めて並べ替えて探す
  - レシピ4 文字列を扱う
  - レシピ5 ファイルを読み書きする
- 第2章 書いたものを実行せずに確かめる
  - レシピ6 実行せずに整合を調べる(--check)
  - レシピ7 より厳しく確かめる(--strict)
  - レシピ8 番地の範囲の外を見つける(境界の検査)
  - レシピ9 構文木を S 式と後置で書き出す(--sexp・--forth)
- 付録 コマンドと関数の一覧

## はじめに

この巻は、Sign で書いた標準ライブラリ(`std.sn`)の使い方と、書いたプログラムを実行せずに確かめる道具のレシピ集です。『動くレシピ集』で標準入力を読むときに `std.sn` を少し使いましたが、この巻では、数・乱数・並び・文字列・ファイルをひと通り動かします。

各レシピは「やりたいこと、全コード、実行結果、ひとこと」の順です。実行は既定のモードで行い、確かめた版は「alpha1 実装 2026-11-06 00:50 JST」です。第1章と第2章の `--strict` は、確かめる道具としてだけ使います。第1章では、既定の結果と同じかを確かめただけで、第2章では、断られる書き方を調べます。

コマンドは、bash で打つ形で書いています。確かめたのは Linux の上だけで、Windows や macOS では試していません。

結果の出どころは、入れた印で区別します。

- **【仕様】** 配布された仕様書に書かれている動作です。
- **【実装】** `sign_interp.py` がそう動くだけで、仕様書に見つからない動作です。別の処理系では同じになるとは限りません。
- **【拡張】** 仕様に無い、この実装に添えた道具です。

`std.sn` の関数と、`--check`、`--strict`、`--check-bounds`、`--sexp`、`--forth` は、すべて【拡張】です。ほかの処理系で同じ名前の関数や同じ指定が使えるとは限りません。

**確かめた範囲** 1台のパソコンの中で、各例を実行して結果を取りました。ファイルを扱う例(第1章のレシピ5)は、その中の作業フォルダの中だけです。

印の無い記述は、仕様書の記述と実行結果が一致したものです。Sign の資料は [johnny-shaman/Sign](https://github.com/johnny-shaman/Sign) にあり、仕様書に無い話は [Discussions](https://github.com/johnny-shaman/Sign/discussions) に出てきます。

## 第1章 標準ライブラリ std.sn

使うときは、プログラムの先頭に `` `std.sn`@~ `` と書きます(ファイル名をバッククォートで囲み、`@~` を続けます)。`std.sn` は、`sign_interp.py` と同じフォルダに置き、プログラムをそのフォルダから実行します。この章の例は、念のため `--strict` でも実行し、同じ結果でした【拡張】。

トップレベルの最後の式の値が画面に出るため、どの実行結果の最後にも `0` が一つ出ています【実装】。

### レシピ1 数のこまごま

**やりたいこと** 最大公約数、平方根、べき乗を求める。負の数を割るときの丸め方を確かめる。

```
`std.sn`@~

show : label v ? seq3 (print label) (println_int v) 0

show `gcd 12 18   = ` (gcd 12 18)
show `lcm 4 6      = ` (lcm 4 6)
show `isqrt 50     = ` (isqrt 50)
show `isqrt 0 - 4  = ` (isqrt (0 - 4))
show `ipow 2 10    = ` (ipow 2 10)
show `clamp 15 0 9 = ` (clamp 15 0 9)
show `sign 0 - 7   = ` (sign (0 - 7))
show `7 / 2        = ` (7 / 2)
show `(0-7) / 2    = ` ((0 - 7) / 2)
show `fdiv (0-7) 2 = ` (fdiv (0 - 7) 2)
show `(0-7) % 3    = ` ((0 - 7) % 3)
show `fmod (0-7) 3 = ` (fmod (0 - 7) 3)
```

**実行結果**

```
gcd 12 18   = 6
lcm 4 6      = 12
isqrt 50     = 7
isqrt 0 - 4  = -1
ipow 2 10    = 1024
clamp 15 0 9 = 9
sign 0 - 7   = -1
7 / 2        = 3
(0-7) / 2    = -3
fdiv (0-7) 2 = -4
(0-7) % 3    = -1
fmod (0-7) 3 = 2
0
```

**ひとこと** `show` は、ラベルと整数を並べて出す、このプログラムだけの小さな関数です。`isqrt` は切り捨ての平方根で、負の数には -1 を返します【拡張】。`/` と `%` は、負の数でも 0 の方へ丸め、`(0 - 7) / 2` は -3、`(0 - 7) % 3` は -1 になりました【仕様】([第8巻](08_spec-vs-impl.md)で、type\_system.md と照らしました)。小さい方へ丸めたいときは、`fdiv` と `fmod` を使います【拡張】。

### レシピ2 乱数を振る

**やりたいこと** サイコロを 10 回振る。同じ種からは同じ目が出ることを確かめる。

```
`std.sn`@~

dice : n ?
	n <= 0 : 0
	(print_int (rand_range 1 7)) : dice2 n
dice2 : n ? seq3 (print `  `) 0 (dice (n - 1))

line : seed ? seq4 (rand_seed seed) (dice 10) (newline 0) 0

line 42
line 42
line 7
```

**実行結果**

```
2  6  6  4  3  2  4  5  2  2  
2  6  6  4  3  2  4  5  2  2  
5  3  3  1  6  6  1  3  6  6  
0
```

**ひとこと** `rand_range 1 7` は 1 以上 7 未満の整数です。`rand_seed` で種を決めると、同じ種からは同じ並びが出ます(1 行目と 2 行目)。種を 7 にすると変わります。線形合同法の乱数です【拡張】。上の目の並びは、この実装でそうなっただけです【実装】。ここでは `dice` の各回のあとに空白をつけたため、行末にも空白が残ります。

### レシピ3 並びを求めて並べ替えて探す

**やりたいこと** 乱数で 8 個の整数を作り、最大・最小・合計を求め、小さい順に並べて探す。

```
`std.sn`@~

A : 0x500000
N : 8

dump : i ?
	i >= N : newline 0
	seq3 (print_int (arr_get A i)) (print `  `) (dump (i + 1))

fill : i ?
	i >= N : 0
	(arr_set A i (rand_int 50)) : fill (i + 1)

yes : label v ? seq3 (print label) (println_int v) 0

seq4 (rand_seed 3) (fill 0) (dump 0) 0
yes `最大 ` (arr_max A N)
yes `最小 ` (arr_min A N)
yes `合計 ` (arr_sum A N)
yes `並んでいる(1 ならはい) ` (arr_sorted A N)
arr_sort A N
dump 0
yes `並んでいる(1 ならはい) ` (arr_sorted A N)
yes `22 は何番目(二分探索) ` (arr_bsearch A N 22)
yes `30 は何番目(二分探索) ` (arr_bsearch A N 30)
arr_reverse A N
dump 0
yes `22 は何番目(順に探す) ` (arr_find A N 22)
0
```

**実行結果**

```
47  7  15  12  22  46  23  43  
最大 47
最小 7
合計 215
並んでいる(1 ならはい) 0
7  12  15  22  23  43  46  47  
並んでいる(1 ならはい) 1
22 は何番目(二分探索) 3
30 は何番目(二分探索) -1
47  46  43  23  22  15  12  7  
22 は何番目(順に探す) 4
0
```

**ひとこと** 整数の並びは、番地 `A` から 4 つとびに 1 語ずつ置きます(`arr_get A i` は `@(A + (i * 4))` と同じです)。この 4 つとびは、`std.sn` の約束です【実装】。番地を `#` で書き `@` で読む動作そのものは、仕様にあります【仕様】。`arr_sort` は挿入ソートで、同じ値の順は変わらず、個数が大きいと遅くなります(個数の 2 乗に比例して時間がかかります)【拡張】。`arr_bsearch` は並べ終えた並びに使います。並べる前の並びでの結果は、確かめていません。

### レシピ4 文字列を扱う

**やりたいこと** 文字列の前後の空白を取り、大文字・小文字にし、探し、切り出し、つなげ、比べ、整数との行き来をする。

```
`std.sn`@~

S : 0x500000
T : 0x501000
P : 0x502000

yes : label v ? seq3 (print label) (println_int v) 0
pat : s ? seq2 (str_put P s) P

str_put S `  Hello, Sign World  `
yes `長さ ` (str_len S)
str_trim S
yes `trim のあとの長さ ` (str_len S)
println_mem S
str_upper S
println_mem S
str_lower S
println_mem S
yes `sign の場所 ` (str_find S (pat `sign`))
yes `xyz の場所 ` (str_find S (pat `xyz`))
yes `hello で始まる ` (str_starts S (pat `hello`))
yes `world で終わる ` (str_ends S (pat `world`))
str_sub T S 7 4
println_mem T
str_put T `!!`
str_cat S T
println_mem S
str_put T `abc`
yes `abc と abd ` (str_cmp T (pat `abd`))
yes `abc と abc ` (str_cmp T (pat `abc`))
str_reverse T
println_mem T
str_put T `-123abc`
yes `-123abc を整数に ` (str_to_int T)
yes `-123abc は整数か ` (str_is_int T)
str_put T `456`
yes `456 は整数か ` (str_is_int T)
str_hex T 255
println_mem T
str_int T (0 - 42)
println_mem T
0
```

**実行結果**

```
長さ 21
trim のあとの長さ 17
Hello, Sign World
HELLO, SIGN WORLD
hello, sign world
sign の場所 7
xyz の場所 -1
hello で始まる 1
world で終わる 1
sign
hello, sign world!!
abc と abd -1
abc と abc 0
cba
-123abc を整数に -123
-123abc は整数か 0
456 は整数か 1
ff
-42
0
```

**ひとこと** `std.sn` の文字列関数が扱うのは、「メモリの文字列」です。番地から 1 語を 1 バイトとして 4 つとびに置き、最後を 0 で終える形です。バッククォートで囲んだ Sign の文字列は、`str_put` でメモリへ写してから渡します。ここでは、探す言葉を渡すための `pat` という小さな関数を作りました。文字は ASCII だけです【拡張】。

**気をつける点** `` str_find S `sign` `` のように、Sign の文字列をそのまま渡すと、この実装では 20 秒待っても終わりませんでした【実装】。メモリの文字列を期待する関数には、必ず `str_put` で写した番地を渡してください。

#### 欄で区切る

カンマで区切った文字列を、`str_split` で欄ごとの番地に分けます。区切りは文字のコードで渡します(カンマは 44)。

```
`std.sn`@~

S : 0x500000
TAB : 0x501000

fields : i n ?
	i >= n : 0
	seq3 (print `[`) (print_mem (arr_get TAB i)) (seq2 (println `]`) (fields (i + 1) n))

str_put S `apple,banana,,cherry`
fields 0 (str_split S 44 TAB 10)
```

```
[apple]
[banana]
[]
[cherry]
0
```

空の欄も、一つの欄として数えられます。`str_split` は、元の文字列の区切りを 0 に書き換えるので、元の文字列はこわれます【拡張】。

**確かめていないこと** 日本語など ASCII 以外の文字を、これらの関数で扱う例は、確かめていません。

### レシピ5 ファイルを読み書きする

**やりたいこと** 作業フォルダの中にファイルを作り、足して書き、読み戻す。無いファイルを読むとどうなるかを見る。

```
`std.sn`@~

P : 0x500000
B : 0x501000
R : 0x502000

yes : label v ? seq3 (print label) (println_int v) 0

str_put P `memo.txt`
str_put B `hello from Sign;`
yes `書いたバイト数 ` (write_file P B (str_len B))
yes `足して書く ` (append_file P B (str_len B))
yes `大きさ ` (file_size P)
yes `あるか ` (file_exists P)
yes `読んだバイト数 ` (read_file P R 1000)
println_mem R
str_put P `none.txt`
yes `無いファイルを読む ` (read_file P R 1000)
yes `あるか ` (file_exists P)
0
```

作業フォルダを指定して実行します(ここでは現在のフォルダ `.`)。

```
python3 sign_interp.py r6.sn --sys=.
```

**実行結果**

```
書いたバイト数 16
足して書く 16
大きさ 32
あるか 1
読んだバイト数 32
hello from Sign;hello from Sign;
無いファイルを読む -2
あるか 0
0
```

フォルダの中に `memo.txt` ができ、中身は `hello from Sign;hello from Sign;` でした。

**ひとこと** 失敗したときは、`-2`(見つからない)のように「-エラー番号」が返ります【拡張】。`--sys` を付けないと、ファイルの関数は `__` を返すので、`yes` の行は何も出ませんでした(`file_exists` だけは 0 を返しました)【拡張】。`--sys` のしくみは[第4巻](04_sound-parts-files.md)でも扱っています。

**確かめていないこと** 作業フォルダの外にあるファイルを開こうとしたときの結果は、確かめていません。

## 第2章 書いたものを実行せずに確かめる

この章の道具は、プログラムを動かさずに、読んで調べて知らせてくれます。すべて【拡張】で、仕様にはありません。「断り」は、このまま使うと困る形として出す知らせ、「注意」と「参考」は断りではない知らせです。

### レシピ6 実行せずに整合を調べる(--check)

**やりたいこと** あるプログラムに、同じ名前の重複定義や、定義の無い名前がないか、動かさずに知る。

```
double : x ? x * 2
twice : x ? double (double x)
double : x ? x + x
unused_fn : a ? a
total : n ? (twice n) + missing
total 5
```

これを `c1.sn` として保存し、調べます。

```
python3 sign_interp.py --check c1.sn
```

**実行結果**

```
c1.sn:3:1: hint [duplicate-definition] double: double は 1 行目にも定義があります(後の定義が前を隠します)
c1.sn:5: note [undefined-identifier] total: missing

c1.sn: 断り 0 件 / 注意 1 件 / 参考 1 件
```

終了コードは 0 でした。`unused_fn` は、どこからも使われていませんが、既定では出ません。`--unused` を付けると出ます。

```
python3 sign_interp.py --check c1.sn --unused
```

```
c1.sn:3:1: hint [duplicate-definition] double: double は 1 行目にも定義があります(後の定義が前を隠します)
c1.sn:4:1: hint [unused-definition] unused_fn: unused_fn はどこからも使われていません(公開 # でもありません)
c1.sn:5: note [undefined-identifier] total: missing

c1.sn: 断り 0 件 / 注意 1 件 / 参考 2 件
```

機械で読むときは `--json`、参考を消すときは `--no-hint` を付けます。文法の誤りは、終了コード 2 で知らせます。

```
f : x ? x +
f 3
```

```
c2.sn:1: error [syntax] 式が必要です
```

この終了コードは 2 でした。整合しているプログラムでは、`断り 0 件 / 注意 0 件 / 参考 0 件  → 整合しています` と出ます(第1章で使った `std_demo.sn` も、このとおりでした)。

**ひとこと** 同じ名前を二度定義したとき、後の定義が前を隠すというのは、この道具の知らせです【拡張】。この動きが仕様にあるかは、確かめていません。定義の無い名前 `missing` は、断りではなく注意です。このプログラムを実際に動かすとどうなるかは、このレシピでは確かめていません。

### レシピ7 より厳しく確かめる(--strict)

**やりたいこと** 実行すると動いてしまうが、よい書き方ではない形を見つける。ここでは `--strict` を、既定のモードを置き換えるものではなく、確かめる道具として使います。

```
f : [y : 1] ? y
f 2
```

仮引数の括りに、既定値を書いた関数です(`[y : 1]`)。括りは参照の口で、既定値は持てません(R131)。保存したファイル `s1.sn` を、次の3つの実行方法で試します(結果の表には、指定を付けない `--check` の行も添えています)。

```
python3 sign_interp.py s1.sn
python3 sign_interp.py --strict s1.sn
python3 sign_interp.py --check s1.sn --strict
```

**実行結果**

| 実行 | 結果 |
| --- | --- |
| 既定で実行 | `2` を出して終わり(終了コード 0) |
| `--strict` で実行 | `エラー: s1.sn:1:11: param-default-bracket: 仮引数の括りに、既定値の行があります(y : …)。…文法に無い形なので、読む段で止めます(§4 R131)`(途中を省略しています。終了コード 1) |
| `--check` | 断り 0 件、整合しています |
| `--check --strict` | `s1.sn:1:11: error [strict-parse] <parse>: param-default-bracket: 仮引数の括りに、既定値の行があります(y : …)。…文法に無い形なので、読む段で止めます(§4 R131)`(途中を省略しています。断り 1 件、終了コード 1) |

**ひとこと** 同じプログラムで、既定では動き、`--strict` では断られます。`--check --strict` は、動かさずに、`--strict` の実行と同じ括りの問題を指しました。この `--strict` は、確かめるためのモードです【拡張】。この巻の他の例は、すべて既定のモードで実行した結果です(第1章の `--strict` は、同じ結果になるかを確かめるために、あとから実行したものです)。ただし【仕様】`value_spec.md` の V9 は「定義でない行の値はファイルでは捨てる」と書き、【実装】この実装は 2026-11-04 22:40 の版から `--strict` でそれに合わせたので、`--strict` で走らせると最後の行の値は画面に出ません(`print` などで出した文字は出ます)。この巻で「`--strict` でも同じ」と書いた所は、値を取り出して既定と比べた結果です。

**確かめていないこと** `--strict` の断りのうち、実行しないと決まらない種類は、`--check --strict` では調べられません。このレシピで確かめたのは、仮引数の括りに既定値を書いた上の形だけです(この例は以前の版では、仮引数が関数を隠す形でした。それは仕様の R133 で断りでなく知らせになったので、例を替えました。[第9巻](09_messages-and-errors.md)にその形があります)。

### レシピ8 番地の範囲の外を見つける(境界の検査)

**やりたいこと** 使ってよいと決めたメモリの範囲(ここでは 0x500000 から、大きさ 0x1000)の外へ、書き込んでしまうことを見つける。

```
seq2 : a b ? b
ok : z ? seq2 (0x500000 # 1) (0x500FFC # 2)
bad : z ? 0x501000 # 3
seq2 (ok 0) (bad 0)
```

範囲を宣言しない普通の実行と、宣言して実行する場合と、実行しない静的な検査を、すべて `b1.sn` に対して試します。

```
python3 sign_interp.py b1.sn
python3 sign_interp.py b1.sn --check-bounds --ram=0x500000:0x1000
python3 sign_interp.py --check b1.sn --bounds --ram=0x500000:0x1000
```

**実行結果**

| 実行 | 結果 |
| --- | --- |
| 普通の実行 | `5246976`(0x501000)を出して終わり。どこへ書いても断られない |
| `--check-bounds --ram=…` | `エラー: b1.sn:3:11: 境界: 書き込みの番地 0x501000 は、装置の帯と --ram で宣言した範囲のどれにも入っていません`(終了コード 1) |
| `--check --bounds --ram=…` | `b1.sn:3:11: error [bounds-static] bad: 境界: 書き込みの番地 0x501000 は、装置の帯と --ram で宣言した範囲のどれにも入っていません`(断り 1 件、終了コード 1) |

**ひとこと** `a # v` が書けたときに、その番地を返すのは、仕様にあります【仕様】。普通の実行の結果 `5246976` は、最後に書いた番地 0x501000 です。範囲の検査で確かめたのは、書き込みの番地が字面で決まる形だけです。実行時の検査と静的な検査は、このプログラムで同じ番地を指しました。この検査は、範囲を宣言したときだけ働き、宣言しないのは普通の実行と同じです【拡張】。

**確かめていないこと** 実行しないと番地が決まらない書き込み(計算して決まる番地など)を、静的な検査で見つける例は、確かめていません。

### レシピ9 構文木を S 式と後置で書き出す(--sexp・--forth)

**やりたいこと** 書いたプログラムを動かさずに、どういう木として読まれたか(どこで区切られ、どちら向きに結ばれたか)を見る。

```
f : x y ? x + y
f 1 2
a : 1 - 2 - 3
b : 2 ^ 3 ^ 2
0x500000 # 1 # 2
```

これを `r9.sn` として保存し、2通りに書き出します。

```
python3 sign_interp.py --sexp r9.sn
python3 sign_interp.py --forth r9.sn
```

**実行結果**(`--sexp`)

```
(setq f (lambda (x y) (+ x y)))
(coproduct f 1 2)
(setq a (- (- 1 2) 3))
(setq b (expt 2 (expt 3 2)))
(output (address 5242880) (output 1 2))
```

**実行結果**(`--forth`)

```
f [ x y ] [ x y + ] ? :
f 1 2 3 coproduct
a 1 2 - 3 - :
b 2 3 2 ^ ^ :
5242880 1 2 # #
```

どちらも終了コードは 0 で、プログラムは実行されません(`f 1 2` の答えも、`#` の書き込みも起きていません)。標準入力から読むときは、ファイル名の代わりに `-` を書きます。文法の誤りがあるプログラムは、`エラー: 式が必要です` のように知らせて、終了コード 1 で終わります。

**ひとこと** 見るところは結ぶ向きです。`1 - 2 - 3` は `(- (- 1 2) 3)` と左から結ばれ、`2 ^ 3 ^ 2` は `(expt 2 (expt 3 2))` と右から結ばれました。`#` も、`(output (address 5242880) (output 1 2))` のとおり右から結ばれます。中置の `#` が右結合であること(`:` `?` `,` `^` `@` も右結合)は、仕様書の演算子表にあります【仕様】。この実装は以前、`#` を左結合に読んでいましたが、2026-11-07 に仕様に合わせて直しました【実装】。

`--sexp` と `--forth` は、構文だけを写します。`_` を吸収する、比べが左の値を返す、0 で割ると `_` になる、といった意味は写していないので、出力は Lisp や Forth で動かせる形ではありません。`f : x y ? x + y` の書き出しは、設計者が GitHub の Discussions #40 に書いた例の並びに合わせました【拡張】。この2つの指定は、仕様にも配布の資料にもなく、この実装に添えた道具です【拡張】。S 式の演算子の名前(`expt`・`output`・`coproduct` など)と、`--forth` の語の綴りは、この実装で決めたものです【拡張】。空白で並べた形は、呼び出しなのか並べて組む形なのかを、意味の段が決めるので、ここでは `coproduct` として書いたとおりに残します。

**確かめていないこと** 38 本の見本はすべて、落ちずに括弧が釣り合って書き出せることだけを確かめました。見本ごとの書き出しの中身が、読み手の期待どおりかは、一つずつは確かめていません。Lisp や Forth の処理系に渡して動かす試みも、していません。

## 付録 コマンドと関数の一覧

### 実行したコマンド

| やりたいこと | コマンド |
| --- | --- |
| 普通に実行する | `python3 sign_interp.py file.sn`(`std.sn` を同じフォルダに置く) |
| ファイルの関数を使う | `python3 sign_interp.py file.sn --sys=.` |
| 実行せずに調べる | `python3 sign_interp.py --check file.sn` |
| 未使用の定義も出す | `python3 sign_interp.py --check file.sn --unused` |
| 参考を消す | `python3 sign_interp.py --check file.sn --no-hint` |
| 機械で読む形で出す | `python3 sign_interp.py --check file.sn --json` |
| より厳しく実行する | `python3 sign_interp.py --strict file.sn` |
| より厳しく、実行せずに調べる | `python3 sign_interp.py --check file.sn --strict` |
| 実行中の番地の範囲を見る | `python3 sign_interp.py file.sn --check-bounds --ram=始まり:大きさ` |
| 範囲を実行せずに調べる | `python3 sign_interp.py --check file.sn --bounds --ram=始まり:大きさ` |
| 構文木を S 式で書き出す | `python3 sign_interp.py --sexp file.sn` |
| 構文木を後置で書き出す | `python3 sign_interp.py --forth file.sn` |

`--check` の終了コードは、断りが無ければ 0、あれば 1、文法の誤りなどで読めないときは 2 でした【拡張】。

### この巻で使った std.sn の関数

| 種類 | 関数 |
| --- | --- |
| 数 | `clamp` `sign` `gcd` `lcm` `isqrt` `ipow` `fdiv` `fmod` |
| 乱数 | `rand_seed` `rand_int` `rand_range` |
| 並び | `arr_get` `arr_set` `arr_sum` `arr_max` `arr_min` `arr_find` `arr_reverse` `arr_sort` `arr_sorted` `arr_bsearch` |
| 文字列 | `str_put` `str_len` `str_cat` `str_cmp` `str_find` `str_starts` `str_ends` `str_sub` `str_upper` `str_lower` `str_trim` `str_reverse` `str_split` |
| 変換 | `str_int` `str_to_int` `str_is_int` `str_hex` |
| 出す | `print` `println` `print_mem` `println_mem` `print_int` `println_int` `newline` |
| ファイル | `write_file` `append_file` `read_file` `file_size` `file_exists` |

この一覧に無い関数も `std.sn` にありますが、この巻では動かしていません。すべて【拡張】です。

---

<!-- nav -->
[← 前: 第5巻 ブロックでゲーム](05_blocks-game.md) | [目次](README.md) | [次: 第7巻 大きなゲームを読む →](07_reading-suika.md)
<!-- /nav -->
