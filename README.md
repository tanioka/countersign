# countersign

プログラミング言語 **Sign** の実装(Python 製のインタープリタと、AArch64 向けのコンパイラ)と、その試験・実装ノートをまとめたリポジトリです。

> **初稿です。** 内容は作業の記録から起こしたもので、設計者の確認は受けていません。
> Sign の言語仕様は設計者のリポジトリの `documents/` が正で、このリポジトリは仕様を決めません。実装が仕様と食い違うときは実装を直し、仕様の側の疑問は [`QUESTIONS_FOR_DESIGNER_2026-11-17.md`](QUESTIONS_FOR_DESIGNER_2026-11-17.md) に記録します。

## 本

Sign 入門と全12巻のレシピ集は [books/](books/README.md) にあります。

## 仕様と実装の関係

- **【仕様】** 設計者の `documents/`(最優先)。実装の `alpha` は先行した実装、`alpha1` はその作り直しです。`documents/` の更新が実装に遅れることもあるので、食い違いが更新の遅れに見えるときは、そう書き添えます。
- **【実装】** このリポジトリの挙動。仕様が決めていない所は実装の都合で決めており、`IMPLEMENTATION_NOTES.md` に区別して書いています。

## 2つのモード

| モード | 読み方 | 使いどころ |
|---|---|---|
| 既定 | 従来の読み。サンプルや実行例はこちら | 普段の実行 |
| `--strict` | 仕様どおりの読み(`STRICT_GATES`)。断る形・知らせる形が増える | 仕様との照合 |

`--strict` でファイルを実行すると、定義でない行の値は表示されません(仕様 value_spec V9「定義でない行の値はファイルでは捨てる」)。値を見たいときは `println` などで出力するか、REPL に入力します。既定のモードは、最後の行の値を表示します。

コンパイラ(`--asm`)は既定の読みに従います。`--strict --asm` は別の道(`strict_rewrite`)を通ります。

## 使い方

Python 3 だけで動きます(インタープリタ側は追加のパッケージ無し)。

```sh
python3 sign.py hello.sn                 # 実行(既定のモード)
python3 sign.py --strict hello.sn        # 仕様どおりの読みで実行
python3 sign.py --asm prog.sn --target=linux -o prog.s   # AArch64 のアセンブリを出す
python3 sign.py --asm prog.sn --elf=prog                  # ELF を出す
python3 sign.py --emit-st mod.sn         # 公開(#)の名前から mod.st を書く
python3 sign.py --tree hello.sn          # 仕様 §1.3 の「出力の木」(construct・apply・compose・unit)を出す。出せない形は「未対応」
```

- `sign.py` は `sign_interp.py` の起動口です。`std.sn`(標準の定義)と `sign_st.py` は `sign_interp.py` と同じフォルダに置いてください。
- コンパイラのオプション一覧は `python3 sign.py --asm` の使い方表示(`sign_asm.py` の `USAGE`)にあります。最適化の切り替えは `--no-opt`・`--no-peephole`・`--no-fuse`・`--no-share`・`--no-hoist`・`--no-scalar`・`--no-neon`・`--no-lint`・`--no-estimate` です。
- コンパイラの対象は AArch64 だけです(`--target=bare|linux`)。Windows・x86-64 は見積もりだけで、コードは出しません。

## かんたんインストール

インタープリタと `std.sn` だけを入れます(コンパイラ `--asm`・試験・本は入りません)。Python 3.12 以上が要ります。置き場所は `install_manifest.txt` が決めます。

- **Linux**: `curl -fsSL https://raw.githubusercontent.com/tanioka/countersign/main/install.sh | sh`(`~/.sign` に置き、`~/.local/bin/sign` を作る。消す: `sh install.sh --uninstall`)
- **Windows 11**: `irm https://raw.githubusercontent.com/tanioka/countersign/main/install.ps1 | iex`(`%LOCALAPPDATA%\Sign` に置き、利用者の PATH に足す。消す: `& ([scriptblock]::Create((irm https://raw.githubusercontent.com/tanioka/countersign/main/install.ps1))) -Uninstall`)

`install.sh` は Linux で試験済み(`test_install.py`)。`install.ps1` は Windows 11 の PowerShell で、入れる(`irm | iex`)・`sign` の実行・消す(`-Uninstall`、PATH からも外れる)を実機で確認済みです(2026-11-24)。`test_install.py` が見るのは中身の取り決めだけで、Windows の動作そのものは自動では試していません。

## 主なファイル

| ファイル | 内容 |
|---|---|
| `sign.py` / `sign_interp.py` | 起動口 / インタープリタ本体 |
| `sign_asm.py` と `sign_opt.py`・`sign_peep.py`・`sign_fuse.py`・`sign_inline.py`・`sign_neon.py`・`sign_plan.py` ほか | AArch64 コンパイラと最適化 |
| `sign_st.py` | `--emit-st`(`.st` の書き出し) |
| `std.sn` | 標準の定義(実装側で決めたもの)。置き場所は番地で渡します(`0x500000` と書く)。`--strict` では素の数を渡せません(仕様 R62: 番地と素の数は混ぜられず、数から番地を作る射がありません) |
| `sign_sir.py` / `diff_observe.py` / `fuzz_sir.py` / `diff_str.py` | strict の正規化中間表現 SIR と、評価器・SIR・機械語の 3 者照合(見本表 `diff_observe.py`・乱数 `fuzz_sir.py --asm`・文字列表の作業リスト `diff_str.py`)。旁路 `--asm --strict --via-sir`。設計は `STAGE2_STRICT_IR.md` |
| `spec_audit.py` / `spec_track.py` / `spec_tree.py` | 仕様書の見本との突き合わせ(`spec_audit.py 仕様書.md`)/ 公式の R 規則・V 規則の見本を規則別に数え、前回との差を出す(`spec_track.py [仕様リポジトリ] [--save] [-v]`、毎日 `.github/workflows/spec-track.yml`)/ `--tree` の木の出力。設計は `TREE_SHARING_DESIGN.md` |
| `test_*.py` | 試験。`test_laws.py` は仕様の法則、`test_origin.py`・`test_law5253.py`・`test_xfile.py`・`test_st.py` ほかは個別の仕様項目 |
| `*.sn` | サンプルと実行例(既定のモードで動かす) |
| `IMPLEMENTATION_NOTES.md` | 実装ノート。日付ごとの変更・精査表・設計メモ |
| `QUESTIONS_FOR_DESIGNER_*.md` | 仕様の側の疑問(設計者へ渡す) |
| `DESIGN_*.md` / `GAP_*.md` | 設計メモと、仕様との差の一覧 |

## 試験

```sh
python3 test_laws.py        # 仕様の法則(3165 件。内訳は下の「test_laws.py の件数」)
python3 test_origin.py      # `' _`(コンストラクタ由来)ほか
python3 test_law5253.py     # 法則52・53
python3 test_asm.py         # コンパイラ(エミュレータで走らせて比べる)
```

### 自動実行(GitHub Actions)

`.github/workflows/tests.yml`: push・pull request で、(1) `smoke`(Python 3.12・3.13。通常の実行・`--version`・`suika.sn --check` と速い試験)、(2) `test_*.py` を 1 本ずつ別の job で走らせる(Python 3.13、1 本 60 分まで)。遅い試験が他に響かないよう、分けてあります。試験の一覧は `ls test_*.py` から作るので、新しい試験は足すだけで入ります。

**実績**: この workflow は GitHub 上で走っています。2026-11-24 の時点で、直近 40 回の `tests` は、成功 14・取り消し 24(連続 push で前の実行が打ち切られた分)・失敗 2 です。失敗 2 回はどちらも `test_iot.py` の同じ 3 件で、命令を注ぐ時刻が固定だったため、起動の遅い実行で購読の前に注いで取りこぼしたものでした。購読を待ってから注ぐ形に直してあります(起動を 2 秒遅らせて、直す前は 3 件 NG、直した後は全部 ok)。直した後の実行がまだ無いので、次の push の結果で確かめます。

### test_laws.py の件数

`3165/3165 通った` の「通った」は、全件を両方のモードで比べたという意味ではありません。実行の終わりに出る内訳は次のとおりです(2026-11-21 の実行)。

| 区分 | 件数 | 比べた範囲 |
| --- | --- | --- |
| 既定のモードと `--strict` の両方で期待どおり | 2446 | 全部(`gate`・`warns` など strict にだけ意味がある形と、strict の綴りで書いた法則(`R138/法則31(strict の綴り)` の 363 件と `R138/法則45(strict の綴り)` の 150 件)は strict だけ) |
| `--strict` の比べを省いた | 674 | 旧綴りの手書き(`!_`・`[]`・未定義の名前)が R138 で断られるため、strict の側を比べていない。そのうち既定のモードの側を比べられる形(`val`・`err`・`same`)は 10 件で、全部一致(期待が `only="strict"` の試験は既定の側を比べない)。うち `[]` を計算で生む void `(1 < 0)` に写し、静的の形は旧綴り(`i : !_` など)を σ で写して、strict でも旧い期待どおりと確かめた物が 495 件(値・同値・一致・知らせ・断り・静的のすべての形)。残り 179 件のうち 175 件は、旧い綴りのまま strict が R138 の門で断ること(G22 114・empty-written 60・void-written 1)までを確かめてある。旧い期待そのもの(流れが消える、など)は strict では書けない |
| 旧綴りを σ で写した strict の側が、旧い期待と合わない | 45 | 比べた結果が合わないまま数えていない(`-v` で一覧)。源の綴りのまま strict に通すと、手書きの void を断る(void-written)21・旧い `x : _` の意味が変わって値が出る 13・その他 11 |

つまり、strict と仕様の照合として全部を確かめた件数は 2446 件までです。省いた 674 件と数えなかった 45 件は、「通った」に含まれています。既定のモードの側で食い違う件は 0 件です(`only="strict"` の試験は既定の側を比べない)。

### 結果の区分(PASS / SKIP / 断り)

「通った」の数をそのまま「仕様に合うと確かめた数」と読まないために、結果を次の区分で読みます。区分の名前は この README での呼び名で、試験の出力にそのまま出る語ではありません。

| 区分 | 意味 | 数え方 |
| --- | --- | --- |
| PASS | 実際に動かして、期待(仕様の読み)と一致した | `test_laws.py` の 2446 件(両モード)と、strict の綴りで書いた法則 |
| PASS(写して確認) | 旧綴りを σ で strict の綴りに写し、旧い期待どおりと確かめた | 495 件。写しが正しいことまでは試験が保証しない |
| 断りを確認 | strict が R138 の門(G22・empty-written・void-written)で断ることまで確かめた。期待の値そのものは strict では書けないので比べていない | 175 件。PASS には数えない |
| SKIP | 現在の条件では strict の側を比べていない | 674 件のうち上の 2 区分に入らない残りの 4 件 |
| 未検証(不一致のまま) | 写しても期待が合わない。仕様と食い違うとは限らない(旧い期待の側が古い場合がある) | 45 件。`-v` で一覧。`GAP_R137_R138.md` に分類 |
| FAIL | 期待と違った | 0 件(あれば試験は失敗で終わる) |

`--asm --strict`(コンパイラ。`test_asm_strict.py`)にはもう一つ区分があります。

- **一致**: strict のインタープリタと同じ答えを出した。
- **溢れ**: 整数の溢れ。仕様どうしの食い違いとして記録(`OPEN_QUESTIONS.md` #3)。
- **断る**: コンパイラが「strict の読みと答えが分かれうる」形(`strict_divergences` の 6 つの形)を名指しで断った。誤答ではないが、確かめた数にも入れない。
- **strict が断る**: strict のインタープリタ側が断った(R138 の門など)。比べない。
- 食い違い(断りも一致もしない): 0 件。あれば試験は失敗で終わる。

この表の XFAIL(既知の不一致を期待する区分)にあたるものは作っていません。既知の食い違いは、通ったことにせず、上の「未検証」か `OPEN_QUESTIONS.md` に置きます。

試験は 1 本ずつ実行します。`test_asm*` 系は時間がかかります。まとめて走らせる一覧は作っていません(`IMPLEMENTATION_NOTES.md` の回帰の記録を参照)。

## 状態と既知の限界

- 実装済み(`--strict` 側): R21・R128・R139、`' _`(`type_system.md` §6.2)、枚をまたぐ・同じ枚の同名の扱い(`compiler_pipeline.md` §4)、`--emit-st` のデータ部分。
- 未実装: 型の観測と解決キャッシュ・`.st` の関数署名・`src`/`test` を使う `sign build`(`compiler_pipeline.md` §6)、`asm_volatile`(仕様に綴りの定めが無い)。
- 【実装】`--strict` の入れ子の深さの上限(value_spec V10)は、仕様の基準 10,000 に対し、実行時の再帰の上限から導いた値(コマンドでは 6237 段)です。上限に届いた呼びは `_` と `resource-depth` の知らせになります。値は仕様が「実装の都合」とする所ですが、深く再帰する(終わりの無い再帰を含む)プログラムの途中の値は、この上限で変わります。
- 既定の道は、同名の扱いなどで `compiler_pipeline.md` と食い違います(既定は変えない方針)。一覧は `IMPLEMENTATION_NOTES.md` の「compiler_pipeline.md の精査」の表です。

詳しい経緯と、各項目が【仕様】か【実装】かの区別は、`IMPLEMENTATION_NOTES.md` を読んでください。

## ライセンスと出どころ

このリポジトリは、Sign 言語の **派生した実装**(インタープリタとコンパイラ)です。オリジナルのリポジトリは [johnny-shaman/Sign](https://github.com/johnny-shaman/Sign) で、**Sign Language License** に従います(全文は [`license/`](license/) に写しを置きました。正は上記リポジトリの `documents/License/` です)。

- 言語の設計・仕様・公式の実装例の著作権は、制作者の岡崎 登に帰属します(ライセンス §1・§2)。
- 派生したコンパイラを公開するときは、オリジナルのリポジトリを示し、ライセンスを維持すること(§2)。この節はそのための表示です。
- Sign の実装は、公式・コピー・改変を問わず、一部でも**販売しません**(§2)。
- 無保証・「現状のまま」の提供です(§6)。準拠法は日本法です(§7)。

この節は、ライセンスの要点を実装側の言葉で写したものです。条文の解釈は、`license/` の全文とオリジナルのリポジトリを正としてください。

設計者(岡崎 登氏)には、このリポジトリの公開について確認しました。返事は「取り敢えず、無断で商用利用だけする場合は自己責任としているだけですので大丈夫です」(要旨。2026-11-19、リポジトリの持ち主を通じて受領)でした。したがって、公開と、Sign Language License の範囲での利用は差し支えありません。ただし、これは設計者からの口頭に近い回答で、このコード独自の別ライセンスを付与するものではありません。このリポジトリのライセンスは、元の Sign Language License に従います。
