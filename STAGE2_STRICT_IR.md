# 第二段階: strict から機械語への意味保存

旧 AST の補正(`strict_rewrite` の 6 パッチ、`strict_divergences`、`strict_call_check`)だけに頼らず、strict の正規化された中間表現 SIR を定め、評価器と生成コードの観測結果を照合する。

## SIR(`sign_sir.py`)
ノード: `int / void / var / op / neg / cmp / chain / and / or / rows / call / flow`。
- void の被演算子は算術で単位として消える(`5 + _` = 5、`0 - _` = 0)。両方 void なら void。0 で割れば void。
- `-_` は void(`0 - _` とは別なので `neg` を独立させた)。
- 値域は -MAX..MAX。MIN に着いたら void。
- 比べの連鎖は `chain`: 3 項の範囲は真ん中の項、`=`/`==` の連鎖は最初の項。それ以外の連鎖は `Unsup`。
- 下げられない形は `Unsup(理由)` で断る。理由の集計が次の作業リスト。

## 観測モデル(`diff_observe.py`)
obs = 値 / void / 罠 / 断り / 未対応。照合は二段。
1. 前段: strict 評価器 = SIR 評価。不一致は SIR の誤り。
2. 後段: SIR = 機械語(エミュレータ)。機械語の断り・罠は許す。違う答えだけが失敗。

## 現状(整数 CASES 177 件)
前段 一致 144 / 部分適用 7 / 未対応 26 / 食い違い 0。後段 断り 134 / 罠 10 / 誤答 0。

## 段階
- A(済): SIR と評価器の前段照合。
- B: 未対応の削減(`'`、`norm`、一般の連鎖、文字列・リスト)。FLOWS・STR_CASES・乱数テストへ広げる。
- C: asm が AST 補正の代わりに SIR を読む。`strict_rewrite`/`strict_divergences` を SIR 由来に置換し、機械語が断る件数を下げる。
- 受け入れ: 前段 0 食い違い、後段 誤答 0、断りの理由が全て列挙されていること。
