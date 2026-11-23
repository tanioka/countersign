"""木の出力で、仕様の見本の外にある形のうち、実装が読まない(None)か、見本が無いまま出している形を一覧にする。
設計者への質問の元(designer_questions_2026-11-21.md の F 節)を作る。使い方: python3 tree_gaps.py [--md]"""
import sys
import spec_tree as T, spec_audit as A
P = A.PRE.splitlines()
# (番号, 形, 追加の定義, 問い)  kind: refuse=読まない / guess=見本が無いまま出している
PROBES = [
 ("refuse", "gd 3 4 7", [], "既定値のある口の関数に、口より多く(`!_` でありうる括りが無い)渡す形(R83 は「未知」)の木は `(construct (apply gd (construct 3 4)) 7)` か、全部を 1 つの束で渡す `(apply gd (construct 3 4 7))` か(`gd 3 (3 < 2) 7` は後者)"),
 ("refuse", "inc (i w) 5", [], "恒等射が `!_` と分かる値だけ受けた括り `(i w)` を、並びの中に置いたとき `(apply (compose inc [i w]) 5)` か、括りは葉か(根の被演算子 `1 & (i w)` は `(unit [i w])`)"),
 ("refuse", "obj :\n\tm : 1\n\tn : 2", [], "`名前 : 値` だけを字下げで並べた構造体のブロックの木は `(: obj (block (: m 1) (: n 2)))` か(R134 の見本は仮引数のブロックの関数を含む形だけ)"),
 ("refuse", "f : x ?\n\t\ty : 1\n\t? x + y", [], "字下げの仮引数のブロックが関数の本体に付く形は param-block-position で断る(R134)が、断る前の木は無いのか(木を出さないのが正しいか)"),
 ("guess", "[+] inc 5~", [], "撒いた値の流れ `5~`(長さが分からない)を受ける合成 `(apply (compose [+] inc) 5~)` でよいか(見本は `w~` だけ)"),
 ("guess", "inc ||_|| 1 2", [], "囲みの中の関数 `||_||` の前に関数が付く形は `(apply ||_|| (construct (apply inc 1) 2))`(`inc [+] 5 6` と同じ読み)でよいか"),
 ("guess", "tl : [x] y ? x + y", [], "括りの仮引数と名前の仮引数が混ざる関数の定義は `(? [[x] y] (defer {x + y}))` でよいか(見本は括りだけ)"),
 ("guess", "p3 : [a] [b ~bs] [c ~cs] ? a + b + c", [], "括りの仮引数が複数のとき、`(? [[a] [b ~bs] [c ~cs]] (defer {…}))` と並べてよいか"),
 ("guess", "[add,] 1 2", [], "`[F,]` で F の口が 2 つ以上のときの `(construct [add,] 1 2)`(種類が未知の葉)でよいか(見本は `[add,] vs` だけ)"),
 ("guess", "0 | inc", [], "字面の数 `0` と関数の `|`(0 は `!_` でない辺)は `(| 0 (unit inc))` か `0` か(R137 の `w | 5` は `5`、`inc | 5` は `(| (unit inc) 5)`)"),
 ("guess", "(0 | inc) 5", [], "`(3 | inc) 5` と同じ `(construct [0 | inc] 5)` でよいか(0 は値で `!_` でない)"),
]
def run():
    rows = []
    for kind, src, defs, q in PROBES:
        try: got = T.tree_of(src, P + defs)
        except BaseException as e: got = "(例外 %s)" % type(e).__name__
        rows.append((kind, src, defs, got, q))
    return rows
if __name__ == "__main__":
    rows = run()
    if "--md" in sys.argv:
        print("| # | 形 | 実装の今の木 | 問い |\n| --- | --- | --- | --- |")
        for i, (kind, src, defs, got, q) in enumerate(rows, 1):
            s = src.replace("\n", " ⏎ ").replace("\t", "⇥").replace("|", "\\|")
            g = ("読まない(`None`)" if got is None else "`" + str(got).replace("|", "\\|") + "`")
            print(f"| F{i} | `{s}` | {g} | {q.replace('|', chr(92) + '|')} |")
    else:
        for kind, src, defs, got, q in rows: print(f"[{kind}] {src!r} -> {got}")
