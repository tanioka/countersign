"""alpha1 追従: 公式の仕様書(coproduct_spec.md の R 規則・value_spec.md の V 規則)の見本を直接取り込み、
--strict の実際の成功・失敗・診断と突き合わせて、規則ごとに数える。読めずに省いた見本は理由別に別集計する。
使い方: python3 spec_track.py [仕様リポジトリのパス(既定 ../sign-spec)] [--save] [--base 前回.json] [-v]
  --save   結果を spec_track_last.json に書く(次回の比べの土台)
  既定で spec_track_last.json があれば、前回との差(新しい見本・消えた見本・状態の変化)を出す。"""
import sys, re, os, json, hashlib, subprocess
here = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, here)
import spec_audit as A
import spec_tree as T

args = [a for a in sys.argv[1:] if not a.startswith("-")]
repo = args[0] if args else os.path.join(here, "..", "sign-spec")
verbose = "-v" in sys.argv; save = "--save" in sys.argv
base_path = os.path.join(here, "spec_track_last.json")
if "--base" in sys.argv: base_path = sys.argv[sys.argv.index("--base") + 1]
docs = os.path.join(repo, "alpha1", "docs")
try: rev = subprocess.check_output(["git", "-C", repo, "rev-parse", "--short", "HEAD"], text=True).strip()
except Exception: rev = "?"

HEAD = {"coproduct_spec.md": re.compile(r"^####\s+(R\d+)\b"), "value_spec.md": re.compile(r"^###\s+(V\d+)\b")}
VAL = re.compile(r"`([^`]+)`(?:（[^）]*）)?\s*は\s*(`[^`]+`|-?\d+(?![\d.\-])|!_)")
def key(doc, rule, src): return f"{doc}|{rule}|{hashlib.sha1(src.encode()).hexdigest()[:10]}"

def items(doc):
    """(行, 規則, 源, 定義, 期待(right), 種別) を順に出す。種別 R=箇条書きの見本, V=文中の「X は Y」"""
    rule = "(前書き)"
    for n, line in enumerate(open(os.path.join(docs, doc), encoding="utf-8"), 1):
        line = line.rstrip("\n")
        m = HEAD[doc].match(line)
        if m: rule = m.group(1)
        elif re.match(r"^#{1,4}\s", line) and not re.match(r"^####\s+R", line) and doc == "coproduct_spec.md" and not line.startswith("#### "): rule = "(前書き)" if line.startswith(("# ", "## ")) else rule
        if doc == "coproduct_spec.md":
            if "→" in line and line.startswith("- `"):
                p = A.parse(line)
                if p is None: yield n, rule, line[:80], [], None, "R", "源の形が読めない(⏎ でつながる code でない)"
                else: yield n, rule, p[0], p[1], p[2], "R", None
        else:
            for mv in VAL.finditer(line):
                src = A.to_src(mv.group(1)); v = mv.group(2).strip("`")
                why = None
                if re.fullmatch(r"[^\w\s]+", src): why = "演算子の名指しで式ではない"
                elif "|" in v: why = "期待が選択肢の書き方"
                else:
                    known = {l.split(" ")[0] for l in A.PRE.splitlines()} | {"vs"}
                    free = {w for w in re.findall(r"[A-Za-z_]\w*", src) if w not in known and w != "_"}
                    if free: why = "文中の定義が前提で取り込めない(" + ",".join(sorted(free))[:30] + ")"
                yield n, rule, src, [], "値 `" + v + "`", "V", why

res = []; skips = {}
for doc in HEAD:
    for n, rule, src, defs, right, kind, pre_skip in items(doc):
        rec = {"doc": doc, "rule": rule, "line": n, "src": src[:100], "kind": kind}
        if pre_skip: rec["state"] = "skip"; rec["why"] = pre_skip
        else:
            exp, warns, none_w = A.expect(right)
            if exp is None and not warns and not none_w:
                rec["state"] = "skip"
                rec["why"] = ("期待が木(S 式)だけで値・断り・知らせが無い(実装は木を出さない)" if re.match(r"\s*`\(", right) or re.match(r"\s*\d+、`", right) else "期待が値でも断りでも知らせでもない(説明文・括り付きの値など)")
            else:
                names = {re.match(r"#?([\w']+)", d).group(1) for d in defs if re.match(r"#?([\w']+)", d)}
                pre = "".join(l + "\n" for l in A.PRE.splitlines() if l.split(" ")[0] not in names)
                prog = A.fixblank(pre + "\n\n".join(defs) + ("\n\n" if defs else "") + src) + "\n"
                out, err, ws = A.run(prog)
                why = A.judge(exp, warns, none_w, out, err, ws)
                rec["state"] = "ng" if why else "ok"
                rec["actual"] = ("断り: " + err[:60]) if err else out[:60]
                rec["expected"] = (exp[1] if exp and exp[0] == "val" and isinstance(exp[1], str) else (" ".join(exp[1]) if exp and exp[0] == "val" else (exp[1] if exp else "知らせ"))) 
                if warns: rec["expected_warn"] = sorted(warns)
                if why: rec["why"] = why
        mt = re.match(r"\s*`(\([^`]*)`", right or "") if kind == "R" and right else None
        if mt:
            exp_t = re.sub(r"\s+", " ", mt.group(1)).strip()
            names_ = {re.match(r"#?([\w']+)", d).group(1) for d in defs if re.match(r"#?([\w']+)", d)}
            got = T.tree_of(src, [l for l in A.PRE.splitlines() if l.split(" ")[0] not in names_] + list(defs))
            defs_all = [l for l in A.PRE.splitlines() if l.split(" ")[0] not in names_] + list(defs)
            got_e = T.tree_of(src, defs_all, kinds="eval")
            rec["tree_want"] = exp_t
            rec["tree_eval"] = "unsupported" if got_e is None else ("match" if got_e == exp_t else "mismatch")
            if got_e is not None and got_e != exp_t: rec["tree_eval_got"] = got_e; rec["tree_exp"] = exp_t
            rec["tree"] = "unsupported" if got is None else ("match" if got == exp_t else "mismatch")
            if got is not None and got != exp_t: rec["tree_got"] = got; rec["tree_exp"] = exp_t
        rec["id"] = key(rec["doc"], rec["rule"], rec["src"])
        res.append(rec)

KNOWN = {   # 食い違いの切り分け済み。 (規則, 源の先頭) → 理由。数えは「既知」に分ける
    ("R125", "q 1"): "取り込みの誤読: 知らせ名は説明文中の語で、本文は知らせ無し",
    ("R125", "f 0"): "表示の綴り: 実装は `_`、仕様は `!_`(同じ値)",
    ("R99", "io@"): "未実装: 標準ライブラリの取り込み(io@)。仕様も実装は G21 と注記",
    ("R49", "(w != 3) , 5"): "仕様が注記: 実装は知らせ無し(§6.4)",
    ("R62", "04x1000 + 0x3"): "取り込みの誤読: 本文は値 0x1003、後ろの `!_` は別の形の注記",
    ("R62", "0x4000 # $inc"): "取り込みの誤読/仕様が注記: 実装は知らせ無し(§6.4)",
    ("R21", "g :"): "取り込みの誤読: 手で動かすと G22 で断る(定義の読みが PRE との連結で変わる)",
    ("R21", "io@"): "未実装: 標準ライブラリの取り込み(io@)",
    ("R121", "fp 1 , 2 , 3"): "設計者待ち(問い G1): 値の綴りが `1 , 2 , 3` か `[1, 2, 3]` か。木は一致",
    ("R121", "fp 1 2 , 3"): "設計者待ち(問い G1): 同上(`1 , 3` の綴り)",
    ("R133", "bb ' aa"): "設計者の答え(Sign#302 の B1、2026-11-25)が本文より新しい: 欄どうしの値の輪は name-cycle の知らせ + その欄は `!_`(断らない)。実装は知らせを出し、外側の算術が続いて値 2",
}
for r in res:
    if r["state"] == "ng":
        for (rl, pre), why in KNOWN.items():
            if r["rule"] == rl and r["src"].startswith(pre): r["state"] = "known"; r["known"] = why
tot = {"ok": 0, "ng": 0, "skip": 0, "known": 0}
def rule_key(r):
    m = re.match(r"([RV])(\d+)", r); return (m.group(1), int(m.group(2))) if m else ("0", 0)
print(f"仕様リポジトリ HEAD {rev}  ({docs})")
for r in res: tot[r["state"]] += 1
print(f"合計: 一致 {tot['ok']} / 食い違い(未切り分け) {tot['ng']} / 既知の食い違い {tot['known']} / 省略 {tot['skip']}  (見本 {len(res)})\n")
print("規則    一致 食い違い 省略")
byrule = {}
for r in res: byrule.setdefault(r["rule"], {"ok": 0, "ng": 0, "skip": 0, "known": 0})[r["state"]] += 1
for rl in sorted(byrule, key=rule_key):
    c = byrule[rl]
    if verbose or c["ng"]: print(f"{rl:9}{c['ok']:4} {c['ng']:6} {c['skip']:6}")
print("\n省略の内訳(別集計):")
cls = lambda w: re.sub(r"\(.*", "", w)
for why in sorted({cls(r["why"]) for r in res if r["state"] == "skip"}):
    print(f"  {sum(1 for r in res if r['state']=='skip' and cls(r['why'])==why):4}  {why}")
tr = [r for r in res if "tree" in r]
if tr:
    import collections as _c
    c = _c.Counter(r["tree"] for r in tr)
    if "--tree-list" in sys.argv:
        for r_ in tr:
            if r_.get("tree_eval") == "mismatch": print("木 不一致 %s L%s: %r  期待 %s  出力 %s" % (r_["rule"], r_["line"], r_["src"][:70], r_.get("tree_want", "")[:70], r_.get("tree_got", "")))
            if r_.get("tree_eval") == "unsupported": print("木 未対応 %s L%s: %r  期待 %s" % (r_["rule"], r_["line"], r_["src"][:70], r_.get("tree_want", "")[:70]))
    print(f"\n木の突き合わせ(spec_tree.py。仕様の見本 {len(tr)} 件): 一致 {c['match']} / 不一致 {c['mismatch']} / 未対応 {c['unsupported']}")
    ce = _c.Counter(r["tree_eval"] for r in tr)
    print(f"木(評価器に聞く版 kinds=eval): 一致 {ce['match']} / 不一致 {ce['mismatch']} / 未対応 {ce['unsupported']}")
    diff = [r for r in tr if r["tree"] != r["tree_eval"]]
    print(f"  綴り版と評価器版で結果が分かれた見本: {len(diff)} 件")
    if verbose:
        for r in diff: print(f"    {r['rule']} L{r['line']} `{r['src'][:40]}`: 綴り={r['tree']} 評価器={r['tree_eval']}" + (f" 出した {r['tree_eval_got']} / 仕様 {r['tree_exp']}" if r["tree_eval"] == "mismatch" else ""))
    if verbose:
        for r in tr:
            if r["tree"] == "mismatch": print(f"  {r['rule']} L{r['line']} `{r['src'][:40]}`: 出した {r['tree_got']} / 仕様 {r['tree_exp']}")
print("\n既知の食い違い(切り分け済み):")
for r in res:
    if r["state"] == "known": print(f"  {r['rule']} L{r['line']} `{r['src'][:30]!s}`: {r['known']}")
print("\n未切り分けの食い違い:")
for r in res:
    if r["state"] == "ng": print(f"  {r['doc'].split('_')[0]} {r['rule']} L{r['line']}: `{r['src'][:70]}`\n        {r['why']}")

if os.path.exists(base_path):
    old = {r["id"]: r for r in json.load(open(base_path, encoding="utf-8"))["items"]}
    new = {r["id"]: r for r in res}
    added = [k for k in new if k not in old]; gone = [k for k in old if k not in new]
    chg = [k for k in new if k in old and new[k]["state"] != old[k]["state"]]
    print(f"\n前回との差: 新しい見本 {len(added)} / 消えた見本 {len(gone)} / 状態が変わった {len(chg)}")
    for k in chg: print(f"  {new[k]['rule']} `{new[k]['src'][:50]}`: {old[k]['state']} → {new[k]['state']}  {new[k].get('why','')}")
    for k in added:
        if new[k]["state"] == "ng": print(f"  新規の食い違い {new[k]['rule']} `{new[k]['src'][:50]}`: {new[k]['why']}")
if save:
    json.dump({"rev": rev, "items": res}, open(os.path.join(here, "spec_track_last.json"), "w", encoding="utf-8"), ensure_ascii=False, indent=0)
    print("\nspec_track_last.json に保存")
