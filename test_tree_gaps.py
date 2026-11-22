"""tree_gaps.py の分類(読まない形は None、見本の外の広げは木を出す)が実装の今と合っているか。ずれたら designer_questions_tree_2026-11-22.md を直す"""
import tree_gaps as G
bad = 0
for kind, src, defs, got, q in G.run():
    if (kind == "refuse") != (got is None): bad += 1; print("NG", kind, repr(src), got)
print("全部 ok" if not bad else f"{bad} 件 NG"); raise SystemExit(1 if bad else 0)
