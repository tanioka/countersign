# pi_intneon — Int の List の NEON 化を、作る前に測る(Raspberry Pi 4)
`python3 run_on_pi.py`(5 回)。できた `report.txt` を返してください。
手書きの AArch64(`bench.S`)。map `(x + x) + 1` と畳み `[+]` を、スカラー(溢れは `adds` + `csel` で `!_`)と NEON(2 レーン × 2 本、溢れは粘着ビットで検出して、あればスカラーでやり直し)で比べる。
NEON に 64 ビットの掛け算は無いので、`+ - シフト・比べ` だけが対象。差が小さければ見送る。
