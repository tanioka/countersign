# --strict の読みとコンパイラ(sign_asm)の突き合わせ(2026-11-18)
- `sign_strict.py`: sign.py の代わり。--strict で読み、最後の値を出す(`__`→`!_`、トップレベルの定義の間に空行を入れる)。使うには `/tmp/strictmods/` に `sign_strict.py`・`emu_dev.py`(= emu_dev_strict.py)と、sign_interp.py の `if res and not STRICT_GATES: print(show(res[-1]))` を `if res: print(...)` に替えた `sign_interp_sv.py` を置く。
- `sfz2.py fuzz_xxx.py 種 本数`: ファザーの `sign.py` を sign_strict.py に替えて走らせる(sign.py を直に呼ぶ fuzz_cnt・fuzz_idx・fuzz_ring と、emu_dev を使う fuzz_effdef・fuzz_nested・fuzz_voidlist)。
- `sfz.py fuzz_xxx.py 種 本数`: 処理系の答えを関数 `interp(s)` で取るファザー(fuzz_seqparam・fuzz_nullary・/tmp/fuzz.py)向け。
