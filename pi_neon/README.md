# pi_neon — NEON と --par の実機照合(Raspberry Pi 4)
`python3 run_on_pi.py` を実行して、できた `report.txt` を返してください(何もつながない。外へ出ない)。
- NEON(n000〜): Float / Vector の演算・`__` の持ち回り・`[op] (map $g xs)` の融合の 83 本。期待は処理系(`--check-f32` = binary32 のレーン)。
- --par(t_par_…_s / _p2 / _p3 / _p4): 同じ答えが出るか、時間が縮むか(Pi 4 は 4 コア。重い関数の兄弟呼びが 2 本あれば直列の 2 倍近く)。
他の処理が走っていると時間がぶれます。時間は参考値です。
