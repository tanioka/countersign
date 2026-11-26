# pi_stack — 深い再帰でスタックが尽きたときの確認(Raspberry Pi)
`sh run_on_pi.sh` を実行して、できた `report.txt` を返してください。
期待: s_ok は out=50005000 rc=0。s_deep は rc=1 で err に「sign: stopped by a memory fault …」(SIGSEGV の rc=139 で落ちないこと)。s_branch は rc=1 と同じ知らせか、out=500000 rc=0(どちらでもよい。落ちる rc=139 は不可)。
