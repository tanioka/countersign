"""test_depth.py — 入れ子の深さの上限(value_spec V10): 再帰する Int の関数の入口でスタックの残りを見て、足りなければ
その呼び出しは `!_` と information(SIGSEGV に頼らない)。上限の値は実装の都合(R)で、機械語は RLIMIT_STACK(上限 64 MiB)から余白を引いた分。
疑似カーネルの上限は 8 MiB(fake_kernel.rlimit_stack)。"""
import sys
src_ = open("test_inline.py", encoding="utf-8").read().split("SAME = [")[0]
exec(src_)

DEEP = "s : n ?\n\tn = 0 : 0\n\tn + (s (n - 1))\n"
# 浅い再帰は今まで通り(上限に届かない)
a, text = asm_run(DEEP + "s 1000\n")
check("浅い再帰の答え", a.splitlines()[-1] == "500500" and "resource-depth" not in a, a[-120:])
check("再帰する関数の入口に検査が入る", "b.lo _sign_deep" in text)
# 深い再帰: 上限で `!_`。`n + !_` は n なので、答えは上の n の和(その段数 k は実装の上限で決まる)
N = 400000
a, text = asm_run(DEEP + "s %d\n" % N, limit=400_000_000)
lines = a.splitlines()
r = int(lines[-1])
tot = k = 0
while tot < r: tot += N - k; k += 1
check("深い再帰: 知らせが 1 回出る", a.count("resource-depth") == 1, a[:200])
check("深い再帰: 答えは上から k 段の和(下は `!_` で消える)", tot == r and 1000 < k < N, "r=%d k=%d" % (r, k))
# 末尾再帰は深さを使わない(検査も要らない)
a, text = asm_run("loop : n acc ?\n\tn = 0 : acc\n\tloop (n - 1) (acc + n)\nloop 300000 0\n", limit=400_000_000)
check("末尾再帰は上限に届かない", a.splitlines()[-1] == "45000150000" and "resource-depth" not in a, a[-100:])
# 相互再帰(非末尾)
M = "ev : n ?\n\tn = 0 : 0\n\t1 + (od (n - 1))\nod : n ?\n\tn = 0 : 0\n\t1 + (ev (n - 1))\n"
a, text = asm_run(M + "ev 1000\n")
check("相互再帰(浅い)", a.splitlines()[-1] == "1000" and "resource-depth" not in a, a[-100:])
a, text = asm_run(M + "ev 600000\n", limit=400_000_000)
check("相互再帰(深い): 知らせが出て、正常に終わる", "resource-depth" in a and a.splitlines()[-1].isdigit(), a[:200])
# 再帰しない関数・非再帰の呼びには検査が入らない
a, text = asm_run("f : x ? x + 1\nf 5\n")
check("再帰しない関数に検査は入らない", "_sign_deep" not in text, "")
print("全部 ok" if not FAIL else "失敗 %d 件: %s" % (len(FAIL), ", ".join(FAIL)))
sys.exit(1 if FAIL else 0)
