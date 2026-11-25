import subprocess, sys
import sign_sir as S
def test_range():
    assert S.I64_MIN == -(2**63 - 1)
def test_front_back_observation():
    r = subprocess.run([sys.executable, "diff_observe.py"], capture_output=True, text=True, timeout=600)
    assert r.returncode == 0, r.stdout[-800:]
def test_fuzz_front():
    r = subprocess.run([sys.executable, "fuzz_sir.py", "800", "7"], capture_output=True, text=True, timeout=600)
    assert r.returncode == 0, r.stdout[-1200:]
def test_fuzz_lists_asm():
    r = subprocess.run([sys.executable, "fuzz_sir.py", "500", "9", "--lists", "--asm"], capture_output=True, text=True, timeout=900)
    assert r.returncode == 0, r.stdout[-1200:]
def test_fuzz_sir_route():
    r = subprocess.run([sys.executable, "fuzz_sir.py", "400", "11", "--asm", "--novoid"], capture_output=True, text=True, timeout=900)
    assert r.returncode == 0, r.stdout[-1200:]
def test_fuzz_flows():
    r = subprocess.run([sys.executable, "fuzz_sir.py", "300", "13", "--flows", "--asm"], capture_output=True, text=True, timeout=900)
    assert r.returncode == 0, r.stdout[-1200:]
import os, tempfile
def _compile(src, *flags):
    with tempfile.TemporaryDirectory() as d:
        p = os.path.join(d, "a.sn"); open(p, "w", encoding="utf-8").write(src)
        r = subprocess.run([sys.executable, "sign.py", "--asm", "--strict", *flags, p, "-o", os.path.join(d, "a.s")], capture_output=True, text=True, timeout=300)
        return r.returncode, r.stderr, open(os.path.join(d, "a.s")).read() if os.path.exists(os.path.join(d, "a.s")) else ""
def test_via_sir_flag():
    rc, err, t1 = _compile("f : x y ?\n\tx > y : x / y\n\tx + 1\nf 3 4\n", "--via-sir")
    assert rc == 0 and "SIR 経由で出します" in err and t1
    rc, err, text = _compile("c : \\a\n(c + 1)\n", "--via-sir")               # 文字の足し算は SIR の外: 旧経路で出る
    assert rc == 0 and "旧経路で出します" in err and text
    rc, err, text2 = _compile("f : x y ?\n\tx > y : x / y\n\tx + 1\nf 3 4\n")     # 旗なしも SIR 経由(既定。2026-11-25)。黙って出す
    assert rc == 0 and "via-sir" not in err and text2 == t1
    rc, err, text3 = _compile("f : x y ?\n\tx > y : x / y\n\tx + 1\nf 3 4\n", "--no-sir")   # 旧経路だけ
    assert rc == 0 and "via-sir" not in err and text3
    # 機械語が SIR の木を断る形は旧経路でやり直す(`||s ' __||` は strict で 0)。旧経路だけでも、既定でも同じ出力
    P = "s : `ce`\nk : 1\n||s ' __||\n"
    rc, err, t_def = _compile(P); rc2, err2, t_old = _compile(P, "--no-sir"); rc3, err3, _ = _compile(P, "--via-sir")
    assert rc == 0 and rc2 == 0 and rc3 == 0 and t_def == t_old and "やり直します" in err3
def test_fuzz_defaults():
    r = subprocess.run([sys.executable, "fuzz_sir.py", "300", "23", "--defaults", "--asm"], capture_output=True, text=True, timeout=900)
    assert r.returncode == 0, r.stdout[-1200:]
def test_fuzz_names():
    r = subprocess.run([sys.executable, "fuzz_sir.py", "500", "29", "--names", "--asm"], capture_output=True, text=True, timeout=900)
    assert r.returncode == 0, r.stdout[-1200:]
def test_fuzz_partial_rows():
    r = subprocess.run([sys.executable, "fuzz_sir.py", "400", "41", "--partial", "--asm"], capture_output=True, text=True, timeout=900)
    assert r.returncode == 0, r.stdout[-1200:]
def test_fuzz_strings():
    r = subprocess.run([sys.executable, "fuzz_sir.py", "500", "53", "--strings", "--asm"], capture_output=True, text=True, timeout=900)
    assert r.returncode == 0, r.stdout[-1200:]
def test_strings_lower_and_refuse():
    import sign_sir as R, sign_interp as S
    def ev(src):
        f, top = R.lower(S.parse_source(src)); return R.evaluate(f, top)
    assert ev("s : `abc`\n||s||\n") == ("val", 3)
    assert ev("\\a\n") == ("chr", 97)
    assert ev("s : `abc`\ns ' 1\n") == ("chr", 98) and ev("s : `abc`\ns ' -1\n") == ("chr", 99)
    assert ev("s : `abc`\ns ' 5\n") == ("void",) and ev("s : `abc`\ns + 1\n") == ("void",) and ev("s : `abc`\n5 + (s + 1)\n") == ("val", 5)
    assert ev("s : `abc`\ns * 2\n") == ("str", "abcabc") and ev("s : `abc`\ns * 0\n") == ("void",) and ev("s : `abc`\ns * -1\n") == ("void",)
    assert ev("s : `abc`\n2 * s\n") == ("void",) and ev("s : `abc`\ns * s\n") == ("void",) and ev("s : `abc`\n||s * 3||\n") == ("val", 9)
    assert ev("s : `abc`\n(s ' 1) + 1\n") == ("chr", 99) and ev("\\a - \\b\n") == ("val", -1) and ev("3 * \\a\n") == ("val", 291)
    assert ev("\\a * 3\n") == ("str", "aaa") and ev("\\a + \\b\n") == ("void",) and ev("\\a + 100\n") == ("void",) and ev("\\a / 2\n") == ("void",)
    for bad in ["\\a - 97\n", "\\a < \\b\n", "s : `h\u00e9`\n||s||\n"]:
        try: ev(bad); assert False, bad
        except R.Unsup: pass
    f, top = R.lower(S.parse_source("5 & \\a\n"))
    try: R.raise_ast(f, top); assert False
    except R.Unsup: pass
def test_old_route_char_unit_plus_int_traps():
    # (s ' 9) + 1 は strict・既定とも 1(Char の `__` は演算の口で消える)。旧経路の機械語は `__` を返していたので、罠にした
    import sign_interp as S, sign_asm
    sign_asm.STRICT[0] = True
    try:
        tree, rest = sign_asm.strict_rewrite(S.parse_source("s : `abc`\n(s ' 9) + 1\n"))
        assert not rest and ".Ltrap" in sign_asm.generate(tree, "linux")
    finally: sign_asm.STRICT[0] = False
def test_norm_of_partial_application_is_void():
    # `||g 1||`(g は 2 口で余った関数)は囲みごと `!_`(R27)。`||_||` の 0 とは別。SIR が 0 と答えていた
    import sign_sir as R, sign_interp as S
    f, top = R.lower(S.parse_source("g : x y ? x + y\n||g 1||\n"))
    assert R.evaluate(f, top) == ("void",)
def test_strings_through_functions():
    import sign_sir as R, sign_interp as S
    def ev(src):
        f, top = R.lower(S.parse_source(src)); return R.evaluate(f, top), f, top
    assert ev("f : x ? ||x||\nf `abcd`\n")[0] == ("val", 4)
    assert ev("f : x ? x ' 1\nf `abc`\n")[0] == ("chr", 98)
    assert ev("f : x ? x\nf `abc`\n")[0] == ("str", "abc")
    v, f, top = ev("f : x ? x + 1\nf `abc`\n")
    assert v == ("void",)
    try: R.raise_ast(f, top); assert False
    except R.Unsup: pass
def test_fuzz_strings_functions():
    r = subprocess.run([sys.executable, "fuzz_sir.py", "600", "61", "--strings", "--asm"], capture_output=True, text=True, timeout=900)
    assert r.returncode == 0, r.stdout[-1200:]
def test_structs_fields_and_constructors():
    # S3・S5: 欄ブロックと `'` の欄引き・コンストラクタ。strict の答えと同じ。機械語へは戻さない(Unsup)
    import sign_sir as R, sign_interp as S
    P = "p :\n\ta : 1\n\tb : 2\n\tc : 7\n"
    def ev(src):
        f, top = R.lower(S.parse_source(src)); return R.evaluate(f, top)
    assert ev(P + "p") == ("rec", "[a: 1, b: 2, c: 7]")
    assert ev(P + "p ' a") == ("val", 1) and ev(P + "p ' -1") == ("val", 7) and ev(P + "p ' 3") == ("void",)
    assert ev(P + "p ' `b`") == ("val", 2) and ev(P + "k : 1\np ' k") == ("void",) and ev(P + "||p||") == ("val", 3)
    assert ev("p :\n\ta : 1\n\tb : (3 < 2)\n\tc : b\np") == ("rec", "[a: 1, b: !_, c: !_]")
    assert ev("Pt : x y ? [\n\tl : x\n\tn : x + y\n]\n(Pt 3 4) ' n") == ("val", 7)
    for bad in (P + "p + 1", "p :\n\ta : 1\n\ta : 2\np ' a"):
        try: ev(bad); assert False
        except R.Unsup: pass
    f, top = R.lower(S.parse_source(P + "p ' a\n"))
    try: R.raise_ast(f, top); assert False
    except R.Unsup: pass
def test_designer_302_duplicates_and_constructor_names():
    # 設計者の答え 2026-11-25(Sign#302): 同じ枚の同名は知らせて `!_`(2 (c))、欄の右辺の自分の名前は 1 つ外を指す・値の輪は `!_`(3)。strict と SIR が同じ
    import sign_sir as R, sign_interp as S
    def ev(src):
        f, top = R.lower(S.parse_source(src + "\n")); return R.evaluate(f, top)
    assert ev("x : 5\nx : 6\nx") == ("void",) and ev("f : x ? 1\nf : x ? 2\nf 0") == ("val", 0) and ev("a : 1\na : 2\nb : 7\nb + a") == ("val", 7)
    assert ev("Point : x y ? [\n\tx : x\n\ty : y\n]\n(Point 1 2) ' y") == ("val", 2) and ev("Point : x y ? [\n\tx : x + 1\n\ty : y\n]\n(Point 3 2) ' x") == ("val", 4)
    assert ev("p :\n\ta : b\n\tb : a\np") == ("rec", "[a: !_, b: !_]")
def test_fuzz_structs():
    r = subprocess.run([sys.executable, "fuzz_sir.py", "800", "71", "--structs", "--asm"], capture_output=True, text=True, timeout=900)
    assert r.returncode == 0, r.stdout[-1200:]
def test_floats_promote_and_refuse_undecided():
    # S4: Float の字面・昇格・比べ(strict と同じ)。`%`・0 割り・溢れ・添字・長さは断る(仕様が未決)。機械語へは戻さない
    import sign_sir as R, sign_interp as S
    def ev(src):
        f, top = R.lower(S.parse_source(src + "\n")); return R.evaluate(f, top)
    assert ev("1.5 + 2") == ("flt", "3.5") and ev("3 / 2.0") == ("flt", "1.5") and ev("3 / 2") == ("val", 1)
    assert ev("1.5 < 2") == ("flt", "1.5") and ev("1 < 1.5") == ("val", 1) and ev("2.5 < 1.5") == ("void",)
    assert ev("0.1 * 3") == ("flt", "0.30000000000000004") and ev("-0.0") == ("flt", "-0.0")
    assert ev("0.0 & 7") == ("val", 7) and ev("(1.5 < 1) | 2.5") == ("flt", "2.5")
    for bad in ("-7 % 2.5", "1 / 0.0", "10.0 / 0", "1" + "0" * 200 + ".0 * 1" + "0" * 200 + ".0"):
        try: ev(bad); assert False, bad
        except R.Unsup: pass
    assert ev("[3 4 5] ' 1.5") == ("val", 5) and ev("[3 4 5] ' 0.5") == ("val", 4) and ev("[3 4 5] ' -0.5") == ("val", 5) and ev("[3 4 5] ' 2.5") == ("void",)
    assert ev("`abc` ' 1.5") == ("chr", 99)
    assert ev("||1.5||") == ("val", 1) and ev("||0||") == ("val", 1) and ev("||__||") == ("val", 0)
    f, top = R.lower(S.parse_source("1.5\n"))
    try: R.raise_ast(f, top); assert False
    except R.Unsup: pass
def test_fuzz_floats():
    r = subprocess.run([sys.executable, "fuzz_sir.py", "800", "81", "--floats", "--asm"], capture_output=True, text=True, timeout=900)
    assert r.returncode == 0, r.stdout[-1200:]
def test_list_arithmetic():
    # 器の算術(type_system.md 910–914): `List * n` は n 回コピー、`List + - %`・`n * List` は `!_`。`/`・`^`・n ≤ 0・器どうしは断る
    import sign_sir as R, sign_interp as S
    def ev(src):
        f, top = R.lower(S.parse_source(src + "\n")); return R.evaluate(f, top)
    assert ev("[1 2] * 2") == ("flow", (1, 2, 1, 2)) and ev("||[1 2] * 3||") == ("val", 6) and ev("([1 2] * 2) ' 3") == ("val", 2)
    assert ev("[1 2] + 1") == ("void",) and ev("2 * [1 2]") == ("void",) and ev("[1 2] % 2") == ("void",) and ev("5 + ([1 2] + 1)") == ("val", 5)
    for bad in ("[1 2] / 2", "[1 2] * -1", "[1 2] * [3 4]", "[1 2] ^ 2"):
        try: ev(bad); assert False, bad
        except R.Unsup: pass
def test_flow_composition_left_to_right():
    # 余った関数が続く流れは合成で、左の関数から実行する(V3、strict の Pipe)。strict の値と同じ
    import sign_sir as R, sign_interp as S
    H = "g : x ? x + 1\nsb : a b ? a - b\n"
    def ev(body):
        f, top = R.lower(S.parse_source(H + body + "\n")); return R.evaluate(f, top)
    assert ev("(sb 10 (3 > 5)) (g __) 5") == ("val", 6)
    assert ev("(sb __ 3) (g __) 5 7") == ("flow", (-1, 7))
    assert ev("1 (sb 10 (3 > 5)) (g __) 5 9") == ("flow", (1, 6, 9))
    assert ev("(g __) (sb 10 (3 > 5)) 5") == ("val", 4)
def test_plan_flow_tree_uniform_kinds():
    # 単位になりうる実引数を含む流れは、単位かどうかの場合分けの木にする。葉の種類(値 1 つ・並び)が揃うときだけ。混ざれば今の道(罠)に戻す
    import sign_sir as R, sign_interp as S
    H = "g : x ? x + 1\nk : x y ? x + y\nsb : a b ? a - b\n"
    f, top = R.lower(S.parse_source(H + "f : x ? 1 (k 4 (x > 5)) 5\nf 3\n"))
    nodes = R.raise_ast(f, top)                                                  # 例外なく戻せる(種類が揃う: 葉はどれも並び)
    assert nodes
    f, top = R.lower(S.parse_source(H + "f : x ? (sb 10 (x > 5)) (g __) 5\nf 3\n"))
    assert R.plan_flow(f, [("call", "sb", [("int", 10), ("cmp", ">", ("var", "x"), ("int", 5))]), ("call", "g", []), ("int", 5)]) is None       # 値 1 つの葉と並びの葉が混ざる
def test_fuzz_flows_defaults_more_seeds():
    for a, seed in (("--flows", "3"), ("--flows", "7"), ("--defaults", "3")):
        r = subprocess.run([sys.executable, "fuzz_sir.py", "400", seed, a, "--asm"], capture_output=True, text=True, timeout=900)
        assert r.returncode == 0, a + r.stdout[-1200:]

if __name__ == "__main__":                      # CI は `python3 test_*.py` で走らせる(pytest ではない)。ここが無いと何も走らず成功になる
    import traceback
    ng = 0
    for name, fn in sorted(globals().items()):
        if name.startswith("test_") and callable(fn):
            try: fn(); print("ok ", name)
            except BaseException: ng += 1; print("NG ", name); traceback.print_exc()
    print("全部 ok" if not ng else "%d 件 NG" % ng)
    sys.exit(1 if ng else 0)
