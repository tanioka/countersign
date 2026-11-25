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
    rc, err, text = _compile("f : x y ?\n\tx > y : x / y\n\tx + 1\nf 3 4\n", "--via-sir")
    assert rc == 0 and "SIR 経由で出します" in err and text
    rc, err, text = _compile("s : `hi`\ns\n", "--via-sir")                  # 文字列は SIR の外: 旧経路で出る
    assert rc == 0 and "旧経路で出します" in err and text
    rc, err, text2 = _compile("f : x y ?\n\tx > y : x / y\n\tx + 1\nf 3 4\n")     # 旗なしは今までどおり
    assert rc == 0 and "via-sir" not in err
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
    for bad in ["s : `abc`\ns * 2\n", "s : `abc`\n(s ' 1) + 1\n", "f : x ? ||x||\nf `ab`\n", "\\a < \\b\n", "s : `h\u00e9`\n||s||\n"]:
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
