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
