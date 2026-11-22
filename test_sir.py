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
