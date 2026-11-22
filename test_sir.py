import subprocess, sys
import sign_sir as S
def test_range():
    assert S.I64_MIN == -(2**63 - 1)
def test_front_back_observation():
    r = subprocess.run([sys.executable, "diff_observe.py"], capture_output=True, text=True, timeout=600)
    assert r.returncode == 0, r.stdout[-800:]
