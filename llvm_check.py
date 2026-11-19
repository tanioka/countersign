# 生成した AArch64 アセンブリを、独立な実装(LLVM の llvm-mc)で組めるか確かめる。エミュレータは文字列の命令を直接解釈するので、
# 実機で組めない形(即値の範囲外、存在しない書き方)を受け入れてしまう危険を、これで見つける。llvm-mc が無ければ None を返す(確認なし)。
import shutil, subprocess, tempfile, os
def available(): return shutil.which("llvm-mc") is not None
def check(asm_text):
    """組めれば "" 、組めなければ llvm-mc のエラー(先頭数行)。llvm-mc が無ければ None。"""
    if not available(): return None
    with tempfile.TemporaryDirectory() as d:
        s = os.path.join(d, "x.s"); open(s, "w").write(asm_text)
        r = subprocess.run(["llvm-mc", "-triple=aarch64", "-filetype=obj", s, "-o", os.path.join(d, "x.o")], capture_output=True, text=True)
        return "" if r.returncode == 0 else "\n".join(r.stderr.splitlines()[:6])
