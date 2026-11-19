"""装置どうしで共通の、インタープリタのメモリの読み書き(sign_bus・sign_sys・sign_audio・sign_db・sign_net・sign_gfx が使う)。"""
import sys


class DevMem:
    def memory(self):
        """インタープリタのメモリ。この装置を持つインタープリタのモジュールから探す。"""
        for name in ("__main__", "sign_interp"):
            m = sys.modules.get(name)
            if m is not None and hasattr(m, "MEMORY") and self in getattr(m, "DEVICES", ()): return m.MEMORY
        return getattr(self, "mem", None)             # 試験が直に渡す用

    def put_bytes(self, buf, data):
        mem = self.memory()
        if mem is None or not isinstance(buf, int): return False
        for i, b in enumerate(data): mem[buf + 4 * i] = b
        return True
