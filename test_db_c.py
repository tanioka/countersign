"""test_db_c.py — sign_db.c(--real-dev の SQLite 本体。libsqlite3 を直に使う)を x86 の箱で作り、処理系の sign_db.py と同じ操作列を流して戻りとバッファを突き合わせる。
C 側のメモリは Sign の番地(0x10000〜)に mmap で本物の領域を置き、1 語 = 1 バイトで文字列を並べる。実機(AArch64)では未実行。"""
import ctypes, mmap, os, subprocess, sys, tempfile
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import sign_db

fails = 0
def check(name, want, got):
    global fails
    if want == got: print("ok ", name)
    else: fails += 1; print("NG ", name, "\n    want", repr(want)[:600], "\n    got ", repr(got)[:600])

so = os.path.join(tempfile.mkdtemp(), "libsigndb.so")
r = subprocess.run(["gcc", "-O2", "-Wall", "-Werror", "-shared", "-fPIC", "-o", so, os.path.join(HERE, "sign_db.c"), "-lsqlite3"], capture_output=True, text=True)
check("sign_db.c が警告なしで組み立てられる(gcc -Wall -Werror)", (r.returncode, r.stderr), (0, ""))
import shutil
_n = [0]
def fresh_lib():                      # 実行ごとに別のコピーを読み込む(C 側の状態 = ハンドルの番号などを初期化するため)
    _n[0] += 1; p = so + ".%d" % _n[0]; shutil.copy(so, p)
    l = ctypes.CDLL(p); l.sign_db_call.restype = ctypes.c_long; l.sign_db_call.argtypes = [ctypes.POINTER(ctypes.c_ulong)]; return l
lib = fresh_lib()
BASE, SIZE = 0x10000, 0x300000
region = mmap.mmap(-1, SIZE, flags=mmap.MAP_PRIVATE | mmap.MAP_ANONYMOUS | 0x10, prot=mmap.PROT_READ | mmap.PROT_WRITE, offset=0) if False else None
libc = ctypes.CDLL(None, use_errno=True); libc.mmap.restype = ctypes.c_void_p; libc.mmap.argtypes = [ctypes.c_void_p, ctypes.c_size_t, ctypes.c_int, ctypes.c_int, ctypes.c_int, ctypes.c_long]
got = libc.mmap(BASE, SIZE, 3, 0x2 | 0x20 | 0x100000, -1, 0)      # MAP_PRIVATE|MAP_ANONYMOUS|MAP_FIXED_NOREPLACE
assert got == BASE, "mmap %x" % (got or 0)
words = (ctypes.c_uint32 * (SIZE // 4)).from_address(BASE)
STR, BLB, DST = BASE + 0x1000, BASE + 0x60000, BASE + 0x80000

class PyMem(dict): pass
class Side:
    def __init__(self, kind):
        self.kind = kind; self.dir = tempfile.mkdtemp()
        if kind == "py": self.dev = sign_db.Db(root=self.dir); self.dev.mem = PyMem()
        else: self.cwd = os.getcwd()
    def put(self, addr, data):
        for i, b in enumerate(data): self.setw(addr + 4 * i, b)
        self.setw(addr + 4 * len(data), 0)
    def setw(self, a, v):
        if self.kind == "py": self.dev.mem[a] = v
        else: words[(a - BASE) // 4] = v
    def getw(self, a):
        return self.dev.mem.get(a, 0) if self.kind == "py" else words[(a - BASE) // 4]
    def call(self, nr, args):
        if self.kind == "py":
            self.dev.reg = {0: nr, **{4 * (i + 1): v for i, v in enumerate(args)}}
            return self.dev.call()
        os.chdir(self.dir)
        try:
            arr = (ctypes.c_ulong * 7)(nr, *[a & 0xFFFFFFFFFFFFFFFF for a in args], *([0] * (6 - len(args))))
            return lib.sign_db_call(arr)
        finally: os.chdir(self.cwd)

def prep(side, a):
    """a の要素: int / ('s', str|bytes) / ('b', bytes) / ('d', 最大) → 引数の整数。文字列は STR から 0x1000 刻み。"""
    out, k = [], 0
    for x in a:
        if isinstance(x, tuple):
            if x[0] == "s": side.put(STR + 0x1000 * k, x[1].encode() if isinstance(x[1], str) else x[1]); out.append(STR + 0x1000 * k)
            elif x[0] == "b": side.put(BLB, x[1]); out.append(BLB)
            elif x[0] == "d": out.append(DST)
            k += 1
        else: out.append(x)
    return out

def dst_text(side, n=80):
    out = bytearray()
    for i in range(n):
        w = side.getw(DST + 4 * i)
        if w == 0: break
        out.append(w & 0xFF)
    return bytes(out)

def run(ops):
    global lib
    lib = fresh_lib(); sides = [Side("py"), Side("c")]; results = []
    for nr, a in ops:
        row = []
        for sd in sides:
            for i in range(20): sd.setw(DST + 4 * i, 0xAA)                      # 書き込み先を印で埋めておく
            r = sd.call(nr, prep(sd, a)); row.append((r, dst_text(sd, 20) if any(isinstance(x, tuple) and x[0] == "d" for x in a) else None))
        results.append(row)
    return results

def ok_all(name, ops):
    res = run(ops); bad = [(i, ops[i], r) for i, r in enumerate(res) if r[0] != r[1]]
    check(name, [], bad)
    return res

OPEN, CLOSE, EXEC, PREP, BI, BT, BN, BB, STEP, CC, CT, CI, CTX, CN, RST, FIN, ROW, CHG, ERR = range(1, 20)
S = lambda s: ("s", s)
# --- 基本: メモリ DB・表・束縛・読み ---
ops = [
 (OPEN, [S(":memory:"), 0]),                                                       # 1
 (EXEC, [1, S("create table t(id integer primary key, n integer, s text, b blob, f real)")]),
 (EXEC, [1, S("create table u(id integer primary key, t_id integer references t(id))")]),
 (EXEC, [1, S("insert into t(n,s) values (1,'a'),(2,'b')")]),                    # 変えた行 2
 (CHG, [1]), (ROW, [1]),
 (EXEC, [1, S("select 1; select 2")]),                                             # 複数の文 → -22
 (EXEC, [1, S("   ")]), (EXEC, [1, S("-- only comment")]),
 (EXEC, [1, S("vacuum into 'x.db'")]), (EXEC, [1, S("VACUUM main INTO 'x.db'")]),
 (EXEC, [1, S("attach database 'y.db' as y")]),
 (EXEC, [1, S("insert into t(id) values (1)")]), (ERR, [1, ("d", 0), 80, 0]),    # 制約違反 -17 と文面
 (EXEC, [1, S("insert into u(t_id) values (99)")]), (ERR, [1, ("d", 0), 80, 0]),  # 外部キー -17
 (EXEC, [1, S("bad sql")]), (ERR, [1, ("d", 0), 80, 0]),
 (EXEC, [1, S("select * from nosuch")]), (EXEC, [1, S("create table t(x)")]),     # 既にある → -5
 (EXEC, [1, S("select ?")]),                                                       # ? に値なし -22
 (PREP, [1, S("insert into t(n,s,b,f) values (?,?,?,?)")]),                        # 2
 (CC, [2]), (BI, [2, 1, 5]), (BT, [2, 2, S("こんにちは")]), (BB, [2, 3, ("b", bytes([0, 1, 255, 7])), 4]), (BN, [2, 4]),
 (BI, [2, 0, 1]), (BI, [2, 5, 1]), (BT, [2, 1, S(b"\xff\xfe")]),
 (STEP, [2]), (CHG, [1]), (ROW, [1]), (CC, [2]),
 (BI, [2, 1, 4294967295]), (BT, [2, 2, S("")]), (BB, [2, 3, ("b", b""), 0]), (BN, [2, 4]), (STEP, [2]), (ROW, [1]),
 (FIN, [2]), (FIN, [2]), (STEP, [2]),
 (PREP, [1, S("select id, n, s, b, f from t order by id")]),                       # 3
 (CC, [3]), (STEP, [3]), (CC, [3]),
]
for c in range(5): ops += [(CT, [3, c]), (CI, [3, c]), (CTX, [3, c, ("d", 0), 80]), (CN, [3, c, ("d", 0), 80])]
ops += [(CTX, [3, 2, ("d", 0), 3]), (CTX, [3, 2, ("d", 0), 1]), (CTX, [3, 2, ("d", 0), 0]), (CT, [3, 9]), (CN, [3, -1, ("d", 0), 5])]
ops += [(STEP, [3]), (STEP, [3]), (STEP, [3]), (STEP, [3]), (STEP, [3]), (CT, [3, 0]), (CC, [3]), (RST, [3]), (STEP, [3]), (CI, [3, 1])]
ops += [(CTX, [3, 2, ("d", 0), 80]), (CTX, [3, 2, ("d", 0), 9]), (CTX, [3, 3, ("d", 0), 80])]
ops += [(CLOSE, [1]), (CLOSE, [1]), (STEP, [3]), (EXEC, [1, S("select 1")]), (OPEN, [S(":memory:"), 2]), (OPEN, [S(""), 0]), (OPEN, [("s", b"\xff"), 0]), (99 and 20, [1]), (0, [1])]
res = ok_all("db_c: 基本(表・束縛・読み・エラー・文面・閉じたあと)が sign_db.py と一致", ops)
check("db_c: 戻りの要所(open=1, 複数文=-22, vacuum into=-95, attach=-95, 制約=-17)", [res[0][1][0], res[6][1][0], res[9][1][0], res[10][1][0], res[11][1][0], res[12][1][0]], [1, -22, -95, -95, -95, -17])
# --- 数値・小数(全角など Unicode の数字・空白も Python と同じに読む)---
fl = ["0.1", "1e16", "1.5e-5", "100.0", "-2.5", "1e22", "123456789012345.0", "0.0001", "1e15", "3.141592653589793", "-0.0", "1.7976931348623157e308", "5e-324", "9223372036854775807", "-9223372036854775808", "'  -7x'", "'12abc'", "'abc'", "'+5'", "'99999999999999999999'", "'１２'", "'  -９x'", "'\u3000+٣٤５'", "'\u00a0７'", "'-１２３４５６７８９０１２３４５６７８９０１２'", "'１ ２'", "'+ 5'", "'\u200b5'", "'𝟓𝟔'", "null", "x'4142'", "1.0e100", "2.5e-10", "12345678901234567890.0", "1e21"]
ops = [(OPEN, [S(":memory:"), 0]), (PREP, [1, S("select " + ", ".join(fl)).__class__ and S("select " + ", ".join(fl))]), (STEP, [2])]
for c in range(len(fl)): ops += [(CT, [2, c]), (CI, [2, c]), (CTX, [2, c, ("d", 0), 80])]
ok_all("db_c: 数の変換(小数の repr・文字列の先頭の整数・飽和)が一致", ops)
# --- ファイル DB・パス・読むだけ ---
ops = [(OPEN, [S("t.db"), 0]), (EXEC, [1, S("create table k(v)")]), (EXEC, [1, S("insert into k values (1)")]), (CLOSE, [1]),
       (OPEN, [S("t.db"), 1]), (EXEC, [3, S("insert into k values (2)")]), (PREP, [3, S("select v from k")]), (ERR, [3, ("d", 0), 80, 0]),
       (OPEN, [S("nofile.db"), 1]), (OPEN, [S("../x.db"), 0]), (OPEN, [S("a/../x.db"), 0]), (OPEN, [S("/tmp/x.db"), 0]), (OPEN, [S("file:x.db"), 0]), (OPEN, [S("C:x.db"), 0]), (OPEN, [S("no/dir/x.db"), 0]),
       (OPEN, [S("sub\\..\\x.db"), 0]), (OPEN, [S(":memory:"), 1]), (OPEN, [S("t.db"), 0]), (EXEC, [6, S("select * from k")])]
res = ok_all("db_c: ファイル・読むだけ・パスの守りが一致", ops)
# --- 日本語・長い文字列・多すぎる ---
ops = [(OPEN, [S(":memory:"), 0]), (EXEC, [1, S("create table m(s)")]), (PREP, [1, S("insert into m values (?)")]), (BT, [2, 1, S("日本語テキスト" * 20)]), (STEP, [2]),
       (PREP, [1, S("select s, length(s), upper('ab') from m")]), (STEP, [3]), (CTX, [3, 0, ("d", 0), 20]), (CI, [3, 1]), (CTX, [3, 2, ("d", 0), 80])]
ops += [(PREP, [1, S("select %d" % i)]) for i in range(70)]
ops += [(OPEN, [S(":memory:"), 0]) for _ in range(66)]
ok_all("db_c: 日本語・文の数の上限(-12)・データベースの数の上限が一致", ops)
region.close() if region else None
print("\n全部 ok" if not fails else "\n失敗 %d 件" % fails)
sys.exit(1 if fails else 0)
