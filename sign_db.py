"""sign_db.py — SQLite 装置(仕様に無い追加)。Python 標準の sqlite3 を、Sign のメモリ番地の口から使えるようにする。

基点 0x9A00000(sign_interp.py の --db[=フォルダ]、sign_console.py にも同じ)。Net 装置と同じ呼び方:
    base + 0x00 NR  命令番号   0x04〜0x18 ARG0〜ARG5   0x20 GO(書くと実行)   0x24 RET(戻り。負は -errno)
命令(h = データベースの番号、s = 文の番号。どちらも 1 から。文字列は 1 語 1 バイト・0 終わり、UTF-8):
     1 OPEN(path, flags)      データベースを開く → h。path は「:memory:」か、フォルダの下の相対名。flags 0 = 読み書き(無ければ作る)、1 = 読むだけ(無ければ -2)
     2 CLOSE(h)               閉じる(その h の文も全部終わる)。0
     3 EXEC(h, sql)           文を 1 つ実行する(結果の行は捨てる)。変更した行数
     4 PREPARE(h, sql)        文を準備する → s(文法の誤りはここで -errno)
     5 BIND_INT(s, i, v)      i 番目(1 から)の ? に整数(64 ビットの範囲。外は -75)
     6 BIND_TEXT(s, i, p)     文字列(p から 0 まで)
     7 BIND_NULL(s, i)
     8 BIND_BLOB(s, i, p, n)  n バイト
     9 STEP(s)                1 = 行が 1 つ読めた、0 = もう無い(INSERT などは実行して 0)。負 = エラー
    10 COL_COUNT(s)           列の数(STEP のあと)
    11 COL_TYPE(s, i)         列 i(0 から)の型: 1 整数 2 小数 3 文字列 4 バイト列 5 NULL
    12 COL_INT(s, i)          整数として(小数は 0 の方へ切る。文字列は先頭の整数。NULL・バイト列は 0)
    13 COL_TEXT(s, i, dst, max)   文字列として dst へ(最大 max-1 バイト + 0)。値の本当の長さを返す(max より長ければ切れている)
    14 COL_NAME(s, i, dst, max)   列の名前を同じ形で
    15 RESET(s)               最初からやり直せる(束縛はそのまま)
    16 FINALIZE(s)            文を捨てる
    17 LAST_ROWID(h)          最後に INSERT した行の番号
    18 CHANGES(h)             最後の文が変えた行数
    19 ERRMSG(h, dst, max)    最後のエラーの文面を dst へ。長さを返す
エラー番号: -2 ファイルが無い・-5 そのほか・-12 多すぎる・-16 使用中・-17 制約違反・-22 引数か文がおかしい・-30 読むだけ・-75 範囲外・-95 許していない。
守り: ファイルは --db のフォルダの下だけ(絶対パス・「..」・URI は -95)。ATTACH と VACUUM INTO は許さない。load_extension は無い。
限界: 小数は COL_INT で切るか COL_TEXT で文字列にするしかない(Sign に小数が無い)。結果を 1 行ずつしか読めない。STEP を続ける間は同じデータベースへ別の文を割り込ませないこと(挙動は SQLite まかせ)。
"""
import os, re, sqlite3, sys
from sign_mem import DevMem

DB_BASE = 0x9A00000
NR, A0, A1, A2, A3, A4, A5, GO, RET = 0x00, 0x04, 0x08, 0x0C, 0x10, 0x14, 0x18, 0x20, 0x24
MAXSTR, MAXBLOB, MAXOBJ = 1 << 20, 1 << 20, 64
I64 = 1 << 63
EPERM_ = 95


def _code(e):
    if isinstance(e, sqlite3.IntegrityError): return -17
    m = str(e).lower()
    if "locked" in m or "busy" in m: return -16
    if "readonly" in m or "read-only" in m: return -30
    if "unable to open" in m: return -2
    if "not authorized" in m: return -EPERM_
    if isinstance(e, (sqlite3.ProgrammingError, sqlite3.InterfaceError)) or "syntax" in m or "no such" in m or "incomplete" in m or "more than one" in m or "only execute one" in m: return -22
    return -5


class _Stmt:
    def __init__(self, h, sql):
        self.h, self.sql, self.params, self.cur, self.row, self.done, self.np = h, sql, {}, None, None, False, 0


class Db(DevMem):
    def __init__(self, root=None, base=DB_BASE):
        self.base, self.size = base, 0x28
        self.root = os.path.realpath(root or os.getcwd())
        self.reg, self.ret, self.dbs, self.stmts, self.next_h, self.errmsg, self.changes = {}, 0, {}, {}, 1, {}, {}

    # --- 装置の口 ---
    def read(self, off): return self.ret if off == RET else self.reg.get(off)
    def write(self, off, v):
        if not isinstance(v, int) or isinstance(v, bool): return
        if off in (NR, A0, A1, A2, A3, A4, A5): self.reg[off] = v
        elif off == GO:
            try: self.ret = self.call()
            except Exception as e: self.ret = -5

    def finish(self): self.release()
    def release(self):
        for d in self.dbs.values():
            try: d.close()
            except Exception: pass
        self.dbs.clear(); self.stmts.clear()

    # --- メモリ ---
    def cstr(self, p, limit=MAXSTR):
        mem = self.memory()
        if mem is None or not isinstance(p, int): return None
        out = bytearray()
        while True:
            v = mem.get(p + 4 * len(out))
            if not isinstance(v, int) or isinstance(v, bool) or not 0 <= v <= 255: return None
            if v == 0: break
            out.append(v)
            if len(out) > limit: return None
        try: return out.decode("utf-8")
        except UnicodeDecodeError: return None

    def blob(self, p, n):
        mem = self.memory()
        if mem is None or not isinstance(p, int) or not isinstance(n, int) or not 0 <= n <= MAXBLOB: return None
        out = bytearray()
        for i in range(n):
            v = mem.get(p + 4 * i)
            if not isinstance(v, int) or isinstance(v, bool) or not 0 <= v <= 255: return None
            out.append(v)
        return bytes(out)

    def put(self, dst, mx, data):
        """data を dst へ(最大 mx-1 バイト + 0)。本当の長さを返す"""
        mem = self.memory()
        if mem is None or not isinstance(dst, int) or not isinstance(mx, int) or mx < 1: return -22
        for i, b in enumerate(data[:mx - 1]): mem[dst + 4 * i] = b
        mem[dst + 4 * min(len(data), mx - 1)] = 0
        return len(data)

    # --- 部品 ---
    def path(self, s, flags):
        if s == ":memory:": return ":memory:", False
        if not s or s.startswith(("/", "\\", "file:")) or "\x00" in s or ".." in s.replace("\\", "/").split("/") or (len(s) > 1 and s[1] == ":"): return None, False
        full = os.path.realpath(os.path.join(self.root, s))
        if full != self.root and not full.startswith(self.root + os.sep): return None, False
        return full, flags == 1

    def new_h(self):
        h = self.next_h; self.next_h += 1; return h

    def fail(self, h, e):
        self.errmsg[h] = str(e); return _code(e)

    @staticmethod
    def authorizer(action, a1, a2, db, src):
        if action == sqlite3.SQLITE_ATTACH: return sqlite3.SQLITE_DENY
        return sqlite3.SQLITE_OK

    @staticmethod
    def bad_sql(sql): return re.search(r"\bvacuum\b[^;]*\binto\b", sql, re.I) is not None

    def sql_of(self, p):
        s = self.cstr(p)
        return s if s is not None and s.strip() else None

    def stmt(self, s):
        st = self.stmts.get(s) if isinstance(s, int) else None
        return st

    def call(self):
        g = self.reg.get
        n, a, b, c, d = g(NR), g(A0), g(A1), g(A2), g(A3)
        if not isinstance(n, int) or not 1 <= n <= 19: return -22
        if n == 1: return self.c_open(a, b)
        if n == 2: return self.c_close(a)
        if n in (3, 4):
            db = self.dbs.get(a)
            if db is None: return -9
            sql = self.sql_of(b)
            if sql is None: return -22
            if self.bad_sql(sql): return -EPERM_
            if n == 3:
                try:
                    cur = db.execute(sql); r = max(cur.rowcount, 0); self.changes[a] = r; cur.close(); return r
                except sqlite3.Error as e: return self.fail(a, e)
            if len(self.stmts) >= MAXOBJ: return -12
            try: np = self.check_sql(db, sql)                # 文法を確かめる(実行はしない)。? の数が分かる
            except sqlite3.Error as e: return self.fail(a, e)
            h = self.new_h(); self.stmts[h] = _Stmt(a, sql); self.stmts[h].np = np; return h
        if n == 17 or n == 18 or n == 19:
            db = self.dbs.get(a)
            if db is None: return -9
            if n == 17: return db.execute("SELECT last_insert_rowid()").fetchone()[0]
            if n == 18: return self.changes.get(a, 0)
            return self.put(b, c, self.errmsg.get(a, "").encode("utf-8"))
        st = self.stmt(a)
        if st is None: return -9
        if n in (5, 6, 7, 8):
            if not isinstance(b, int) or not 1 <= b <= st.np: return -22
            if n == 5:
                if not isinstance(c, int) or not -I64 <= c < I64: return -75
                st.params[b] = c
            elif n == 6:
                s = self.cstr(c)
                if s is None: return -22
                st.params[b] = s
            elif n == 7: st.params[b] = None
            else:
                x = self.blob(c, d)
                if x is None: return -22
                st.params[b] = x
            st.cur = None; st.row = None; st.done = False
            return 0
        if n == 9: return self.c_step(st)
        if n == 15: st.cur = None; st.row = None; st.done = False; return 0
        if n == 16: del self.stmts[a]; return 0
        if n in (10, 11, 12, 13, 14):
            if st.cur is None or st.cur.description is None: return -22
            if n == 10: return len(st.cur.description)
            if not isinstance(b, int) or not 0 <= b < len(st.cur.description): return -22
            if n == 14: return self.put(c, d, st.cur.description[b][0].encode("utf-8"))
            if st.row is None: return -22
            v = st.row[b]
            if n == 11: return 5 if v is None else 1 if isinstance(v, int) else 2 if isinstance(v, float) else 3 if isinstance(v, str) else 4
            if n == 12: return self.as_int(v)
            return self.put(c, d, v if isinstance(v, bytes) else b"" if v is None else (repr(v) if isinstance(v, float) else str(v)).encode("utf-8"))
        return -22

    @staticmethod
    def check_sql(db, sql):
        try: db.execute("EXPLAIN " + sql).close(); return 0
        except sqlite3.ProgrammingError as e:             # ? の数が合わない: 数を読み取って空の値で数だけ満たす
            m = re.search(r"uses (\d+)", str(e))
            if not m: raise
            db.execute("EXPLAIN " + sql, [None] * int(m.group(1))).close(); return int(m.group(1))

    @staticmethod
    def as_int(v):
        if isinstance(v, int): return v
        if isinstance(v, float): return 0 if v != v else max(-I64, min(I64 - 1, int(v)))
        if isinstance(v, str):
            m = re.match(r"\s*([+-]?\d+)", v)
            return max(-I64, min(I64 - 1, int(m.group(1)))) if m else 0
        return 0

    def c_open(self, p, flags):
        s = self.cstr(p, 4096)
        if not s or flags not in (0, 1): return -22
        full, ro = self.path(s, flags)
        if full is None: return -EPERM_
        if len(self.dbs) >= MAXOBJ: return -12
        try:
            if full == ":memory:": db = sqlite3.connect(":memory:", isolation_level=None, check_same_thread=False)
            else:
                if ro and not os.path.exists(full): return -2
                from urllib.parse import quote
                db = sqlite3.connect("file:" + quote(full) + ("?mode=ro" if ro else ""), uri=True, isolation_level=None, check_same_thread=False)
            db.set_authorizer(self.authorizer)
            db.execute("PRAGMA foreign_keys=ON").close()
        except (sqlite3.Error, OSError) as e:
            return _code(e)
        h = self.new_h(); self.dbs[h] = db; return h

    def c_close(self, h):
        db = self.dbs.pop(h, None) if isinstance(h, int) else None
        if db is None: return -9
        for k in [k for k, st in self.stmts.items() if st.h == h]: del self.stmts[k]
        try: db.close()
        except sqlite3.Error: pass
        return 0

    def c_step(self, st):
        db = self.dbs.get(st.h)
        if db is None: return -9
        try:
            if st.cur is None:
                st.cur = db.execute(st.sql, [st.params.get(i) for i in range(1, st.np + 1)])
                st.done = False
                if st.cur.description is None:                       # INSERT など: 実行して 0
                    self.changes[st.h] = max(st.cur.rowcount, 0); st.done = True; st.row = None; return 0
            if st.done: st.row = None; return 0
            st.row = st.cur.fetchone()
            if st.row is None: st.done = True; return 0
            return 1
        except sqlite3.Error as e:
            st.cur = None; st.row = None; return self.fail(st.h, e)
