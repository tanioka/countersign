/* sign_db.c — `--real-dev` の SQLite 装置(0x9A00000)の本体。sign_db.py(処理系の仮想装置)と同じ振る舞いを、本物の libsqlite3 で行う。
 *
 * アセンブリの中継ルーチンが、GO の書き込みで  long sign_db_call(const unsigned long *r)  を呼ぶ。
 *   r[0] = NR, r[1..6] = ARG0..ARG5(影のレジスタ。1 つ 8 バイトで、4 バイトの書き込みは 0 拡張)
 *   戻り = RET(0 以上は成功の値、負は -エラー番号)
 * 文字列・バッファは Sign のメモリ番地から 1 語(4 バイト)= 1 バイト(0〜255)。命令の番号と戻りは sign_db.py の先頭の表と同じ。
 *
 * Raspberry Pi 上で:   sudo apt install gcc libsqlite3-dev
 *   gcc -O2 -nostartfiles -no-pie -Wl,-Ttext-segment=0x10000000 -o prog prog.s sign_db.c -lsqlite3
 * (`sign.py --pi-bundle=DIR` がこの一式と build.sh を作る。)ファイルの置き場は、プログラムを起動した時のカレントディレクトリ。
 *
 * これは実装の決めで、仕様に定めはない。実機では未実行(処理系の sign_db.py と突き合わせる試験は x86 の箱で行った)。
 */
#define _GNU_SOURCE
#include <sqlite3.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include <limits.h>
#include <math.h>
#include <unistd.h>
#include <sys/stat.h>
#include <ctype.h>
#include <strings.h>

#define MAXOBJ 64
#define MAXSTR (1 << 20)
#define MAXBLOB (1 << 20)
#define EPERM_ 95

typedef struct { long id; sqlite3 *db; long changes; char *err; } Db;
typedef struct { long id, dbid; sqlite3_stmt *p; int np, started, done, hasrow; char *sql; } St;
static Db dbs[MAXOBJ]; static int ndb;
static St sts[MAXOBJ]; static int nst;
static long next_h = 1;
static char root[PATH_MAX]; static int root_ok;

/* ---- Sign のメモリ ---- */
static int okaddr(uint64_t a) { return (a >= 0x10000 && a < 0x9000000) || (a >= 0x10000000 && a < (1ULL << 47)); }
static int word(uint64_t a, int *v) { if (!okaddr(a)) return 0; uint32_t w = *(volatile uint32_t *)a; if (w > 255) return 0; *v = (int)w; return 1; }
static int valid_utf8(const unsigned char *s, size_t n) {
    size_t i = 0;
    while (i < n) {
        unsigned c = s[i];
        if (c < 0x80) { i++; continue; }
        int k = c >= 0xF0 ? 3 : c >= 0xE0 ? 2 : c >= 0xC2 ? 1 : -1;
        if (k < 0 || c > 0xF4 || i + k >= n) return 0;
        for (int j = 1; j <= k; j++) if ((s[i + j] & 0xC0) != 0x80) return 0;
        if (k == 2 && ((c == 0xE0 && s[i + 1] < 0xA0) || (c == 0xED && s[i + 1] >= 0xA0))) return 0;
        if (k == 3 && ((c == 0xF0 && s[i + 1] < 0x90) || (c == 0xF4 && s[i + 1] >= 0x90))) return 0;
        i += k + 1;
    }
    return 1;
}
/* p から 0 まで(UTF-8)→ malloc した文字列。長さ上限 limit を超える・語が 0〜255 でない・UTF-8 でない → NULL */
static char *cstr(uint64_t p, size_t limit, size_t *outn) {
    size_t cap = 64, n = 0; char *b = malloc(cap);
    if (!b) return NULL;
    for (;;) {
        int v; if (!word(p + 4 * n, &v)) { free(b); return NULL; }
        if (v == 0) break;
        if (n + 2 > cap) { cap *= 2; char *t = realloc(b, cap); if (!t) { free(b); return NULL; } b = t; }
        b[n++] = (char)v;
        if (n > limit) { free(b); return NULL; }
    }
    b[n] = 0;
    if (!valid_utf8((unsigned char *)b, n)) { free(b); return NULL; }
    if (outn) *outn = n;
    return b;
}
static unsigned char *blob(uint64_t p, uint64_t n) {
    if (n > MAXBLOB) return NULL;
    unsigned char *b = malloc(n ? n : 1); if (!b) return NULL;
    for (uint64_t i = 0; i < n; i++) { int v; if (!word(p + 4 * i, &v)) { free(b); return NULL; } b[i] = (unsigned char)v; }
    return b;
}
static long put(uint64_t dst, long mx, const char *data, size_t n) {
    if (mx < 1 || !okaddr(dst)) return -22;
    size_t m = n < (size_t)(mx - 1) ? n : (size_t)(mx - 1);
    for (size_t i = 0; i <= m; i++) if (!okaddr(dst + 4 * i)) return -22;
    for (size_t i = 0; i < m; i++) *(volatile uint32_t *)(dst + 4 * i) = (unsigned char)data[i];
    *(volatile uint32_t *)(dst + 4 * m) = 0;
    return (long)n;
}

/* ---- エラー番号(sign_db.py の _code と同じ) ---- */
static int has(const char *low, const char *w) { return strstr(low, w) != NULL; }
static long errcode(int rc, const char *msg) {
    int base = rc & 0xff;
    if (base == SQLITE_CONSTRAINT || base == SQLITE_MISMATCH) return -17;
    char low[512]; size_t i = 0;
    for (; msg && msg[i] && i < sizeof low - 1; i++) low[i] = (char)((msg[i] >= 'A' && msg[i] <= 'Z') ? msg[i] + 32 : msg[i]);
    low[i] = 0;
    if (has(low, "locked") || has(low, "busy")) return -16;
    if (has(low, "readonly") || has(low, "read-only")) return -30;
    if (has(low, "unable to open")) return -2;
    if (has(low, "not authorized")) return -EPERM_;
    if (base == SQLITE_MISUSE || has(low, "syntax") || has(low, "no such") || has(low, "incomplete") || has(low, "more than one") || has(low, "only execute one")) return -22;
    return -5;
}
static Db *getdb(long h) { for (int i = 0; i < ndb; i++) if (dbs[i].id == h) return &dbs[i]; return NULL; }
static St *getst(long s) { for (int i = 0; i < nst; i++) if (sts[i].id == s) return &sts[i]; return NULL; }
static void seterr(Db *d, const char *m) { free(d->err); d->err = strdup(m ? m : ""); }
static long fail(Db *d, int rc) { const char *m = sqlite3_errmsg(d->db); seterr(d, m); return errcode(rc, m); }

/* ---- 部品 ---- */
static int bad_sql(const char *s) {            /* \bvacuum\b[^;]*\binto\b(大文字小文字は問わない) */
    size_t n = strlen(s);
    for (size_t i = 0; i + 6 <= n; i++) {
        if (strncasecmp(s + i, "vacuum", 6) != 0) continue;
        if (i > 0 && (isalnum((unsigned char)s[i - 1]) || s[i - 1] == '_')) continue;
        if (i + 6 < n && (isalnum((unsigned char)s[i + 6]) || s[i + 6] == '_')) continue;
        for (size_t j = i + 6; j + 4 <= n && s[j] != ';'; j++)
            if (strncasecmp(s + j, "into", 4) == 0 && !(isalnum((unsigned char)s[j - 1]) || s[j - 1] == '_') && !(j + 4 < n && (isalnum((unsigned char)s[j + 4]) || s[j + 4] == '_'))) return 1;
    }
    return 0;
}
static int blank(const char *s) { for (; *s; s++) if (!isspace((unsigned char)*s)) return 0; return 1; }
static const char *skip_sql(const char *s) {   /* 空白とコメントを飛ばす */
    for (;;) {
        while (*s && isspace((unsigned char)*s)) s++;
        if (s[0] == '-' && s[1] == '-') { while (*s && *s != '\n') s++; continue; }
        if (s[0] == '/' && s[1] == '*') { const char *e = strstr(s + 2, "*/"); if (!e) return s + strlen(s); s = e + 2; continue; }
        return s;
    }
}
static int is_dml(const char *sql) {
    const char *s = skip_sql(sql);
    return !strncasecmp(s, "insert", 6) || !strncasecmp(s, "update", 6) || !strncasecmp(s, "delete", 6) || !strncasecmp(s, "replace", 7);
}
static int auth(void *u, int action, const char *a, const char *b, const char *c, const char *d) {
    (void)u; (void)a; (void)b; (void)c; (void)d; return action == SQLITE_ATTACH ? SQLITE_DENY : SQLITE_OK;
}
static int under_root(const char *full) { size_t n = strlen(root); return strcmp(full, root) == 0 || (strncmp(full, root, n) == 0 && full[n] == '/'); }

/* path: ":memory:" か、起動時のフォルダの下の相対名。NULL = 許さない(-95)、戻り値 2 = 場所が引けない(-2) */
static int dbpath(const char *s, char *full) {
    if (!strcmp(s, ":memory:")) { strcpy(full, ":memory:"); return 0; }
    if (!*s || s[0] == '/' || s[0] == '\\' || !strncmp(s, "file:", 5) || (strlen(s) > 1 && s[1] == ':')) return 1;
    char t[4200]; size_t n = strlen(s); if (n >= sizeof t) return 1;
    for (size_t i = 0; i <= n; i++) t[i] = s[i] == '\\' ? '/' : s[i];
    for (char *p = t; *p; ) { char *e = strchr(p, '/'); size_t l = e ? (size_t)(e - p) : strlen(p); if (l == 2 && p[0] == '.' && p[1] == '.') return 1; if (!e) break; p = e + 1; }
    if (!root_ok) { if (!getcwd(root, sizeof root)) return 2; char r[PATH_MAX]; if (realpath(root, r)) strcpy(root, r); root_ok = 1; }
    char j[PATH_MAX + 4200]; snprintf(j, sizeof j, "%s/%s", root, s);
    char r[PATH_MAX];
    if (realpath(j, r)) { if (!under_root(r)) return 1; strcpy(full, r); return 0; }
    char *sl = strrchr(j, '/'); if (!sl) return 2;
    *sl = 0; if (!realpath(j, r)) return 2;
    if (strlen(r) + strlen(sl + 1) + 2 > PATH_MAX) return 2;
    strcat(r, "/"); strcat(r, sl + 1);
    if (!under_root(r)) return 1;
    strcpy(full, r); return 0;
}

/* ---- 数の整形 ---- */
/* Python の re の \s と \d(Unicode 15.1.0 版の表)と int() に合わせるための表 */
static const unsigned _ws_rng[][2] = {{0x9,0xD},{0x1C,0x20},{0x85,0x85},{0xA0,0xA0},{0x1680,0x1680},{0x2000,0x200A},{0x2028,0x2029},{0x202F,0x202F},{0x205F,0x205F},{0x3000,0x3000}};
static const unsigned _nd_zero[] = {0x30,0x660,0x6F0,0x7C0,0x966,0x9E6,0xA66,0xAE6,0xB66,0xBE6,0xC66,0xCE6,0xD66,0xDE6,0xE50,0xED0,0xF20,0x1040,0x1090,0x17E0,0x1810,0x1946,0x19D0,0x1A80,0x1A90,0x1B50,0x1BB0,0x1C40,0x1C50,0xA620,0xA8D0,0xA900,0xA9D0,0xA9F0,0xAA50,0xABF0,0xFF10,0x104A0,0x10D30,0x11066,0x110F0,0x11136,0x111D0,0x112F0,0x11450,0x114D0,0x11650,0x116C0,0x11730,0x118E0,0x11950,0x11C50,0x11D50,0x11DA0,0x11F50,0x16A60,0x16AC0,0x16B50,0x1D7CE,0x1D7D8,0x1D7E2,0x1D7EC,0x1D7F6,0x1E140,0x1E2F0,0x1E4F0,0x1E950,0x1FBF0};
/* UTF-8 を 1 文字読む。不正なら 0 を返して進めない */
static unsigned u8next(const char **pp) {
    const unsigned char *s = (const unsigned char *)*pp; unsigned c = s[0], n, cp, min;
    if (c < 0x80) { *pp += c ? 1 : 0; return c; }
    if (c >= 0xC2 && c <= 0xDF) { n = 1; cp = c & 0x1F; min = 0x80; }
    else if (c >= 0xE0 && c <= 0xEF) { n = 2; cp = c & 0x0F; min = 0x800; }
    else if (c >= 0xF0 && c <= 0xF4) { n = 3; cp = c & 0x07; min = 0x10000; }
    else return 0;
    for (unsigned i = 1; i <= n; i++) { if ((s[i] & 0xC0) != 0x80) return 0; cp = (cp << 6) | (s[i] & 0x3F); }
    if (cp < min || cp > 0x10FFFF || (cp >= 0xD800 && cp <= 0xDFFF)) return 0;
    *pp += n + 1; return cp;
}
static int is_ws(unsigned c) {
    for (size_t i = 0; i < sizeof _ws_rng / sizeof _ws_rng[0]; i++) if (c >= _ws_rng[i][0] && c <= _ws_rng[i][1]) return 1;
    return 0;
}
static int nd_val(unsigned c) {   /* Unicode の十進数字なら 0..9、違えば -1 */
    for (size_t i = 0; i < sizeof _nd_zero / sizeof _nd_zero[0]; i++) if (c >= _nd_zero[i] && c < _nd_zero[i] + 10) return (int)(c - _nd_zero[i]);
    return -1;
}
/* Python の re.match(r"\s*([+-]?\d+)") と int() と同じ(全角などの数字も読む) */
static long long as_int_text(const char *s) {
    for (;;) { const char *q = s; unsigned c = u8next(&q); if (c && is_ws(c)) s = q; else break; }
    int neg = 0; if (*s == '+' || *s == '-') { neg = *s == '-'; s++; }
    unsigned long long v = 0; int over = 0, any = 0;
    for (;;) {
        const char *q = s; unsigned c = u8next(&q); int d;
        if (!c || (d = nd_val(c)) < 0) break;
        any = 1; s = q;
        if (v > (ULLONG_MAX - (unsigned)d) / 10) over = 1; else v = v * 10 + (unsigned)d;
    }
    if (!any) return 0;
    if (over || (!neg && v > (unsigned long long)LLONG_MAX)) return neg ? LLONG_MIN : LLONG_MAX;
    if (neg && v > (unsigned long long)LLONG_MAX + 1ULL) return LLONG_MIN;
    return neg ? (long long)(0 - v) : (long long)v;
}
static long long as_int_float(double v) {
    if (v != v) return 0;
    if (v >= 9223372036854775808.0) return LLONG_MAX;
    if (v <= -9223372036854775808.0) return LLONG_MIN;
    return (long long)v;
}
static void py_repr(double v, char *out) {      /* Python の repr(float) と同じ */
    if (v != v) { strcpy(out, "nan"); return; }
    if (isinf(v)) { strcpy(out, v < 0 ? "-inf" : "inf"); return; }
    char b[64]; int p;
    for (p = 1; p <= 17; p++) { snprintf(b, sizeof b, "%.*e", p - 1, v); if (strtod(b, NULL) == v) break; }
    char *q = b; int neg = 0; if (*q == '-') { neg = 1; q++; }
    char dg[32]; int nd = 0;
    while (*q && *q != 'e') { if (*q != '.') dg[nd++] = *q; q++; }
    int ex = atoi(q + 1);
    while (nd > 1 && dg[nd - 1] == '0') nd--;
    dg[nd] = 0;
    char *o = out; if (neg) *o++ = '-';
    if (v == 0) { strcpy(o, "0.0"); return; }
    int decpt = ex + 1;
    if (-4 <= ex && ex < 16) {
        if (decpt <= 0) { *o++ = '0'; *o++ = '.'; for (int i = 0; i < -decpt; i++) *o++ = '0'; memcpy(o, dg, nd); o += nd; }
        else if (decpt >= nd) { memcpy(o, dg, nd); o += nd; for (int i = 0; i < decpt - nd; i++) *o++ = '0'; *o++ = '.'; *o++ = '0'; }
        else { memcpy(o, dg, decpt); o += decpt; *o++ = '.'; memcpy(o, dg + decpt, nd - decpt); o += nd - decpt; }
        *o = 0;
    } else {
        *o++ = dg[0]; if (nd > 1) { *o++ = '.'; memcpy(o, dg + 1, nd - 1); o += nd - 1; }
        sprintf(o, "e%c%02d", ex < 0 ? '-' : '+', ex < 0 ? -ex : ex);
    }
}

/* ---- 命令 ---- */
static long c_open(uint64_t p, long flags) {
    char *s = cstr(p, 4096, NULL);
    if (!s || !*s || (flags != 0 && flags != 1)) { free(s); return -22; }
    char full[PATH_MAX + 8]; int r = dbpath(s, full); free(s);
    if (r == 1) return -EPERM_;
    if (r == 2) return -2;
    if (ndb >= MAXOBJ) return -12;
    int ro = flags == 1 && strcmp(full, ":memory:") != 0;
    struct stat sb;
    if (ro && stat(full, &sb) != 0) return -2;
    sqlite3 *db = NULL;
    int rc = sqlite3_open_v2(full, &db, ro ? SQLITE_OPEN_READONLY : (SQLITE_OPEN_READWRITE | SQLITE_OPEN_CREATE), NULL);
    if (rc != SQLITE_OK) { long e = errcode(rc, db ? sqlite3_errmsg(db) : "unable to open database file"); if (db) sqlite3_close(db); return e; }
    sqlite3_busy_timeout(db, 5000);
    sqlite3_set_authorizer(db, auth, NULL);
    char *em = NULL; sqlite3_exec(db, "PRAGMA foreign_keys=ON", NULL, NULL, &em); sqlite3_free(em);
    Db *d = &dbs[ndb++]; memset(d, 0, sizeof *d); d->id = next_h++; d->db = db;
    return d->id;
}
static void rmst(St *s) { sqlite3_finalize(s->p); free(s->sql); *s = sts[--nst]; }
static long c_close(long h) {
    Db *d = getdb(h); if (!d) return -9;
    for (int i = nst - 1; i >= 0; i--) if (sts[i].dbid == h) rmst(&sts[i]);
    sqlite3_close_v2(d->db); free(d->err); *d = dbs[--ndb];
    return 0;
}
/* sql を 1 文だけ準備する。成功 0、失敗は負(エラーの文面は d->err)。*stmt は NULL(空の文)もある */
static long prep(Db *d, const char *sql, sqlite3_stmt **stmt) {
    const char *tail = NULL;
    int rc = sqlite3_prepare_v2(d->db, sql, -1, stmt, &tail);
    if (rc != SQLITE_OK) { *stmt = NULL; return fail(d, rc); }
    if (*skip_sql(tail)) { sqlite3_finalize(*stmt); *stmt = NULL; seterr(d, "You can only execute one statement at a time."); return -22; }
    return 0;
}
static long c_exec(Db *d, const char *sql) {
    sqlite3_stmt *st; long e = prep(d, sql, &st); if (e) return e;
    if (!st) { d->changes = 0; return 0; }
    if (sqlite3_bind_parameter_count(st) > 0) { sqlite3_finalize(st); seterr(d, "Incorrect number of bindings supplied."); return -22; }
    int rc = sqlite3_step(st);
    if (rc != SQLITE_ROW && rc != SQLITE_DONE) { sqlite3_finalize(st); return fail(d, rc); }
    long r = is_dml(sql) ? sqlite3_changes(d->db) : 0;
    sqlite3_finalize(st);
    d->changes = r; return r;
}
static long c_prepare(Db *d, const char *sql) {
    if (nst >= MAXOBJ) return -12;
    sqlite3_stmt *p; long e = prep(d, sql, &p); if (e) return e;
    if (!p) { seterr(d, "empty statement"); return -22; }
    St *s = &sts[nst++]; memset(s, 0, sizeof *s);
    s->id = next_h++; s->dbid = d->id; s->p = p; s->np = sqlite3_bind_parameter_count(p); s->sql = strdup(sql);
    return s->id;
}
static void restart(St *s) { sqlite3_reset(s->p); s->started = s->done = s->hasrow = 0; }
static long c_step(St *s) {
    Db *d = getdb(s->dbid); if (!d) return -9;
    if (s->done) { s->hasrow = 0; return 0; }
    s->started = 1;
    int rc = sqlite3_step(s->p);
    if (rc == SQLITE_ROW) { s->hasrow = 1; return 1; }
    if (rc == SQLITE_DONE) {
        s->done = 1; s->hasrow = 0;
        if (sqlite3_column_count(s->p) == 0) d->changes = is_dml(s->sql) ? sqlite3_changes(d->db) : 0;
        return 0;
    }
    long e = fail(d, rc); restart(s); return e;
}
static long c_col(St *s, int n, long i, uint64_t dst, long mx) {
    if (!s->started || sqlite3_column_count(s->p) == 0) return -22;
    if (n == 10) return sqlite3_column_count(s->p);
    if (i < 0 || i >= sqlite3_column_count(s->p)) return -22;
    if (n == 14) { const char *nm = sqlite3_column_name(s->p, (int)i); return put(dst, mx, nm ? nm : "", nm ? strlen(nm) : 0); }
    if (!s->hasrow) return -22;
    int t = sqlite3_column_type(s->p, (int)i);
    if (n == 11) return t == SQLITE_INTEGER ? 1 : t == SQLITE_FLOAT ? 2 : t == SQLITE_TEXT ? 3 : t == SQLITE_BLOB ? 4 : 5;
    if (n == 12) {
        if (t == SQLITE_INTEGER) return (long)sqlite3_column_int64(s->p, (int)i);
        if (t == SQLITE_FLOAT) return (long)as_int_float(sqlite3_column_double(s->p, (int)i));
        if (t == SQLITE_TEXT) return (long)as_int_text((const char *)sqlite3_column_text(s->p, (int)i));
        return 0;
    }
    char b[64];
    if (t == SQLITE_INTEGER) { snprintf(b, sizeof b, "%lld", (long long)sqlite3_column_int64(s->p, (int)i)); return put(dst, mx, b, strlen(b)); }
    if (t == SQLITE_FLOAT) { py_repr(sqlite3_column_double(s->p, (int)i), b); return put(dst, mx, b, strlen(b)); }
    if (t == SQLITE_NULL) return put(dst, mx, "", 0);
    const void *v = t == SQLITE_TEXT ? (const void *)sqlite3_column_text(s->p, (int)i) : sqlite3_column_blob(s->p, (int)i);
    return put(dst, mx, v ? (const char *)v : "", (size_t)sqlite3_column_bytes(s->p, (int)i));
}

long sign_db_call(const unsigned long *r) {
    long n = (long)r[0], a = (long)r[1], b = (long)r[2], c = (long)r[3], dd = (long)r[4];
    if (n < 1 || n > 19) return -22;
    if (n == 1) return c_open((uint64_t)a, b);
    if (n == 2) return c_close(a);
    if (n == 3 || n == 4) {
        Db *d = getdb(a); if (!d) return -9;
        char *sql = cstr((uint64_t)b, MAXSTR, NULL);
        if (!sql || blank(sql)) { free(sql); return -22; }
        long e;
        if (bad_sql(sql)) e = -EPERM_; else e = n == 3 ? c_exec(d, sql) : c_prepare(d, sql);
        free(sql); return e;
    }
    if (n >= 17) {
        Db *d = getdb(a); if (!d) return -9;
        if (n == 17) return (long)sqlite3_last_insert_rowid(d->db);
        if (n == 18) return d->changes;
        return put((uint64_t)b, c, d->err ? d->err : "", d->err ? strlen(d->err) : 0);
    }
    St *s = getst(a); if (!s) return -9;
    if (n >= 5 && n <= 8) {
        if (b < 1 || b > s->np) return -22;
        restart(s);
        if (n == 5) return sqlite3_bind_int64(s->p, (int)b, (sqlite3_int64)c) == SQLITE_OK ? 0 : -5;
        if (n == 6) { char *t = cstr((uint64_t)c, MAXSTR, NULL); if (!t) return -22; int rc = sqlite3_bind_text(s->p, (int)b, t, -1, SQLITE_TRANSIENT); free(t); return rc == SQLITE_OK ? 0 : -5; }
        if (n == 7) return sqlite3_bind_null(s->p, (int)b) == SQLITE_OK ? 0 : -5;
        unsigned char *x = blob((uint64_t)c, (uint64_t)dd); if (!x) return -22;
        int rc = sqlite3_bind_blob64(s->p, (int)b, x, (sqlite3_uint64)dd, SQLITE_TRANSIENT); free(x); return rc == SQLITE_OK ? 0 : -5;
    }
    if (n == 9) return c_step(s);
    if (n == 15) { restart(s); return 0; }
    if (n == 16) { rmst(s); return 0; }
    return c_col(s, (int)n, b, (uint64_t)c, dd);
}
