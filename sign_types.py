"""Sign の型の静的パス(type_system.md §5: Pass 1a / 1b / 2 / 3 / 3b)

  Pass 1a  識別子の構造型(Lambda / Atom とアリティ)。自己参照・相互参照は Atom に倒す
  Pass 1b  呼び出しサイトの実引数の型から仮引数の型を決める(観測した種類を信じる。型変数・単一化は使わない)
  Pass 2   余積(空白)の静的な解決。実行時の解決(coproduct_resolver.md)と同じ段の順
  Pass 3   左辺優先ルールで Layer 2 の型(Int / Char / String / Address / Float / List(T) / Struct …)を伝播
  Pass 3b  `__` へ収束すると静的に分かった箇所と理由を帳簿(diagnostics)に残す

出力: `.ist`(内部・全識別子)と `.st`(公開 # だけ)。lower.sn の入力にそのまま使える形。
使い方:  python sign_types.py file.sn [--st] [--diag] [--layer N] [--alpha] [--layout [--charset ascii|utf32]]
  --layout   形の解決(Pass 3.5): 識別子ごとに実体(規則か要素の並びか)と AArch64 の大きさを出す
  --layer N  リテラルの layer 制約を検査する(省略時は隣の option.ms の layer)。小数点は 2 以上、Vector は 3 以上
  --alpha    0r・0b を UInt ではなく Int と型付ける(alpha の現状)
型: Int UInt Address Float Vector Char String List(T) Struct Iterator(T) Reader(T) Lambda と、恒等射 `_`(Id)。
形(Pass 3.5): [0 ~+ 1] は規則 16 byte、[1 ~ 5] は規則 24 byte、[1 2 3 4 5] は要素 40 byte(Int)。
  構造体のスロットは「運ぶ姿」を自然境界に置く(String/List は {ptr,len}=16、Struct は {ptr}=8)。名前付きは名前順。
未実装: Implicit(T) の作り手(前置 # ## ###)、他ターゲットの幅、ジェネリックな仮引数の呼び出しサイトごとの具体化。
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sign_interp as S

# ---------------------------------------------------------------- 型
INT, FLOAT, CHAR, STRING, ADDR, UNIT_T, ANY, SCALAR = "Int", "Float", "Char", "String", "Address", "Unit", "Atom", "Scalar"
class _MarkT(str): pass
MARK_T = _MarkT("Unit")                         # 書いた `_`。型としては Unit と等しいが、既定値の口に当たれば既定値で埋まる(`dd _ 2`)印
UINT, VECTOR, ID_T = "UInt", "Vector", "Id"       # Id は恒等射(.st では `_`)。Scalar = Int | UInt | Address | Float | Vector
NUMERIC = {INT, FLOAT, ADDR, SCALAR, UINT, VECTOR}
BITWISE = {INT, UINT, ADDR}                       # ビット演算が扱う GPR 幅の整数(住処は UInt)
ERROR_KINDS = {"range-no-progress", "float-literal-layer", "struct-runtime-index", "function-return-without-address", "name-cycle", "bare-function-return", "unknown-input", "instance-nest-limit"}    # 帳簿のうち、information ではなくコンパイルエラーになるもの

class _Frozen:                                 # 凍結した値の型(dataclass(frozen=True) と同じ: 欄で等しく、欄でハッシュ、書き換えは AttributeError、repr は 名前(欄=値, …))
    __slots__ = ()
    def __setattr__(self, k, v): raise AttributeError("cannot assign to field %r" % k)
    def __delattr__(self, k): raise AttributeError("cannot delete field %r" % k)
    def _vals(self): return tuple(getattr(self, f) for f in self._FIELDS)
    def __eq__(self, o): return o.__class__ is self.__class__ and self._vals() == o._vals()
    def __hash__(self): return hash(self._vals())
    def __reduce__(self): return (self.__class__, self._vals())       # pickle・copy・deepcopy が通る(欄の値で作り直す。dataclass のときと同じ)
    def __repr__(self): return "%s(%s)" % (type(self).__name__, ", ".join("%s=%r" % (f, getattr(self, f)) for f in self._FIELDS))

class Fn(_Frozen):                             # Lambda 型。bound は適用済みの実引数の型
    __slots__ = _FIELDS = ("name", "params", "bound", "ret", "variadic", "sec")
    def __init__(self, name=None, params=(), bound=(), ret=ANY, variadic=False, sec=None):   # sec: ポイントフリーの素性: ("fold", op) / ("map", op, kind, operand)
        o = object.__setattr__
        o(self, "name", name); o(self, "params", params); o(self, "bound", bound); o(self, "ret", ret); o(self, "variadic", variadic); o(self, "sec", sec)

def is_fn(t): return isinstance(t, Fn)
def remaining(f): return len(f.params) - len(f.bound)
def needs_more(f): return f.variadic or remaining(f) >= 1
def is_list(t): return isinstance(t, tuple) and t[:1] == ("List",)
def is_struct(t): return isinstance(t, tuple) and t[:1] == ("Struct",)
def is_open(t): return isinstance(t, tuple) and t[:1] == ("Open",)
def is_stream(t): return isinstance(t, tuple) and t[:1] == ("Stream",)
def is_iter(t): return isinstance(t, tuple) and t[:1] == ("Iterator",)       # 終端を持たない規則の列(|.| が答えられない)
def is_addr_of(t): return isinstance(t, tuple) and t[:1] == ("Addr",)       # $x : 参照先の型を運ぶ Address

def norm(t):                                    # 演算子の項として読むときの型: 参照先を辿る・読む値へ戻す
    if is_addr_of(t): return ADDR
    if isinstance(t, tuple) and t[:1] in (("Reader",), ("Implicit",)): return t[1]
    return t

def unify(ts):                                 # 観測した型を1つにまとめる(制約解決ではなく、揃うかどうかだけを見る)
    ts = [t for t in ts if t not in (UNIT_T, ANY)]
    if not ts: return ANY
    if all(t in (CHAR, STRING) for t in ts) and STRING in ts: return STRING     # Char | String は広い方 String に揃える
    if all(t == ts[0] for t in ts): return ts[0]
    if all(t in NUMERIC for t in ts): return FLOAT if FLOAT in ts else SCALAR
    return ANY

def seq_type(elems):                           # 要素の型が揃えば List(T)、揃わなければ Struct(§2)
    elems = [e for e in elems if e != UNIT_T]
    if not elems: return UNIT_T
    if all(e == elems[0] for e in elems): return ("List", elems[0])
    if FLOAT in elems and all(e in (INT, UINT, ADDR, FLOAT, SCALAR) for e in elems):
        return ("List", FLOAT)                         # `1 , 2.5` は 1 が Float へ昇格して並ぶ → List(Float)(FPU ロード1つで済む)
    return ("Struct", tuple((None, e) for e in elems))

def show_t(t):
    if is_fn(t):
        ps = [show_t(p) for p in t.params[len(t.bound):]] if not t.variadic else ["Atom..."]
        return " ".join(ps + ["->", show_t(t.ret)]) if ps else "-> " + show_t(t.ret)
    if t == ID_T: return "_"
    if is_addr_of(t): return "Address"
    if isinstance(t, tuple) and t[:1] in (("Iterator",), ("Reader",), ("Implicit",)): return f"{t[0]}({show_t(t[1])})"
    if is_list(t): return f"List({show_t(t[1])})"
    if is_stream(t): return f"Stream({show_t(t[1])})"
    if is_struct(t): return "Struct{" + " ".join(f"{k if k else ''}:{show_t(v)}" for k, v in t[1]) + "}"
    return str(t)

class Scope:
    def __init__(self, parent=None): self.vars, self.parent = {}, parent
    def get(self, n):
        e = self
        while e:
            if n in e.vars: return e.vars[n]
            e = e.parent
        return None

# ---------------------------------------------------------------- 検査器
STRICT_R91 = True
ADDR_PAIR = {("+", "pt", "diff"): "pt", ("+", "pt", "hex"): "pt", ("+", "diff", "diff"): "diff", ("+", "diff", "pt"): "pt", ("+", "hex", "pt"): "pt",
             ("+", "diff", "hex"): "diff", ("+", "hex", "diff"): "diff", ("-", "pt", "pt"): "diff", ("-", "pt", "diff"): "pt", ("-", "pt", "hex"): "pt",
             ("-", "diff", "diff"): "diff", ("-", "diff", "hex"): "diff",
             ("-", "hex", "diff"): "diff", ("+", "hex", "hex"): "hex", ("-", "hex", "hex"): "hex", ("/", "diff", "int"): "int"}      # R62・R98
ADDR_NAME = {"pt": "点", "diff": "差", "hex": "`0x…`", "int": "Int", "sum": "`0x…` の和"}
class Checker:
    def __init__(self, nodes, base_dir=".", stack=(), layer=None, alpha=False):
        self.layer, self.alpha = layer, alpha     # layer: option.ms の layer(None なら検査しない) / alpha: 0r・0b を Int と型付ける
        self.nodes, self.base_dir, self.stack = nodes, base_dir, tuple(stack)
        self.erased = set()                                          # R113: `x : _`(右辺が書いた `_` 1つだけ)は書かなかったことと同じ。その名前は undefined-identifier を出さない
        def _scan(x):
            if isinstance(x, tuple):
                if len(x) == 3 and x[0] == "def" and x[2] == ("hole",): self.erased.add(x[1])
                if x and x[0] == "cases" and isinstance(x[1], list):
                    for r in x[1]:
                        if isinstance(r, tuple) and len(r) == 2 and r[0] is not None and r[0][0] == "id" and r[1] == ("hole",): self.erased.add(r[0][1])
                for c in x: _scan(c)
            elif isinstance(x, list):
                for c in x: _scan(c)
        _scan(nodes)
        self.defs, self.exports, self.order = {}, set(), []
        self.imported = {}                     # `f`@~ で入った名前 → 型
        self.types, self.resolving = {}, set()
        self.params = {}                       # 関数名 → 観測した仮引数の型
        self.optional = {}                     # 関数名 → 既定値のある口の位置
        self.brackets = {}                     # 関数名 → 括りの口の位置(R83: 参照の口は __ を空の器 [] で受ける)
        self.callsites = {}                    # 関数名 → [実引数の型の並び]
        self.diags, self.import_diags = [], []
        self.where = "<top>"
        self.gather()
        self.import_diags = list(self.diags)

    # --- 診断(Pass 3b) ---
    def note(self, kind, detail=""):
        item = (kind, self.where, detail)
        if item not in self.diags: self.diags.append(item)

    # --- Pass 1a: 識別子テーブルの収集 ---
    def gather(self):
        for node in self.nodes:
            exported = node[0] == "export"
            d = node[1] if exported else node
            if d[0] == "def":
                self.defs[d[1]] = d[2]; self.order.append(d[1])
                if exported: self.exports.add(d[1])
            elif d[0] == "importspread": self.load_import(d)

    def load_import(self, node):
        path = node[1][1] if node[1][0] == "lit" else None
        full = os.path.abspath(os.path.join(self.base_dir, path)) if isinstance(path, str) else None
        if not full or not os.path.exists(full) or full in self.stack:
            self.where = "<import>"; self.note("import-failed", str(path)); return
        try:
            sub = Checker(S.parse_source(open(full, encoding="utf-8").read()), os.path.dirname(full),
                          self.stack + (full,), self.layer, self.alpha)
            sub.solve()
        except (SyntaxError, NotImplementedError) as e:
            self.note("import-failed", f"{path}: {e}"); return
        names = sub.exports or set(sub.defs)           # 公開があれば公開だけ。無ければ頂の束縛を全部(alpha)
        for n in names: self.imported[n] = sub.def_type(n)
        if not sub.exports:                            # 公開の無いファイルは、自分が取り込んだ名前も見せる
            for n, t in sub.imported.items(): self.imported.setdefault(n, t)

    def def_type(self, name):
        if name in self.types: return self.types[name]
        if name in self.resolving:
            rhs = self.defs[name]
            if rhs[0] == "lam":                         # `?` があれば Lambda(アリティも構文で決まる)。返値だけが未確定
                obs = self.params.get(name, [])
                return Fn(name, tuple(obs[i] if i < len(obs) else ANY for i in range(len(rhs[1]))), (), ANY)
            if not getattr(self, "lift_depth", 0): self.note("name-cycle", f"{name} の定義が自分自身へ戻る輪に値の定義を含む(種類が決まらない)")
            return ANY                                  # 値としての自己参照・相互参照は Atom へ倒す
        self.resolving.add(name)
        saved = self.where; self.where = name
        try:
            rhs = self.defs[name]
            t = self.lam_type(name, rhs, Scope()) if rhs[0] == "lam" else self.type_of(rhs, Scope())
        finally:
            self.where = saved; self.resolving.discard(name)
        self.types[name] = t
        return t

    def lam_type(self, name, node, scope):
        sc = Scope(scope); ptypes = []
        obs = self.params.get(name, []) if name else []
        if name: self.brackets[name] = {i for i, sp in enumerate(node[1]) if sp[0] == "destr"}
        if name: self.optional[name] = {i for i, sp in enumerate(node[1]) if (sp[0] == "name" and sp[2] is not None) or (sp[0] == "destr" and len(sp) > 3 and sp[3])}
        for i, spec in enumerate(node[1]):
            if spec[0] == "name":
                t = obs[i] if i < len(obs) else ANY
                if spec[2] is not None:                 # 既定値があれば、その型が仮引数の型の下限
                    dt = self.type_of(spec[2], sc)
                    if t in (ANY,) and dt != UNIT_T: t = dt
                sc.vars[spec[1]] = t
            else:                                       # 括り仮引数: 器を割って受ける
                t = obs[i] if i < len(obs) else ANY
                elem = t[1] if is_list(t) else (CHAR if t == STRING else ANY)
                dfl = spec[3] if len(spec) > 3 and isinstance(spec[3], dict) else {}
                for n in list(spec[1]) + list(spec[4] if len(spec) > 4 else []):
                    sc.vars[n] = self.type_of(dfl[n], sc) if (n in dfl and elem == ANY and self.type_of(dfl[n], sc) != UNIT_T) else elem     # [x : 1] の x は既定値の型が下限
                if spec[2]: sc.vars[spec[2]] = ("List", elem) if elem != ANY else ANY
            ptypes.append(t)
        ret = self.type_of(node[2], sc)
        if name and is_fn(ret) and ret.bound:       # 捕まえる値が実行時に決まる関数は、$ で関数オブジェクトの番地を返す
            self.note("function-return-without-address",
                      f"{name} は関数(捕まえた値あり)を返す。$ を付けて関数オブジェクトの番地で返す(execution_model.md §4)")
        return Fn(name, tuple(ptypes), (), ret)

    # --- 全体を解く: Pass 1b を不動点で ---
    def solve(self, rounds=5):
        for _ in range(rounds):
            self.callsites, self.types, self.diags = {}, {}, list(self.import_diags)
            for name in self.order: self.def_type(name)
            self.where = "<top>"
            for node in self.nodes:
                d = node[1] if node[0] == "export" else node
                if d[0] != "def": self.type_of(d, Scope())
            new = {}
            for name, sites in self.callsites.items():
                n = max(len(a) for a in sites)
                new[name] = [unify([a[i] for a in sites if len(a) > i]) for i in range(n)]
            if new == self.params: break
            self.params = new
        return self

    def record(self, f, bound):
        if f.name: self.callsites.setdefault(f.name, []).append(bound)

    # --- Pass 2: 余積の静的な解決 ---
    def apply(self, f, a):
        brk = a == UNIT_T and f.name is not None and len(f.bound) in self.brackets.get(f.name, ())      # R83・R90: 参照の口の __ は空の器で、分解が立たなければ本体を読まずに _(A)
        if brk and not f.variadic:
            bound = f.bound + (a,)
            if f.name: self.record(f, bound)
            if len(bound) >= len(f.params): return ANY if all(b != UNIT_T or i in self.brackets.get(f.name, ()) for i, b in enumerate(bound)) else UNIT_T
            return Fn(f.name, f.params, bound, f.ret, False, f.sec)
        opt = isinstance(a, _MarkT) and f.name is not None and len(f.bound) in self.optional.get(f.name, ())      # 書いた `_` が既定値のある口に当たれば既定値で埋まる
        if a == UNIT_T and not f.variadic and remaining(f) >= 1 and not opt:
            self.note("completeness-axiom", f"{f.name or '<fn>'} に __ を渡している(呼び出しは __ に崩壊する)")
        bound = f.bound + (a,)
        if f.name and not f.variadic: self.record(f, bound)
        if f.variadic: return Fn(f.name, f.params, bound, f.ret, True, f.sec)
        if len(bound) >= len(f.params) and a != UNIT_T and UNIT_T not in bound: return self.expect_ret(f)
        if len(bound) >= len(f.params) and opt and all(b != UNIT_T or isinstance(b, _MarkT) for b in bound): return self.expect_ret(f)
        if len(bound) >= len(f.params): return UNIT_T
        return Fn(f.name, f.params, bound, f.ret, False, f.sec)

    def expect_ret(self, f): return f.ret

    def finalize(self, t):
        if is_open(t): t = seq_type(list(t[1]))
        if is_fn(t) and t.variadic and t.bound and t.sec:
            kind = t.sec[0]
            if kind == "fold":
                args = list(t.bound)
                if len(args) == 1: return args[0]
                acc = args[0]
                for x in args[1:]: acc = self.bin_type(t.sec[1], acc, x)
                return acc
            op, side, operand = t.sec[1], t.sec[2], t.sec[3]
            elem = unify([self.bin_type(op, x, operand) if side == "right" else self.bin_type(op, operand, x) for x in t.bound])
            return ("List", INT if op in S.CMP else elem)
        if is_fn(t) and not t.variadic and t.bound and len(t.bound) >= 1 and remaining(t) <= 0: return t.ret
        return t

    def join(self, a, b):                           # Atom ⊙ Atom (list_model.md §2.2)
        if a == UNIT_T: return b
        if b == UNIT_T: return a
        if (a == STRING or a == CHAR) and (b in (STRING, CHAR) or b in NUMERIC): return STRING
        if b == STRING and (a in NUMERIC): return STRING
        if is_open(a) and b == STRING and all(x in NUMERIC or x in (STRING, CHAR) for x in a[1]): return STRING
        left = list(a[1]) if is_open(a) else ([a[1]] if is_stream(a) else [a])
        if is_stream(a): left = [a[1]]
        right = [b[1]] if is_stream(b) else [b]
        return ("Open", tuple(left + right))

    def resolve(self, ts):
        items = list(ts)
        phases = [
            (lambda a, b: is_fn(a) and is_fn(b), lambda a, b: Fn(a.name, a.params, a.bound, b.ret, a.variadic, a.sec)),
            (lambda a, b: is_fn(a) and not is_fn(b) and needs_more(a), self.apply),
            (lambda a, b: not is_fn(a) and not is_fn(b), self.join),
            (lambda a, b: is_fn(a) and not is_fn(b), self.apply),
            (lambda a, b: not is_fn(a) and is_fn(b) and b.sec is None, lambda a, b: UNIT_T if a == UNIT_T else self.apply(b, a)),
        ]
        for pred, red in phases:
            again = True
            while again and len(items) > 1:
                again = False
                for i in range(len(items) - 1):
                    if pred(items[i], items[i + 1]):
                        items[i:i + 2] = [red(items[i], items[i + 1])]; again = True; break
        acc = items[0]
        for t in items[1:]: acc = ANY if is_fn(acc) or is_fn(t) else self.join(acc, t)
        return self.finalize(acc)

    # --- Pass 3: 演算子の型(左辺優先ルール) ---
    def bin_type(self, op, lt, rt):
        lt, rt = norm(self.fin(lt)), norm(self.fin(rt))
        if op in ("+", "-", "*", "/", "%", "^"):
            if op in ("/", "%") and rt in (INT, ADDR) and getattr(self, "_zero", False):
                self.note("divide-by-zero-literal", f"整数を字面の 0 で割る({op})")
            if lt == UNIT_T: return rt if rt in NUMERIC else UNIT_T
            if rt == UNIT_T: return lt if lt in NUMERIC else UNIT_T
            if lt == STRING:
                if op == "*" and rt == INT: return STRING
                self.note("arith-type-mismatch", f"String に {op} の射は無い"); return UNIT_T
            if is_list(lt) or is_struct(lt):
                if op in ("*", "^", "/") and rt == INT: return ("List", lt) if op == "^" else lt
                self.note("arith-type-mismatch", f"List に {op} の射は無い"); return UNIT_T
            if lt == CHAR:                              # 文字は位置(§3.6)
                if rt == CHAR: return INT if op == "-" else (CHAR if op == "+" else UNIT_T)
                if op in ("+", "-") and rt in (INT, ANY, SCALAR): return CHAR
                if op == "*" and rt == INT: return STRING
                return UNIT_T
            if rt == STRING or is_list(rt) or is_struct(rt) or rt == CHAR and lt in NUMERIC:
                if rt == CHAR and lt in NUMERIC: return lt if lt != ANY else INT
                self.note("arith-type-mismatch", f"{show_t(lt)} {op} {show_t(rt)}"); return UNIT_T
            if lt == ADDR and op in ("*", "^"): return UNIT_T          # 番地の * ^ は射が無い
            if lt == VECTOR: return VECTOR                             # Vector は要素ごと。左辺が域を決める
            if FLOAT in (lt, rt): return FLOAT
            if lt in (ANY, SCALAR):                      # 仮引数が算術に使われた → 数値(Scalar)
                return rt if rt in (INT, ADDR) and lt == SCALAR else SCALAR
            return lt                                    # Int / Address / UInt は左辺が域を決める
        if op in ("<<", ">>"):                                         # L(Address|Int|UInt) -> (Int|UInt)。Address の << は射が無い
            if lt == ADDR: return UNIT_T
            return lt if lt in (INT, UINT) else (INT if lt in (ANY, SCALAR) else UNIT_T)
        if op in ("||", ";;", "&&"):                                   # 両辺をビット列として読む。左辺が域を決める
            if lt in BITWISE and (rt in BITWISE or rt in (ANY, SCALAR)): return lt
            if lt in (ANY, SCALAR) and rt in BITWISE: return rt if rt != ADDR else INT
            self.note("arith-type-mismatch", f"{show_t(lt)} {op} {show_t(rt)}(ビット列として読めない)"); return UNIT_T
        if op in ("~+", "~-", "~*", "~/", "~^"):                       # 派生範囲: 端点は数値のみ。終端の無い列
            if (lt in NUMERIC or lt == ANY) and (rt in NUMERIC or rt == ANY):
                return ("Iterator", FLOAT if FLOAT in (lt, rt) else (INT if INT in (lt, rt) or ANY in (lt, rt) else lt))
            self.note("range-endpoint-not-a-point", f"{show_t(lt)} {op} {show_t(rt)}(派生範囲の端点は数値のみ)"); return UNIT_T
        if op in S.CMP:
            if op not in ("=", "==", "!=", "!==") and (is_list(lt) or is_struct(lt) or is_fn(lt) or is_list(rt)):
                self.note("compare-non-scalar", f"{op} は Scalar か文字にだけ射を持つ"); return UNIT_T
            if lt in NUMERIC and rt in NUMERIC: return FLOAT if FLOAT in (lt, rt) else lt
            return lt if lt != UNIT_T else rt
        if op == "&": return rt
        if op in ("|", ";"): return unify([lt, rt]) if UNIT_T not in (lt, rt) else (rt if lt == UNIT_T else lt)
        if op == "~":
            if is_iter(lt) and (rt in NUMERIC or rt == ANY): return ("List", lt[1])   # 終端を与えると数えられる List になる
            if lt == CHAR and rt == CHAR: return STRING
            if lt in NUMERIC and rt in NUMERIC: return ("List", INT)
            self.note("range-endpoint-not-a-point", f"{show_t(lt)} ~ {show_t(rt)}"); return UNIT_T
        if op in ("'", "@"): return self.get_type(lt)
        if op == "#": return ADDR
        if op == ",": return seq_type(self.prod_elems([lt, rt]))
        return ANY

    def fin(self, t): return self.finalize(t)

    def prod_elems(self, ts):
        out = []
        for t in ts:
            if is_stream(t): out.append(t[1])
            elif t != UNIT_T: out.append(t)
        return out

    def get_type(self, obj):
        obj = self.fin(obj)
        if is_list(obj): return obj[1]
        if obj == STRING: return CHAR
        if is_struct(obj): return unify([v for _, v in obj[1]])
        return ANY

    def lit_type(self, node):
        if len(node) > 2:
            tag = node[2]
            return INT if tag == UINT and self.alpha else tag          # 0r・0b は UInt(alpha は Int)、0x は Address
        v = node[1]
        if isinstance(v, S.Char): return CHAR
        if isinstance(v, str): return STRING
        if isinstance(v, float):
            if self.layer is not None and self.layer < 2:              # FPU が初期化されていない層では浮動小数点を使えない
                self.note("float-literal-layer", f"小数点のあるリテラル {v} は layer 2 以上(今は layer {self.layer})")
            return FLOAT
        if isinstance(v, bool): return ANY
        if isinstance(v, int): return INT
        return UNIT_T

    def type_of(self, n, sc):
        k = n[0]
        if k == "lit": return self.lit_type(n)
        if k == "id":
            t = sc.get(n[1])
            if t is None:
                if n[1] in self.defs: t = self.def_type(n[1])
                elif n[1] in self.imported: t = self.imported[n[1]]
                elif n[1] == "vec4": t = Fn("vec4", (FLOAT,) * 4, (), VECTOR)     # 組込み: 4 つの Float から Vector
                else:
                    if n[1] != "__" and n[1] not in self.erased: self.note("undefined-identifier", n[1])
                    return UNIT_T
            return t
        if k in ("hole",): return MARK_T
        if k == "block":
            inner = n[1]
            if (inner[0] == "seq" and len(inner[1]) == 4 and all((m[0] == "lit" and isinstance(m[1], float)) or (m[0] == "neg" and len(m) == 2 and m[1][0] == "lit" and isinstance(m[1][1], float)) for m in inner[1])
                    and self.layer is not None and self.layer >= 3):
                return VECTOR                                          # [1.0 2.0 3.0 4.0] : layer 3 以上の SIMD 型(4要素の字面)
            return self.type_of(inner, sc)
        if k == "seq":
            ts = [self.type_of(m, sc) for m in self.empties_to_holes(n[1])]
            if len(ts) > 1 and any(isinstance(t, _MarkT) for t in ts):
                if is_fn(ts[0]) and any(isinstance(t, _MarkT) for t in ts[1:-1]): return ANY      # R38・R86: 内側の書いた _ は穴(カリー化)で、型は決めない
                ts = [t for i, t in enumerate(ts) if not (isinstance(t, _MarkT) and not (i == 0 and len(ts) == 1))]    # 値の隣・末尾の書いた _ は消える(R15・R138・R43)
                if not ts: return UNIT_T
            return self.resolve(ts)
        if k == "def": return self.type_of(n[2], sc)
        if k == "export": return self.type_of(n[1], sc)
        if k == "opdef": return UNIT_T
        if k == "lam": return self.lam_type(None, n, sc)
        if k == "cases":
            vals = []
            for cond, expr in n[1]:
                if cond is not None: self.type_of(cond, sc)
                vals.append(self.type_of(expr, sc))
            return unify(vals) if len(vals) > 1 else (vals[0] if vals else UNIT_T)
        if k == "bin" and n[1] in ("'", "@"):
            key_node, obj_node = (n[3], n[2]) if n[1] == "'" else (n[2], n[3])
            obj = self.fin(self.type_of(obj_node, sc))
            if is_struct(obj):
                named = any(key is not None for key, _ in obj[1])
                if key_node[0] == "id" and named:                          # 名前付きスロットに印の無い識別子: 名前
                    for key, v in obj[1]:
                        if key == key_node[1]: return v
                    self.note("struct-missing-key", key_node[1]); return UNIT_T
                if key_node[0] == "lit" and isinstance(key_node[1], str):                  # 文字列の字面の鍵: 名前(`d ' `#``)
                    for key, v in obj[1]:
                        if key == str(key_node[1]): return v
                    self.note("struct-missing-key", str(key_node[1])); return UNIT_T
                if key_node[0] == "lit" and isinstance(key_node[1], int):                 # 字面の添字(名前付きなら宣言順の N 番目。物理位置ではない: stack_abi.md §7.1)
                    i = key_node[1]
                    if 0 <= i < len(obj[1]): return obj[1][i][1]
                    self.note("struct-missing-key", f"スロット {i}"); return UNIT_T
                if named and key_node[0] == "post" and key_node[1] == "~" and key_node[2][0] != "lit":
                    return unify([v for _, v in obj[1]])                   # s ' k~ : 名前付きスロットは実行時の鍵で引ける
                if not named and key_node[0] == "post" and key_node[1] == "~" and key_node[2][0] == "lit" and isinstance(key_node[2][1], int) and key_node[2][1] >= 0:
                    return ("Struct", tuple(obj[1][key_node[2][1]:]))          # 字面の切り出し `s ' 1~`: 実行時の添字ではない。残りのスロット
                self.note("struct-runtime-index", "多相な連番スロットへの実行時インデックスは命令を選べない(断る形)")
                return UNIT_T
            if key_node[0] == "post" and key_node[1] == "~":
                inner = key_node[2]
                if inner[0] == "lit" or (inner[0] == "post" and inner[1] == "~"):
                    return obj if is_list(obj) or obj == STRING else ANY       # 切り出しは器のまま
            self.type_of(key_node, sc)
            return self.get_type(obj)
        if k == "bin" and n[1] == "~" and n[2][0] == "bin" and n[2][1] in ("~+", "~-", "~*", "~/", "~^") and n[2][3][0] == "lit" \
                and not isinstance(n[2][3][1], (bool, str)) and n[2][3][1] == (0 if n[2][1] in ("~+", "~-") else 1):
            self.note("range-no-progress", f"`{n[2][1]} {n[2][3][1]}` は刻みが単位元で、閉じた派生範囲 `[a {n[2][1]} s ~ b]` が先へ進みません(stack_abi §1.2)。開端レンジ `[a {n[2][1]} s]` にするか、刻みを変えます")
        if k == "bin":
            op = n[1]
            lt = self.leftover_operand(self.type_of(n[2], sc), op)
            self._zero = n[3][0] == "lit" and n[3][1] == 0 and not isinstance(n[3][1], bool)
            r = self.leftover_operand(self.type_of(n[3], sc), op)
            self._zero = n[3][0] == "lit" and n[3][1] == 0 and not isinstance(n[3][1], bool)
            out = self.bin_type(op, lt, r)
            self._zero = False
            return out
        if k == "cmp":
            ts = [self.leftover_operand(self.type_of(x, sc), n[2][0]) for x in n[1]]
            out = ts[0]
            for i, op in enumerate(n[2]): out = self.bin_type(op, ts[i], ts[i + 1])
            return out
        if k == "prod": return seq_type(self.prod_elems([self.type_of(x, sc) for x in n[1]]))
        if k == "not":                                                # !x : 恒等射か __。__ に当てれば恒等射(.st では _)
            t = self.fin(self.type_of(n[1], sc))
            return ID_T if t in (UNIT_T, ANY, ID_T) else UNIT_T
        if k in ("neg", "abs"):
            t = self.leftover_operand(self.type_of(n[1], sc), "-"); return t if t in NUMERIC else (SCALAR if t == ANY else UNIT_T)
        if k == "bnot": t = self.type_of(n[1], sc); return t if t in NUMERIC else (SCALAR if t == ANY else UNIT_T)
        if k == "norm":
            t = self.fin(self.type_of(n[1], sc))
            if is_iter(t): self.note("iterator-has-no-length", "終端の無い列に |.| は答えられない(__)"); return UNIT_T
            return INT
        if k == "lift":                                               # 前置 ~ : T -> List(T)。器に当てれば恒等
            t = self.fin(self.type_of(n[1], sc))
            if isinstance(t, _MarkT): return t                         # R88: `~_` は書いた `[_]` と同じ項で `_`
            return t if is_list(t) or t == STRING else ("List", t)
        if k == "post":
            t = self.fin(self.type_of(n[2], sc))
            if n[1] == "!":                                           # 階乗: 左辺が域を決める。Address は射が無い
                if t == ADDR: return UNIT_T
                return t if t in NUMERIC else (INT if t == ANY else UNIT_T)
            if n[1] == "~":
                if is_list(t): return ("Stream", t[1][1] if is_list(t[1]) else t[1])
                if t == STRING: return ("Stream", CHAR)
                return ("Stream", t) if t != UNIT_T else UNIT_T
            return ANY
        if k == "addr":                                               # $ : 常に Address(参照先の型を運ぶ)。$__ だけは Unit
            if n[1] == ("id", "__"): return UNIT_T
            if n[1][0] == "id" and n[1][1] in self.resolving and n[1][1] not in sc.vars and self.defs.get(n[1][1], ("lam",))[0] != "lam":
                return ("Addr", ANY)                         # R73: `$v` は v をその場で評価しないので、v を解いている途中の輪の辺ではない
            self.lift_depth = getattr(self, "lift_depth", 0) + 1                  # R103: 持ち上げの中身を解く途中で戻る輪は、持ち上げを通る輪で値の輪ではない
            try: t = self.fin(self.type_of(n[1], sc))
            finally: self.lift_depth -= 1
            return UNIT_T if t == UNIT_T else ("Addr", t)
        if k == "input":                                              # 前置 @ : 参照先の圏を継承。番地そのものなら Reader
            t = self.fin(self.type_of(n[1], sc))
            if is_addr_of(t): return t[1]
            if t == ADDR: return ("Reader", ANY)
            return UNIT_T if t == UNIT_T else ANY
        if k == "struct": return ("Struct", tuple((key, self.fin(self.type_of(v, sc))) for key, v in n[1]))
        if k == "sec":
            _, kind, op, a, comma = n
            if kind in ("not", "fact"): return Fn(None, (ANY,), (), UNIT_T if kind == "not" else INT)
            if kind == "fold": return Fn(None, (), (), ANY, True, ("fold", op))
            if kind in ("neg", "bnot"): return Fn(None, (ANY,), (), ANY)
            operand = self.type_of(a, sc)
            if comma: return Fn(None, (), (), ANY, True, ("map", op, kind, operand))
            ret = self.bin_type(op, ANY, operand) if kind == "right" else self.bin_type(op, operand, ANY)
            return Fn(None, (ANY,), (), ret)
        if k == "importspread": return UNIT_T
        return ANY

    # --- 出力 ---
    # --- R73・R80: 値の定義を含む輪(name-cycle)を、解く順に依らず依存の辺から見る。`$名前` の辺は輪を閉じない(R73) ---
    def refs_of(self, n, out, opened=False):
        if isinstance(n, list):
            for c in n: self.refs_of(c, out, opened)
            return
        if not isinstance(n, tuple) or not n: return
        k = n[0]
        if k == "id": out.add(n[1]); return
        if k == "addr":
            if n[1][0] == "id" and opened: out.add(n[1][1])  # `@[$v]`・`$v ' 0` のように中を開く辺は、v の値に依る(R73 の今のまま断る組)
            return                                           # R103: 持ち上げは中身を評価しないので、中の名前は辺にならない
        if k == "input": self.refs_of(n[1], out, True); return
        if k == "bin" and n[1] == "'":
            self.refs_of(n[2], out, True)
            if n[3][0] != "id": self.refs_of(n[3], out)
            return
        if k == "lam":
            inner = set(); self.refs_of(n[2], inner); self.refs_of([sp[2] for sp in n[1] if sp[0] == "name" and sp[2] is not None], inner)
            for sp in n[1]:
                inner -= {sp[1]} if sp[0] == "name" else set(sp[1]) | set(sp[4] if len(sp) > 4 else []) | ({sp[2]} if sp[2] else set())
            out |= inner; return
        for c in n[1:]: self.refs_of(c, out, opened and k in ("block", "seq"))

    def local_rows(self, lam):
        """R80: 枝の無い関数の本体の `名前 : 右辺` の行 → ([(名前, 右辺)], 残りの行)。枝のある本体・同名・外の名前と同じ名前は None"""
        body = lam[2]
        if body[0] != "cases": return None
        names = [c[1] for c, _ in body[1] if c is not None and c[0] == "id"]
        if not names or any(c is not None and c[0] != "id" for c, _ in body[1]) or len(set(names)) != len(names): return None
        params = {sp[1] for sp in lam[1] if sp[0] == "name"}
        for sp in lam[1]:
            if sp[0] != "name": params |= set(sp[1]) | set(sp[4] if len(sp) > 4 else []) | ({sp[2]} if sp[2] else set())
        if any(nm in params or nm in self.defs or nm in self.imported for nm in names): return None
        return [(c[1], v) for c, v in body[1] if c is not None], [v for c, v in body[1] if c is None]

    def scc_cycles(self, graph, rhs_of):
        index, low, stack, on, out, counter = {}, {}, [], set(), [], [0]
        def strong(v):
            index[v] = low[v] = counter[0]; counter[0] += 1; stack.append(v); on.add(v)
            for w in graph[v]:
                if w not in index: strong(w); low[v] = min(low[v], low[w])
                elif w in on: low[v] = min(low[v], index[w])
            if low[v] == index[v]:
                comp = []
                while True:
                    w = stack.pop(); on.discard(w); comp.append(w)
                    if w == v: break
                if len(comp) > 1 or v in graph[v]: out.append(comp)
        for v in graph:
            if v not in index: strong(v)
        return [c for c in out if any(rhs_of[m][0] != "lam" for m in c)]

    def cycle_pass(self):
        def graph_of(rhs_of):
            g = {}
            for nm, rhs in rhs_of.items():
                o = set(); self.refs_of(rhs, o); g[nm] = {x for x in o if x in rhs_of}
            return g
        for comp in self.scc_cycles(graph_of(self.defs), self.defs):
            self.where = comp[0]; self.note("name-cycle", f"{', '.join(sorted(comp))} の定義が自分自身へ戻る輪に値の定義を含む(種類が決まらない)")
        def all_refs(n, out):                     # 持ち上げの中も数える
            if isinstance(n, list):
                for c in n: all_refs(c, out)
            elif isinstance(n, tuple) and n:
                if n[0] == "id": out.add(n[1])
                else:
                    for c in n[1:]: all_refs(c, out)
        def lowers(n, carriers, found):           # 持ち上げの外の `@X`・`X ' i` で、X が輪へ届く名前を運びうるか(R103 の綴りの近似)
            if isinstance(n, list):
                for c in n: lowers(c, carriers, found)
            elif isinstance(n, tuple) and n:
                if n[0] == "addr": return
                x = n[1] if n[0] == "input" else (n[2] if n[0] == "bin" and n[1] == "'" else None)
                if x is not None:
                    r = set(); all_refs(x, r)
                    if r & carriers: found.append(1)
                if n[0] == "seq" and n[1] and n[1][0][0] == "id" and n[1][0][1] in self.defs and self.defs[n[1][0][1]][0] == "lam":
                    g = self.defs[n[1][0][1]]; ps = {sp[1] for sp in g[1] if sp[0] == "name"}
                    inner = []; lowers(g[2], ps, inner)
                    if inner:
                        for a in n[1][1:]:
                            r = set(); all_refs(a, r)
                            if r & carriers: found.append(1)
                for c in n[1:]: lowers(c, carriers, found)
        full = {}
        for nm, rhs in self.defs.items():
            o = set(); all_refs(rhs, o); full[nm] = {x for x in o if x in self.defs}
        real = {frozenset(c) for c in self.scc_cycles(graph_of(self.defs), self.defs)}
        for comp in self.scc_cycles(full, self.defs):
            if frozenset(comp) in real: continue
            carriers = set(comp); found = []
            for m in comp:
                rhs = self.defs[m]
                if rhs[0] == "lam":
                    ps = {sp[1] for sp in rhs[1] if sp[0] == "name"}; lowers(rhs[2], carriers | ps, found)
                else: lowers(rhs, carriers, found)
            if found:
                self.where = comp[0]; self.note("name-cycle", f"{', '.join(sorted(comp))} の輪が、定義の時に持ち上げを下ろす所(`@`・`' i`)を通ります(R103)")
        def walk(n):
            if isinstance(n, list):
                for c in n: walk(c)
            elif isinstance(n, tuple) and n:
                if n[0] == "lam" and len(n) == 3:
                    lr = self.local_rows(n)
                    if lr:
                        rhs_of = dict(lr[0])
                        for comp in self.scc_cycles(graph_of(rhs_of), rhs_of):
                            self.note("name-cycle", f"局所の定義 {', '.join(sorted(comp))} の輪に値の定義を含む(R80)")
                for c in n: walk(c)
        walk(self.nodes)
        return self

    # --- R81: 素の関数(括りの仮引数の無い関数)の定義の行は印の無い1回の読み。仮引数の `@p` から出る門は定義の行で断る。
    #          自分の仮引数の `$` を渡す再帰は印が段ごとに深くなるので実体の守りで断る ---
    def plain_lams(self):
        for nm, rhs in self.defs.items():
            if rhs[0] == "lam" and all(sp[0] == "name" for sp in rhs[1]): yield nm, rhs, {sp[1] for sp in rhs[1]}

    def only_plain_calls(self, nm, idx):
        """名前 nm の呼び出しが 1 つ以上あり、どの出方も `nm 実引数…` の頭で、idx 番目の実引数が関数でない字面(数・文字列・文字)だけなら True(呼び出しを見るまで知らせを重くしない)。"""
        heads, total, ok = [0], [0], [True]
        def walk(n):
            if isinstance(n, list):
                for c in n: walk(c)
                return
            if not isinstance(n, tuple) or not n: return
            if n[0] == "id" and len(n) > 1 and n[1] == nm: total[0] += 1
            if n[0] == "def" and n[1] == nm: return
            if n[0] == "seq" and n[1] and n[1][0] == ("id", nm):
                heads[0] += 1; total[0] += 0
                args = n[1][1:]
                if idx >= len(args) or args[idx][0] != "lit" or not isinstance(args[idx][1], (int, float, str)) or isinstance(args[idx][1], bool): ok[0] = False
            for c in n[1:]: walk(c)
        walk(self.nodes)
        return ok[0] and heads[0] >= 1 and total[0] == heads[0]

    def plain_pass(self):
        def is_in(m, P): return m[0] == "input" and m[1][0] == "id" and m[1][1] in P
        for nm, rhs, P in self.plain_lams():
            def walk(n):
                if isinstance(n, list):
                    for c in n: walk(c)
                    return
                if not isinstance(n, tuple) or not n: return
                if n[0] == "lam": return
                if n[0] == "seq":
                    items = n[1]
                    for i, m in enumerate(items):
                        if is_in(m, P) and i == 0 and any(x[0] == "post" and x[1] == "~" for x in items[1:]):
                            self.where = nm; self.note("unknown-input", f"G19: {nm} の定義の行で、仮引数 {m[1][1]} の前置 @ に流れ(x~)を当てています。印の無い読みでは先の種類が分かりません(R81・Q45)")
                        # R126: G6 は廃止(先の分からない `y @p` は種類の未知な項として値の段が畳む)。ここでは知らせない
                        elif m[0] == "sec" and m[1] == "mapf" and m[3] is not None and m[3][0] == "block" and is_in(m[3][1], P) and i + 1 < len(items):
                            pn = m[3][1][1][1]
                            if self.only_plain_calls(nm, [sp[1] for sp in rhs[1]].index(pn)):
                                self.where = nm; self.note("unknown-input-called", f"G7: {nm} の定義の行で、`[@{pn},]` の写像の先は分かりませんが、{nm} の呼び出しは仮引数 {pn} に関数でない字面(数・文字列)だけを渡すので、--strict の実行は断りません(R50「ほかは未知」)")
                            else:
                                self.where = nm; self.note("unknown-input", f"G7: {nm} の定義の行で、`[@{pn},]` の写像の先が分かりません(R81)")
                for c in n[1:]: walk(c)
            walk(rhs[2])
        return self

    # --- R64: 括りの口は残りの行を丸ごと List で受け、名前より多い要素は受けない。書いた時点で数が分かる形は information の bracket-excess ---
    def leftover_operand(self, t, op):          # R87: 値の演算子の被演算子に丸ごと残った関数は評価する所で _(恒等射は黙る)
        ft = self.fin(t)
        if STRICT_R91 and is_fn(ft) and needs_more(ft):
            self.note("leftover-lambda", f"値の演算子 {op} の被演算子に関数{(' ' + ft.name + ' ') if ft.name else ''}が丸ごと残り、_ になって消えます。関数を値として置くなら `$` を付けます(R87)")
            return MARK_T
        return t

    def known_len(self, m):                    # R91: 書いた時点で長さが分かる実引数(行・字面・括った物・積・値名・数)
        if not isinstance(m, tuple) or not m: return False
        if m[0] == "lit": return True
        if m[0] == "block": return m[1][0] in ("seq", "prod", "lit")
        if m[0] == "prod": return True
        if m[0] == "seq": return all(i[0] == "lit" for i in m[1]) and len(m[1]) >= 1
        if m[0] == "id" and m[1] in self.defs and self.defs[m[1]][0] not in ("lam", "struct"): return self.known_len(self.defs[m[1]])
        return False

    def addr_used(self, n, name):
        if isinstance(n, list): return any(self.addr_used(c, name) for c in n)
        if isinstance(n, tuple) and n:
            if n[0] == "addr" and isinstance(n[1], tuple) and n[1][:2] == ("id", name): return True
            return any(self.addr_used(c, name) for c in n[1:])
        return False

    def elem_count(self, m, depth=0):
        if depth > 4 or not isinstance(m, tuple) or not m: return None
        k = m[0]
        if k == "lit" and isinstance(m[1], str): return len(m[1])
        if k == "block":
            x = m[1]
            if x[0] == "seq": return len([i for i in x[1] if i != ("hole",)])
            if x[0] == "prod": return len([i for i in x[1] if i != ("hole",)])
            if x[0] in ("lit", "id", "block") and x[0] != "id": return 1
            return None
        if k == "prod": return len([i for i in m[1] if i != ("hole",)])
        if k == "seq" and len(m[1]) >= 2 and all(i[0] == "lit" for i in m[1]): return len(m[1])
        if k == "post" and m[1] == "~": return self.elem_count(m[2], depth + 1)
        if k == "id" and m[1] in self.defs and self.defs[m[1]][0] not in ("lam", "struct"): return self.elem_count(self.defs[m[1]], depth + 1)
        return None

    def empty_node(self, n, depth=0):
        """長さ 0 と分かる項(`[]`・`[[]]`・書いた `_`・それを右辺に持つ名前)(R84)"""
        if depth > 6: return False
        k = n[0]
        if k == "hole": return True
        if k == "lit": return isinstance(n[1], list) and not n[1]
        if k == "block": return self.empty_node(n[1], depth + 1)
        if k == "id" and n[1] in self.defs and self.defs[n[1]][0] not in ("lam", "struct"): return self.empty_node(self.defs[n[1]], depth + 1)
        return False
    def empties_to_holes(self, items):
        return [("hole",) if (m[0] == "post" and m[1] == "~" and self.empty_node(m[2])) else m for m in items]

    def excess_pass(self):
        brk = {nm: rhs[1] for nm, rhs in self.defs.items() if rhs[0] == "lam" and any(sp[0] == "destr" for sp in rhs[1])}
        def expand(items, pre_ids):
            out = []
            for m in items:
                if m[0] == "block" and m[1][0] == "seq" and m[1][1] and m[1][1][0][0] == "id" and m[1][1][0][1] in brk: out += list(m[1][1]); pre_ids.update(id(x) for x in m[1][1])
                elif m[0] == "id" and m[1] in self.defs and self.defs[m[1]][0] == "seq" and self.defs[m[1]][1][0][0] == "id" and self.defs[m[1]][1][0][1] in brk: out += list(self.defs[m[1]][1]); pre_ids.update(id(x) for x in self.defs[m[1]][1])
                else: out.append(m)
            return out
        def check(items, extra, where):
            pre_ids = set(); items = expand(items, pre_ids)
            for j, m in enumerate(items):
                if m[0] != "id" or m[1] not in brk: continue
                params = brk[m[1]]; args = [a for a in items[j + 1:] if a != ("hole",)] + [a for a in extra if a != ("hole",)]
                pos = 0
                for i, sp in enumerate(params):
                    if pos >= len(args): break
                    if sp[0] == "name": pos += 1; continue
                    k = len(sp[1]) + len(sp[4] if len(sp) > 4 else [])
                    if sp[2]: pos += 1; continue                       # ~rest があれば余りも受ける
                    if i == len(params) - 1:
                        nit = len([a for a in items[j + 1:] if a != ("hole",)])
                        rest = args[pos:nit] if extra else args[pos:]          # R93: `,` の左の2項以上は1つの要素(`fab 1 2 , 3` の `1 2`)
                        if extra:
                            c = (1 if rest else 0) + len([a for a in extra if a != ("hole",)])
                            if c > k: self.where = where; self.note("bracket-excess", f"{m[1]} の括りの仮引数 [{' '.join(sp[1])}] は {k} 個までで、{c} 個渡しています。余りは受けません(積み直しません)。残りが欲しければ `[a b ~c]` と書きます(R64)")
                            break
                        if any(a[0] == "post" and a[1] == "~" for a in rest) and len(rest) > 1: break    # 流れと書いた実引数の混ざった形は数えない(Q29)
                        c = len(rest) if len(rest) > 1 else (self.elem_count(rest[0]) if self.elem_count(rest[0]) is not None else 1)
                    else:
                        c = self.elem_count(args[pos]); pos += 1
                    if STRICT_R91 and c is not None and c < len(sp[1]) and not (len(sp) > 4 and sp[4]):
                        known = (i == len(params) - 1 and (len(rest) > 1 or self.known_len(rest[0]))) if i == len(params) - 1 else self.known_len(args[pos - 1])
                        miss = [n for n in sp[1][c:] if self.addr_used(self.defs[m[1]][2], n)]
                        if known and miss:
                            self.where = where
                            self.note("bracket-short", f"G7: {m[1]} の括りの仮引数 [{' '.join(sp[1])}] に {c} 個しか渡していません(書いた時点で長さが分かる並び)。足りない {' '.join(miss)} は `_` で、`$` で番地を取れません(R91)。{len(sp[1])} 個そろえて渡します")
                    if c is not None and c > k and not (args[pos - 1 if i != len(params) - 1 else pos] is not None and id(args[pos - 1 if i != len(params) - 1 else pos]) in pre_ids):
                        self.where = where
                        self.note("bracket-excess", f"{m[1]} の括りの仮引数 [{' '.join(sp[1])}] は {k} 個までで、{c} 個渡しています。余りは受けません(積み直しません)。残りが欲しければ `[a b ~c]` と書きます(R64)")
                    if i == len(params) - 1: break
        def walk(n, where):
            if isinstance(n, list):
                for c in n: walk(c, where)
            elif isinstance(n, tuple) and n:
                if n[0] == "def" and len(n) == 3 and isinstance(n[1], str): where = n[1]
                if n[0] == "seq": check(n[1], [], where)
                for c in n[1:]: walk(c, where)
        walk(self.nodes, "")
        return self.empty_pass().addr_pass().width_pass().g2_pass()

    def written_empty(self, n, depth=0):         # R85: 書いた `[]`(`e0 : []` の e0・`[[]]`・`~[]`・括った物)。空の文字列は含まない
        if depth > 5 or not isinstance(n, tuple) or not n: return False
        k = n[0]
        if k == "lit": return isinstance(n[1], list) and not n[1]
        if k == "block": return not isinstance(n[1], list) and self.written_empty(n[1], depth + 1)
        if k == "seq" and len(n[1]) == 1: return self.written_empty(n[1][0], depth + 1)
        if k == "lift": return n[1] != ("hole",) and self.written_empty(n[1], depth + 1)
        if k == "id" and n[1] in self.defs and self.defs[n[1]][0] not in ("lam", "struct"): return self.written_empty(self.defs[n[1]], depth + 1)
        return False

    def empty_pass(self):                        # R85: 書いた `[]` が値の口(素の関数の裸の仮引数)に来たら G5
        def walk(n, where):
            if isinstance(n, list):
                for c in n: walk(c, where)
            elif isinstance(n, tuple) and n:
                if n[0] == "def" and len(n) == 3 and isinstance(n[1], str): where = n[1]
                if n[0] == "seq" and n[1] and n[1][0][0] == "id" and n[1][0][1] in self.defs and self.defs[n[1][0][1]][0] == "lam":
                    items = n[1]; lam = self.defs[items[0][1]]; params = lam[1]
                    plain = all(sp[0] in ("name", "destr") for sp in params) and not any(sp[0] == "name" and sp[2] is not None for sp in params)
                    fnarg = any(a[0] == "id" and a[1] in self.defs and self.defs[a[1]][0] == "lam" for a in items[1:])
                    if plain and not fnarg and not any(a == ("hole",) for a in items[1:]):
                        for k, a in enumerate(items[1:]):
                            if k >= len(params): break
                            if params[k][0] == "name" and self.written_empty(a):
                                self.where = where
                                self.note("empty-in-value-mouth", f"G5: {items[0][1]} の値の口に書いた `[]` を置いています。`[] = _` なら穴、裸の仮引数にリストが来たら断る裁定なら型の誤り、と読みが割れます。穴のつもりなら `_` か `!_` と書きます(R85)")
                for c in n[1:]: walk(c, where)
        walk(self.nodes, "")
        return self

    def hex_sum(self, n, depth=0):               # R62: `0x… ± 0x…`(括り・名前を通して)
        if depth > 6 or not isinstance(n, tuple) or not n: return False
        if n[0] == "block" and not isinstance(n[1], list): return self.hex_sum(n[1], depth + 1)
        if n[0] == "seq" and len(n[1]) == 1: return self.hex_sum(n[1][0], depth + 1)
        if n[0] == "id" and n[1] in self.defs and self.defs[n[1]][0] not in ("lam", "struct"): return self.hex_sum(self.defs[n[1]], depth + 1)
        return n[0] == "bin" and n[1] in ("+", "-") and self.addr_face(n) == "hex"

    def addr_face(self, n, depth=0):             # R62・R92: 書いた式の番地の顔(pt 点・diff 差・hex `0x…`・int 十進の整数)。分からなければ None
        if depth > 6 or not isinstance(n, tuple) or not n: return None
        k = n[0]
        if k == "addr":
            x = n[1]
            if x[0] == "id" and not (x[1] in self.defs and self.defs[x[1]][0] == "lam"): return "pt"
            return None
        if k == "lit":
            if len(n) > 2 and n[2] == "Address": return "hex"
            return "int" if isinstance(n[1], int) and not isinstance(n[1], bool) else None
        if k == "block" and not isinstance(n[1], list): return self.addr_face(n[1], depth + 1)
        if k == "seq" and len(n[1]) == 1: return self.addr_face(n[1][0], depth + 1)
        if k == "id" and n[1] in self.defs and self.defs[n[1]][0] not in ("lam", "struct"):
            f = self.addr_face(self.defs[n[1]], depth + 1)
            return f if f in ("pt", "diff", "hex") else None
        if k == "bin" and n[1] in ("+", "-"):
            a, b = self.addr_face(n[2], depth + 1), self.addr_face(n[3], depth + 1)
            return ADDR_PAIR.get((n[1], a, b))
        return None

    def int_tree(self, n, depth=0):              # R99・R62: Int と書いた所から分かる木(数の字面・Int どうしの演算・Int を並べた List。名前と括り1つも)
        if depth > 8 or not isinstance(n, tuple) or not n: return False
        k = n[0]
        if k == "lit": return len(n) == 2 and type(n[1]) is int
        if k == "block" and not isinstance(n[1], list): return self.int_tree(n[1], depth + 1)
        if k == "seq" and len(n[1]) == 1: return self.int_tree(n[1][0], depth + 1)
        if k == "bin" and n[1] in ("+", "-", "*", "/", "%", "^", "<<", ">>", "||", ";;", "&&"): return self.int_tree(n[2], depth + 1) and self.int_tree(n[3], depth + 1)
        if k == "neg": return self.int_tree(n[1], depth + 1)
        if k == "prod": return bool(n[1]) and all(self.int_tree(x, depth + 1) for x in n[1])
        if k == "id" and n[1] in self.defs and self.defs[n[1]][0] not in ("lam", "struct"): return self.int_tree(self.defs[n[1]], depth + 1)
        return False

    def hex_value(self, n, depth=0):             # R99・R62: `0x…` の字面とその + - の畳み込み。決まらなければ None
        if depth > 6 or not isinstance(n, tuple) or not n: return None
        if n[0] == "lit": return n[1] if len(n) > 2 and n[2] == "Address" else None
        if n[0] == "block" and not isinstance(n[1], list): return self.hex_value(n[1], depth + 1)
        if n[0] == "seq" and len(n[1]) == 1: return self.hex_value(n[1][0], depth + 1)
        if n[0] == "id" and n[1] in self.defs and self.defs[n[1]][0] not in ("lam", "struct"): return self.hex_value(self.defs[n[1]], depth + 1)
        if n[0] == "bin" and n[1] in ("+", "-"):
            a, b = self.hex_value(n[2], depth + 1), self.hex_value(n[3], depth + 1)
            return None if a is None or b is None else (a + b if n[1] == "+" else a - b)
        return None

    def hex_lits(self, n, depth=0):              # R99・R62: 差の字面の1つ1つ(`0x4 + 0x7` は [4, 7])。名前は右辺の字面を辿る
        if depth > 6 or not isinstance(n, tuple) or not n: return []
        if n[0] == "lit": return [n[1]] if len(n) > 2 and n[2] == "Address" else []
        if n[0] == "block" and not isinstance(n[1], list): return self.hex_lits(n[1], depth + 1)
        if n[0] == "seq" and len(n[1]) == 1: return self.hex_lits(n[1][0], depth + 1)
        if n[0] == "id" and n[1] in self.defs and self.defs[n[1]][0] not in ("lam", "struct"): return self.hex_lits(self.defs[n[1]], depth + 1)
        if n[0] == "bin" and n[1] in ("+", "-"): return self.hex_lits(n[2], depth + 1) + self.hex_lits(n[3], depth + 1)
        return []

    def width_pass(self):                        # R99・R62: 要素の幅が 8 byte と分かる点に、幅の倍数でない差を足し引きする形は G21
        def pt_int(n):
            while n[0] == "block" and not isinstance(n[1], list) or (n[0] == "seq" and len(n[1]) == 1): n = n[1] if n[0] == "block" else n[1][0]
            if n[0] == "addr":
                x = n[1]
                if x[0] == "id": return x[1] in self.defs and self.defs[x[1]][0] not in ("lam", "struct") and self.int_tree(self.defs[x[1]])
                return self.int_tree(x)
            if n[0] == "id" and n[1] in self.defs and self.defs[n[1]][0] not in ("lam", "struct"): return pt_int(self.defs[n[1]])
            if n[0] == "bin" and n[1] in ("+", "-"): return pt_int(n[2]) if self.addr_face(n[2]) == "pt" else (pt_int(n[3]) if self.addr_face(n[3]) == "pt" else False)
            return False
        def walk(n, where):
            if isinstance(n, list):
                for c in n: walk(c, where)
            elif isinstance(n, tuple) and n:
                if n[0] == "def" and len(n) == 3 and isinstance(n[1], str): where = n[1]
                if n[0] == "bin" and n[1] in ("+", "-"):
                    for pn, hn in ((n[2], n[3]), (n[3], n[2])):
                        if (hn is n[3] or n[1] == "+") and self.addr_face(pn) == "pt" and self.addr_face(hn) == "hex" and pt_int(pn):
                            v = self.hex_value(hn)
                            lits = [abs(x) for x in self.hex_lits(hn)]
                            if v is not None and v % 8 == 0 and len(lits) > 1 and any(x % 8 for x in lits):
                                self.where = where
                                self.note("address-width", f"G21: 要素の幅が 8 byte(Int の語)と分かる番地の点に足し引きする `0x…` の和の字面のどれかが幅の倍数ではありません(値 0x{abs(v):X} は倍数。字面ごとに見るか値で見るかは決まっていません。§5 Q77)")
                                break
                            if v is not None and v % 8 != 0:
                                self.where = where
                                self.note("address-width", f"G21: 要素の幅が 8 byte(Int の語)と分かる番地の点に、幅の倍数でない差(値 0x{abs(v):X})を足し引きしています(R99・R62)")
                                break
                for c in n[1:]: walk(c, where)
        walk(self.nodes, "")
        return self

    def addr_pass(self):                         # R92: 番地の対表(点・差・`0x…`)。表に無い組は G21
        ok_cmp = {("pt", "pt"), ("diff", "diff"), ("pt", "hex"), ("hex", "pt")}
        def judge(op, a, b, where):
            if a is None or b is None or "pt" not in (a, b) and "diff" not in (a, b): return
            if op in ("+", "-", "/"):
                if (op, a, b) in ADDR_PAIR: return
            elif (a, b) in ok_cmp: return
            self.where = where
            if "int" in (a, b): self.note("address-pair", f"G21: Address と Int は混ぜない。ずらしは `0x…` で書く(`$x + 1` → `$x + 0x1`。R62)")
            else: self.note("address-pair", f"G21: 番地の組が決まっていません(`{op}`、左は {ADDR_NAME[a]}、右は {ADDR_NAME[b]}。点 + 点・差 ± 点・`0x…` − 点など。R92 の表: 点 ± 差/`0x…`、差/`0x…` + 点、差 ± `0x…`、`0x…` + 差、点 − 点)")
        def walk(n, where):
            if isinstance(n, list):
                for c in n: walk(c, where)
            elif isinstance(n, tuple) and n:
                if n[0] == "def" and len(n) == 3 and isinstance(n[1], str): where = n[1]
                if n[0] == "bin" and n[1] in ("+", "-", "/", "<", "<=", "=", "==", ">=", ">", "!=", "!=="):
                    fa, fb = self.addr_face(n[2]), self.addr_face(n[3])
                    if n[1] not in ("+", "-", "/"):                         # R62: 比べの相手の `0x…` どうしの和は字面と読まない
                        fa = "sum" if fa == "hex" and self.hex_sum(n[2]) else fa; fb = "sum" if fb == "hex" and self.hex_sum(n[3]) else fb
                    judge(n[1], fa, fb, where)
                elif n[0] == "cmp" and len(n[2]) == 1:
                    fa, fb = self.addr_face(n[1][0]), self.addr_face(n[1][1])
                    fa = "sum" if fa == "hex" and self.hex_sum(n[1][0]) else fa; fb = "sum" if fb == "hex" and self.hex_sum(n[1][1]) else fb
                    judge(n[2][0], fa, fb, where)
                for c in n[1:]: walk(c, where)
        walk(self.nodes, "")
        return self

    def zero_known(self, n, depth=0):            # R63・R91: 書いた時点で `_` と分かる値(`un`・`[_]`・`~_`)。`_` そのものは含めない
        if depth > 5 or not isinstance(n, tuple) or not n or n == ("hole",): return False
        k = n[0]
        if k == "lift": return n[1] == ("hole",)
        if k == "block" and not isinstance(n[1], list): return n[1] == ("hole",) or self.zero_known(n[1], depth + 1)
        if k == "seq" and len(n[1]) == 1: return self.zero_known(n[1][0], depth + 1)
        if k == "id" and n[1] in self.defs and self.defs[n[1]][0] not in ("lam", "struct"):
            d = self.defs[n[1]]
            return d == ("hole",) or self.zero_known(d, depth + 1)
        return False

    def g2_pass(self):                           # R90 残り: `[~xs]` に `_` と分かる値が来たら xs~ の数は数えられず、後ろに項が続けば G2(a)
        def stream_then_term(n, rest):
            if isinstance(n, list): return any(stream_then_term(c, rest) for c in n)
            if isinstance(n, tuple) and n:
                if n[0] == "seq":
                    for k, m in enumerate(n[1]):
                        if m[0] == "post" and m[1] == "~" and m[2] == ("id", rest) and any(x != ("hole",) for x in n[1][k + 1:]): return True
                if n[0] == "lam": return False
                return any(stream_then_term(c, rest) for c in n[1:])
            return False
        def walk(n, where):
            if isinstance(n, list):
                for c in n: walk(c, where)
            elif isinstance(n, tuple) and n:
                if n[0] == "def" and len(n) == 3 and isinstance(n[1], str): where = n[1]
                if n[0] == "seq" and n[1] and n[1][0][0] == "id" and n[1][0][1] in self.defs and self.defs[n[1][0][1]][0] == "lam":
                    lam = self.defs[n[1][0][1]]
                    for k, a in enumerate(n[1][1:]):
                        if k >= len(lam[1]): break
                        sp = lam[1][k]
                        if sp[0] == "destr" and not sp[1] and sp[2] and not (len(sp) > 4 and sp[4]) and self.zero_known(a) and stream_then_term(lam[2], sp[2]):
                            self.where = where
                            self.note("uncountable-stream", f"G2(a): {n[1][0][1]} の `[~{sp[2]}]` に `_` と分かる値が来て、撒いた流れ `{sp[2]}~` の数が数えられず、後ろの項を当てるのか積むのかが決まりません(R90、§5 Q75 (e))。後ろの項を括って `(…)` にするか、流れを最後に置きます")
                for c in n[1:]: walk(c, where)
        walk(self.nodes, "")
        return self

    def nest_pass(self):
        funcs = {nm: rhs for nm, rhs in self.defs.items() if rhs[0] == "lam"}
        g = {}
        for nm, rhs in funcs.items():
            o = set(); self.refs_of(rhs[2], o); g[nm] = {x for x in o if x in funcs}
        reach = {nm: self.reach_of(g, nm) for nm in funcs}
        for nm, rhs, P in self.plain_lams():
            def mentions(n):
                if isinstance(n, list): return any(mentions(c) for c in n)
                if isinstance(n, tuple) and n:
                    if n[0] == "id": return n[1] in P
                    return any(mentions(c) for c in n[1:])
                return False
            def has_deep(n):
                if isinstance(n, list): return any(has_deep(c) for c in n)
                if isinstance(n, tuple) and n:
                    if n[0] == "addr" and mentions(n[1]): return True
                    return any(has_deep(c) for c in n[1:])
                return False
            def walk(n):
                if isinstance(n, list):
                    for c in n: walk(c)
                elif isinstance(n, tuple) and n:
                    if n[0] == "seq" and n[1] and n[1][0][0] == "id" and n[1][0][1] in funcs and nm in reach.get(n[1][0][1], set()) | {n[1][0][1]} \
                            and (n[1][0][1] == nm or nm in reach[n[1][0][1]]) and has_deep(n[1][1:]):
                        self.where = nm; self.note("instance-nest-limit", f"{nm} が自分の仮引数の `$` を渡して自分へ戻る再帰で、印が段ごとに深くなります(実体の守り、R81)")
                    for c in n[1:]: walk(c)
            walk(rhs[2])
        return self

    def reach_of(self, g, a):
        seen, st = set(), [a]
        while st:
            x = st.pop()
            for y in g.get(x, ()):
                if y not in seen: seen.add(y); st.append(y)
        return seen

    def errors(self): return [d for d in self.diags if d[0] in ERROR_KINDS]

    # --- G16: 本体の根が裸の関数の `?` は断る(coproduct_spec.md R125)。種類 A / L / U を綴りと定義から見る ---
    # 種類は (文字, 口の数, 返す種類の遅延) 。L の口の数は None なら可変長。括りの関数(括り仮引数)は実体の根で見るので、ここでは対象外。
    HOLE_NODE = ("not", ("hole",))

    def bare_function_return(self):
        A, U = ("A", 0, None), ("U", 0, None)
        L = lambda n, ret: ("L", n, ret)
        body_cache, def_cache, busy = {}, {}, set()

        def body_kind(lam):
            key = id(lam)
            if key in body_cache: return body_cache[key]
            if key in busy: return "A"                       # 再帰は A と仮置き(仮置きの上では断らない、R125)
            busy.add(key)
            try:
                sc = {sp[1]: U for sp in lam[1] if sp[0] == "name"}
                for sp in lam[1]:
                    if sp[0] != "name":
                        for n in list(sp[1]) + list(sp[4] if len(sp) > 4 else []) + ([sp[2]] if sp[2] else []): sc[n] = U
                body = lam[2]
                lr = self.local_rows(lam) if body[0] == "cases" else None
                if lr:                                       # R80: 局所の定義を除いた行が1つだけなら、その行が本体の返す所(1行の本体の根と同じ)
                    for nm, rhs in lr[0]: sc[nm] = node_kind(rhs, sc)
                    r = node_kind(lr[1][0], sc)[0] if len(lr[1]) == 1 else "A"
                else: r = "A" if body[0] == "cases" else node_kind(body, sc)[0]   # 字下げのブロックは根が L にならない(Q35)
            finally: busy.discard(key)
            body_cache[key] = r
            return r

        def lam_kind(lam): return L(len(lam[1]), lambda: body_kind(lam))

        def name_kind(name, sc):
            if name in sc: return sc[name]
            if name in self.defs:
                if name in def_cache: return def_cache[name]
                if name in busy: return A
                busy.add(name)
                try: def_cache[name] = node_kind(self.defs[name], {})
                finally: busy.discard(name)
                return def_cache[name]
            t = self.imported.get(name)
            if is_fn(t): return L(remaining(t), lambda: "U")
            return A                                         # 未定義の名前は値(R21)

        def field_kind(obj, key):                        # m ' say : 名前の欄の関数を引いた物は L(R26)
            d = self.defs.get(obj[1]) if obj[0] == "id" else None
            if d is not None and d[0] == "block" and d[1][0] == "def": d = ("struct", [(d[1][1], d[1][2])])    # [say : inc]
            if d is not None and d[0] == "struct":
                k = key[1] if key[0] in ("id", "lit") else None
                for fk, fnode in d[1]:
                    if fk == k: return node_kind(fnode, {})
            return U

        def node_kind(n, sc):
            k = n[0]
            if k == "lit": return A
            if k == "hole": return A
            if n == self.HOLE_NODE: return L(None, lambda: "A")      # 恒等射(R29)
            if k == "id": return name_kind(n[1], sc)
            if k == "lam": return lam_kind(n)
            if k == "sec": return L(None, lambda: "A")
            if k == "block": return node_kind(n[1], sc)
            if k == "seq": return fold(n[1], sc)
            if k == "input": return U
            if k == "post": return U if n[1] in ("~", "`") else A
            if k == "importspread": return U
            if k == "bin": return field_kind(n[2], n[3]) if n[1] == "'" else A
            return A

        def fold(items, sc):
            items = self.empties_to_holes(items)
            while len(items) > 1 and items[-1] == ("hole",): items = items[:-1]      # R138(2026-10-26): 末尾の書いた _ は消える印
            if len(items) == 1: return node_kind(items[0], sc)
            top = node_kind(items[0], sc)
            n_arg = top[1] if top[0] == "L" and isinstance(top[1], int) else None             # R89: 閉じた頭の後ろの口の外の `!_` と `_` は並びの単位(穴ではない)
            inner = lambda x: [k for k, y in enumerate(items[1:], 1) if y == x and (n_arg is None or k <= n_arg)]
            if top[0] == "L" and inner(self.HOLE_NODE): return L(None, lambda: "A")   # 穴の書き換え(`add !_ x`)
            if top[0] == "L" and [k for k in inner(("hole",)) if k < len(items) - 1]: return L(None, lambda: "A")      # 内側の _ は穴(R38)
            items = [x for x in items if x != ("hole",)]
            if len(items) == 1: return node_kind(items[0], sc)
            top = node_kind(items[0], sc)
            for x in items[1:]:
                kx = node_kind(x, sc)
                if top[0] == "U": continue
                if top[0] == "A":
                    if kx[0] == "L":                         # 逆適用: 口が1つ(か可変長)ならその口に入る。2つ以上なら行の終わりで _
                        top = (kx[2](), 0, None) if kx[1] in (1, None) else U
                        top = ("L", None, lambda: "A") if top[0] == "L" else top
                    else: top = A
                else:                                        # top は L
                    if kx[0] == "L":                         # 合成
                        top = L(top[1], lambda kx=kx: kx[2]() if kx[1] in (1, None) else "L")
                    elif top[1] is None: top = A             # 可変長は1つ受ければ閉じる
                    elif top[1] <= 1:
                        r = top[2]()
                        top = ("L", None, lambda: "A") if r == "L" else (r, 0, None)
                    else: top = L(top[1] - 1, top[2])
            return top

        def walk(n, sc, where):                              # 全部の `?` を見る
            if isinstance(n, tuple):
                if n and n[0] == "def" and len(n) == 3 and isinstance(n[1], str): where = n[1]
                if n and n[0] == "lam" and len(n) == 3:
                    plain = all(sp[0] == "name" for sp in n[1])
                    if plain and body_kind(n) == "L":
                        nested = n[2][0] == "lam"
                        self.where = where
                        self.note("bare-function-return",
                                  "G16: 本体の根が裸の関数です(呼ばれなくても断ります)。" +
                                  ("仮引数を並べて書きます(`x y ? x + y`。足りない適用は自動で部分適用になる)" if nested else
                                   "関数を返すなら $ を明示します(`$[+ m]`)。カリー化は仮引数を並べて書きます(`x y ? x + y`)"))
                    sc = {**sc, **{sp[1]: U for sp in n[1] if sp[0] == "name"}}
                for c in n: walk(c, sc, where)
            elif isinstance(n, list):
                for c in n: walk(c, sc, where)

        saved = self.where
        for node in self.nodes: walk(node, {}, "<top>")
        self.where = saved
        return self

    def render(self, t):
        t = t if not is_fn(t) else t
        if t == SCALAR: return "Scalar"
        return show_t(t)

    def signatures(self, only_exports=False):
        rows = []
        for name in self.order:
            if only_exports and name not in self.exports: continue
            t = self.def_type(name)
            if is_fn(t):
                ps = " ".join(self.render(p) for p in t.params[len(t.bound):]) or "_"      # 部分適用なら残りの仮引数だけ
                rows.append(f"{'#' if name in self.exports else ''}{name} : {ps} -> {self.render(self.fin(t.ret))}")
            else:
                rows.append(f"{'#' if name in self.exports else ''}{name} : {self.render(t)}")
        return rows


# ---------------------------------------------------------------- Pass 3.5: 形の解決(実体の帳簿)
class Shape(_Frozen):
    """実体(レイアウト)。型は「何ができるか」、形は「メモリにどう在るか」(type_system.md §2 / stack_abi.md)。
    kind: scalar | unit | elements(同一幅セルの並び)| rule(規則だけ)| struct | ref(場所)| fnobj | lambda | dynamic
    size: AArch64 での byte 数。実行時にしか決まらなければ None / slots: struct / fnobj: ((名前, オフセット, 大きさ), ...)  名前付きは名前順の正規順 / align: 境界(自然境界)"""
    __slots__ = _FIELDS = ("kind", "size", "desc", "slots", "align")
    def __init__(self, kind, size, desc="", slots=(), align=1):
        o = object.__setattr__
        o(self, "kind", kind); o(self, "size", size); o(self, "desc", desc); o(self, "slots", slots); o(self, "align", align)

CHARSET_WIDTH = {"ascii": 1, "utf32": 4}               # メモリ上の String の要素幅(option.ms の charset)
WIDTH = {INT: 8, UINT: 8, ADDR: 8, FLOAT: 8, VECTOR: 16, UNIT_T: 0, ID_T: 0}    # GPR / FPU / NEON(ISA の転記)
PTR = 8                                                 # AArch64 の番地

def align_up(n, a): return (n + a - 1) // a * a if a > 1 else n

class Shaper:
    def __init__(self, checker, charset="ascii"):
        self.c, self.cw, self.memo = checker, CHARSET_WIDTH[charset], {}

    def width(self, t):                                # 型のセル幅(byte)。決まらなければ None
        t = norm(t)
        if t == CHAR: return self.cw                   # レジスタでは GPR だが、記憶上は charset 幅
        return WIDTH.get(t)

    def ty(self, node):                                # 型を引く(帳簿・呼び出しサイトを汚さない)
        d, cs, sv = list(self.c.diags), {k: list(v) for k, v in self.c.callsites.items()}, self.c.where
        try: return self.c.fin(self.c.type_of(node, Scope()))
        finally: self.c.diags, self.c.callsites, self.c.where = d, cs, sv

    def scalar(self, t):
        w = self.width(t)
        if t in (UNIT_T, ID_T): return Shape("unit", 0, "場所を占めない")
        return Shape("scalar", w, f"{show_t(t)}", (), w) if w is not None else Shape("dynamic", None, f"{show_t(t)}(幅が決まらない)")

    def rule(self, t, fields):                         # 規則だけを持つ実体: 要素数に依らない固定サイズ
        w = self.width(t)
        if w is None: return Shape("dynamic", None, "規則の幅が決まらない")
        return Shape("rule", w * len(fields), "{" + ", ".join(fields) + "}", (), w)

    def elements(self, n, t):                          # 要素の並び: 同一幅セルの連続ブロック
        w = self.width(t)
        if w is None: return Shape("dynamic", None, f"{n} × {show_t(t)}(幅が決まらない)")
        return Shape("elements", n * w, f"{n} × {show_t(t)}" + (f"({self.cw})" if t == CHAR else ""), (), max(w, 1))

    def ref(self, t):                                  # 場所(Implicit): 型が語らない分だけ運ぶ。List・String は要素数も
        t = norm(t)
        if is_list(t) or t == STRING or is_stream(t): return Shape("ref", 2 * PTR, "{ptr, len}", (), PTR)
        return Shape("ref", PTR, "{ptr}", (), PTR)

    def carried(self, sh, t):
        """スロットや捕まえた値に置かれる「運ぶ姿」(stack_abi.md §4.6・§7.2): 中身ではなく、渡し方が決める。
        スカラー=値、規則=その3つ組、入力=番地、要素の並び=参照({ptr,len} か {ptr})。(大きさ, 境界)を返す。"""
        t = norm(t)
        if sh is not None and sh.kind == "rule": return sh.size, sh.align
        if sh is not None and sh.kind in ("unit",): return 0, 1
        if is_fn(t): return PTR, PTR                           # 関数ポインタ
        if is_struct(t): return PTR, PTR                       # Struct は形が型にあるので {ptr}
        if is_list(t) or t == STRING or is_stream(t): return 2 * PTR, PTR      # 要素数が型に無いので {ptr, len}
        if is_iter(t): return 2 * self.width(t[1]), self.width(t[1])           # {start, step}
        if is_addr_of(t) or (isinstance(t, tuple) and t[:1] == ("Reader",)): return PTR, PTR
        w = self.width(t)
        if w is None: return None, 1
        return w, max(w, 1)

    def layout(self, slots, order_by_name):
        """スロットを自然境界に置く。名前付きは名前でソートした正規順、連番は宣言順(並べ替えは一切しない)。
        slots: [(名前 or None, 大きさ, 境界)]。全体の大きさは最大の境界へ切り上げる。"""
        seq = sorted(slots, key=lambda x: x[0]) if order_by_name else list(slots)
        off, out, top = 0, [], 1
        for key, size, al in seq:
            if size is None: return None
            off = align_up(off, al); out.append((key, off, size)); off += size; top = max(top, al)
        return tuple(out), align_up(off, top), top

    def of_slots(self, slots):                         # slots: [(名前 or None, 形, 型)]
        named = all(k is not None for k, _, _ in slots) and bool(slots)
        forms = []
        for key, sh, t in slots:
            size, al = self.carried(sh, t)
            forms.append((key, size, al))
        res = self.layout(forms, named)
        if res is None: return Shape("dynamic", None, "Struct(スロットの大きさが決まらない)")
        out, total, top = res
        how = "名前順の正規配置" if named else "宣言順(連番スロット)"
        return Shape("struct", total, f"{len(out)} slots・{how}・境界 {top}", out, top)

    def fnobj(self, f):                                # 関数を返す関数が返す、関数オブジェクト {fn, 捕まえた値…}
        forms = [("fn", PTR, PTR)]
        for i, b in enumerate(f.bound):
            size, al = self.carried(None, b)
            forms.append((f"captured{i}", size, al))
        res = self.layout(forms, False)
        if res is None: return Shape("dynamic", None, "関数オブジェクト(捕まえた値の大きさが決まらない)")
        out, total, top = res
        return Shape("fnobj", total, f"{{fn, 捕まえた値 {len(f.bound)} 個}}・置き場は呼ぶ側", out, top)

    def of_def(self, name):
        if name in self.memo: return self.memo[name]
        self.memo[name] = Shape("dynamic", None, "循環")
        rhs = self.c.defs[name]
        self.memo[name] = Shape("lambda", None, "関数") if rhs[0] == "lam" else self.of(rhs)
        return self.memo[name]

    def of(self, n):
        k = n[0]
        if k in ("export",): return self.of(n[1])
        if k == "def": return self.of(n[2])
        if k == "block":
            if self.ty(n) == VECTOR: return self.scalar(VECTOR)          # [1.0 2.0 3.0 4.0] は1つの Q レジスタ
            return self.of(n[1])
        if k == "lam": return Shape("lambda", None, "関数")
        if k == "id":
            if n[1] in self.c.defs: return self.of_def(n[1])
            if n[1] in self.c.imported: return self.scalar(self.ty(n))
            return Shape("unit", 0, "未定義の識別子は __(場所を占めない)")
        t = self.ty(n)
        if is_fn(t): return Shape("lambda", None, "コンパイル時に特殊化した関数(実行時の実体は無い)")
        if k == "lit":
            if t == STRING:
                v = n[1]
                return self.elements(len(v), CHAR) if v else Shape("unit", 0, "空の文字列は __")
            return self.scalar(t)
        if k == "seq": return self.of_seq(n, t)
        if k == "prod": return self.of_prod(n, t)
        if k == "struct": return self.of_slots([(key, self.of(v), self.ty(v)) for key, v in n[1]])
        if k == "bin":
            op = n[1]
            if op == "~":
                lt = self.ty(n[2])
                if is_iter(lt) and is_list(t): return self.rule(lt[1], ("start", "step", "end"))     # 終端を与えた Iterator
                if is_list(t): return self.rule(t[1], ("start", "step", "end"))                      # 1 ~ 5 : 要素数に依らない
                if t == STRING: return Shape("rule", 2 * self.cw + 8, "{start, step, end}(端点は charset 幅、歩幅は Int)", (), 1)
            if op in ("~+", "~-", "~*", "~/", "~^") and is_iter(t): return self.rule(t[1], ("start", "step"))
            if op in ("'", "@"):
                key = n[3] if op == "'" else n[2]
                if key[0] == "post" and key[1] == "~": return self.ref(t if t != ANY else ("List", ANY))   # 切り出しは {ptr, len}
                return self.scalar(t)
        if k == "addr": return Shape("scalar", PTR, "Address", (), PTR) if not is_addr_of(t) else self.ref(t[1])
        return self.scalar(t)

    def of_seq(self, n, t):
        items = n[1]
        if t == STRING:                                # 文字・文字列・数を吸収した String: 字面だけなら長さが確定
            if all(m[0] == "lit" for m in items):
                text = "".join(str(m[1]) if not isinstance(m[1], float) else repr(m[1]) for m in items)
                return self.elements(len(text), CHAR)
            return Shape("dynamic", None, "String(長さは実行時)")
        shapes = [self.of(m) for m in items]
        if is_list(t) and all(sh.kind == "scalar" for sh in shapes):
            return self.elements(len(items), t[1])
        return Shape("dynamic", None, f"{show_t(t)}(要素数が静的に決まらない)") if is_list(t) else self.scalar(t)

    def of_prod(self, n, t):
        pairs = [(self.of(m), self.ty(m)) for m in n[1]]
        pairs = [(sh, ty) for sh, ty in pairs if sh.kind != "unit"]
        if is_struct(t): return self.of_slots([(None, sh, ty) for sh, ty in pairs])
        if is_list(t):
            if all(sh.kind == "scalar" for sh, _ in pairs): return self.elements(len(pairs), t[1])
            sizes = {sh.size for sh, _ in pairs}
            if len(sizes) == 1 and None not in sizes:                  # 同じ幅の行が並ぶ多次元: 行優先の連続ブロック
                row = next(iter(sizes)); return Shape("elements", row * len(pairs), f"{len(pairs)} 行 × {row} byte(行優先)", (), 1)
            return Shape("dynamic", None, f"{show_t(t)}(行の大きさが揃わない)")
        return self.scalar(t)

    def table(self):
        rows = []
        for name in self.c.order:
            sh = self.of_def(name)
            if sh.kind == "lambda":
                t = self.c.def_type(name)
                if is_fn(t):                           # 関数を返す関数だけは、フレームを超える関数オブジェクトを返す
                    r = self.c.fin(t.ret)
                    if is_addr_of(r) and is_fn(r[1]): rows.append((name + "(戻り値)", r[1], self.fnobj(r[1])))
                continue
            rows.append((name, self.c.def_type(name), sh))
        return rows

    def render(self):
        out = []
        for name, t, sh in self.table():
            size = f"{sh.size} byte" if sh.size is not None else "実行時"
            ts = show_t(t)
            head = f"{name} : {ts if len(ts) <= 40 else ts[:37] + '...'}"
            body = f"{sh.kind} {sh.desc}  ({size}" + (f", 境界 {sh.align}" if sh.kind in ("struct", "fnobj", "elements") else "") + ")"
            if sh.slots: body += "  オフセット " + " ".join(f"{k if k is not None else i}@{o}+{z}" for i, (k, o, z) in enumerate(sh.slots))
            out.append(f"{head:36} = {body}")
        return out

def infer(src, base_dir=".", layer=None, alpha=False):
    chk = Checker(S.parse_source(src), base_dir, (), layer, alpha).solve().cycle_pass().plain_pass().nest_pass().excess_pass()
    return chk.bare_function_return()

def read_option(directory):                     # option.ms の `キー : 値` の行
    path, out = os.path.join(directory, "option.ms"), {}
    if os.path.exists(path):
        for line in open(path, encoding="utf-8").read().split("\n"):
            parts = line.split()
            if len(parts) >= 3 and parts[1] == ":": out[parts[0]] = parts[2]
    return out

def read_layer(directory):                      # option.ms の layer : N
    v = read_option(directory).get("layer")
    return int(v) if v and v.isdigit() else None

if __name__ == "__main__":
    argv = sys.argv[1:]
    layer = None
    if "--layer" in argv:
        i = argv.index("--layer"); layer = int(argv[i + 1]); del argv[i:i + 2]
    charset = None
    if "--charset" in argv:
        i = argv.index("--charset"); charset = argv[i + 1]; del argv[i:i + 2]
    args = [a for a in argv if not a.startswith("--")]
    if not args: print(__doc__); sys.exit(2)
    path = os.path.abspath(args[0])
    if layer is None: layer = read_layer(os.path.dirname(path))      # 隣の option.ms があればその layer
    chk = infer(open(path, encoding="utf-8").read(), os.path.dirname(path), layer, "--alpha" in argv)
    if "--layout" in argv:
        cs = charset or read_option(os.path.dirname(path)).get("charset", "ascii")
        print("\n".join(Shaper(chk, cs).render()))
    else: print("\n".join(chk.signatures(only_exports="--st" in argv)))
    if "--diag" in argv:
        for kind, where, detail in chk.diags: print(f"  [{kind}] {where}: {detail}")
    for kind, where, detail in chk.errors(): print(f"エラー [{kind}] {where}: {detail}", file=sys.stderr)
    sys.exit(1 if chk.errors() else 0)
