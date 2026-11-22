"""strict の形の規則(sign_asm.STRICT_RULES)の整合試験: 各規則の見本が、書き換えられるか断られるかのどちらかになる(すり抜けない)こと。"""
import sign_asm, sign_interp as S
from fixblank import fix

SAMPLES = {
    1: ["l : 1 2 3\nk : 1\nl ' k\n"],
    2: ["f : x ? x\nn : 4\nn f\n", "f : x ? x\n5 f 1\n"],
    3: ["f : x ?\n\tx < 3 : 5 / 0\n\t7\nf 1\n"],
    4: ["f : x ?\n\tx : 5\n\t7\nf 1\n", "f : x ?\n\tzz : 5\n\t7\nf 1\n"],
    5: ["f : x y ? x != y\nf 3 4\n"],
    6: ["[>] 3 5 4\n", "[>] 3 __\n", "[==] 3 __ 3\n", "[<] (1 + 2) 5\n"],
}

def test_every_rule_listed():
    assert set(sign_asm.STRICT_RULES) == set(SAMPLES)

def test_no_form_slips_through():
    for no, srcs in SAMPLES.items():
        for src in srcs:
            src = fix(src.replace("\\\n", "\n").replace("\\\t", "\t"))
            tree = S.parse_source(src)
            new, rest = sign_asm.strict_rewrite(tree)
            assert new != tree or rest, "規則 %d の見本がすり抜けた: %r" % (no, src)
