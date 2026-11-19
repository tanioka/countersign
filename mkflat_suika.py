import re
s = open('suika.sn', encoding='utf-8').read()
def rep(old, new, cnt=1):
    global s
    n = s.count(old)
    assert n == cnt, (old[:60], n, cnt)
    s = s.replace(old, new)

# ---- F の読み: (@(F + (X * 4))) -> (fr X)
for X in ["i", "j", "a", "(@(G + 76))", "((@(G + 32)) - 1)"]:
    s = s.replace("(@(F + (%s * 4)))" % X, "(fr %s)" % X)
assert "(@(F +" not in s

# ---- 箱(G+52): 平らな配列へ
rep("boxof : cx cy r ? ss 52 ((@(G + 52))~ (cx - r) (cy - r) (cx + r) (cy + r))",
    "boxof : cx cy r ? boxw (@(G + 52)) (cx - r) (cy - r) (cx + r) (cy + r)\n\n"
    "boxw : n a b c d ? seq6 ((BX + (n * 8)) # a) ((BX + ((n + 1) * 8)) # b) ((BX + ((n + 2) * 8)) # c) ((BX + ((n + 3) * 8)) # d) (ss 52 (n + 4)) 0\n\n"
    "boxreset : z ? seq6 (BX # 999) ((BX + 8) # 999) ((BX + 16) # 999) ((BX + 24) # 999) (ss 52 4) 0")
rep("touches : px py r bs ?\n\t(((px + r) >= (bs ' 0)) & ((px - r) <= (bs ' 2))) & (((py + r) >= (bs ' 1)) & ((py - r) <= (bs ' 3))) : 1\n\t||bs|| <= 4 : 0\n\ttouches px py r (bs ' 4~)",
    "bxg : k ? @(BX + (k * 8))\n\ntouches : px py r i n ?\n\t(((px + r) >= (bxg i)) & ((px - r) <= (bxg (i + 2)))) & (((py + r) >= (bxg (i + 1))) & ((py - r) <= (bxg (i + 3)))) : 1\n\t(n - i) <= 4 : 0\n\ttouches px py r (i + 4) n")
rep("(@(G + 52))) = 0)) : 0", "0 (@(G + 52))) = 0)) : 0")
rep("nb : bs ? ||bs||\n\n", "")
rep("(nb (@(G + 52)))", "(@(G + 52))", 3)
rep("render : z ? seq7 (ss 52 [999 999 999 999])", "render : z ? seq7 (boxreset 0)")

# ---- LD(最後に描いた果物): 3 項目に展開
rep("ldget : i ? get (LD + i * 4)\nldput : i v ? LD + i * 4 # v",
    "ldget : i ? [(@(LD + (i * 32))) (@(LD + ((i * 32) + 8))) (@(LD + ((i * 32) + 16)))]\n"
    "ldput : i v ? seq4 ((LD + (i * 32)) # (v ' 0)) ((LD + ((i * 32) + 8)) # (v ' 1)) ((LD + ((i * 32) + 16)) # (v ' 2)) 0\n"
    "same3 : a b ?\n\t(((a ' 0) = (b ' 0)) & ((a ' 1) = (b ' 1))) & ((a ' 2) = (b ' 2)) : 1\n\t0")
rep("erase_i : cur old ?\n\tcur = old : 0", "erase_i : cur old ?\n\t(same3 cur old) = 1 : 0")
rep("(cur = old) & (((touches", "((same3 cur old) = 1) & (((touches")
rep("NONE : [999 999 999]", "NONE : [999 999 999]")

# ---- F の書き込み・読み
rep("cell : i ? get (F + i * 4)\nput : i v ? F + i * 4 # v",
    "fr : i ? [(@(F + (i * 64))) (@(F + ((i * 64) + 8))) (@(F + ((i * 64) + 16))) (@(F + ((i * 64) + 24))) (@(F + ((i * 64) + 32))) (@(F + ((i * 64) + 40))) (@(F + ((i * 64) + 48))) (@(F + ((i * 64) + 56)))]\n"
    "put : i v ? seq9 ((F + (i * 64)) # (v ' 0)) ((F + ((i * 64) + 8)) # (v ' 1)) ((F + ((i * 64) + 16)) # (v ' 2)) ((F + ((i * 64) + 24)) # (v ' 3)) ((F + ((i * 64) + 32)) # (v ' 4)) ((F + ((i * 64) + 40)) # (v ' 5)) ((F + ((i * 64) + 48)) # (v ' 6)) ((F + ((i * 64) + 56)) # (v ' 7)) 0")

# ---- RUNS: 件数つきの平らな表
rep("RUNS : 0x5100", "RUNS : 0x00C00000\nBX : 0x00B00000\nRN : 0x00C10000")
rep("mk : r dy sdy shw acc ?\n\tdy > r : acc~ sdy ((r + 1) - sdy) shw\n\t(hwf r dy) = shw : mk r (dy + 1) sdy shw acc\n\tmk r (dy + 1) dy (hwf r dy) (acc~ sdy (dy - sdy) shw)",
    "wr3 : base n a b c ? seq4 ((base + (n * 8)) # a) ((base + ((n + 1) * 8)) # b) ((base + ((n + 2) * 8)) # c) (n + 3)\n\n"
    "mk : base r dy sdy shw n ?\n\tdy > r : wr3 base n sdy ((r + 1) - sdy) shw\n\t(hwf r dy) = shw : mk base r (dy + 1) sdy shw n\n\tmk base r (dy + 1) dy (hwf r dy) (wr3 base n sdy (dy - sdy) shw)")
rep("setruns : lv ? RUNS + lv * 4 # ((mk (radius lv) (1 - (radius lv)) (0 - (radius lv)) (hwf (radius lv) (0 - (radius lv))) [0]) ' 1~)",
    "setruns : lv ? (RN + (lv * 8)) # (mk (RUNS + (lv * 1024)) (radius lv) (1 - (radius lv)) (0 - (radius lv)) (hwf (radius lv) (0 - (radius lv))) 0)")
rep("drawruns : x y c rs ?\n\t||rs|| <= 3 : rect (x - (rs ' 2)) (y + (rs ' 0)) (((rs ' 2) * 2) + 1) (rs ' 1) c\n\tseq2 (rect (x - (rs ' 2)) (y + (rs ' 0)) (((rs ' 2) * 2) + 1) (rs ' 1) c) (drawruns x y c (rs ' 3~))",
    "rg : lv k ? @(RUNS + ((lv * 1024) + (k * 8)))\n\n"
    "drawruns : x y c lv i n ?\n\t(n - i) <= 3 : rect (x - (rg lv (i + 2))) (y + (rg lv i)) (((rg lv (i + 2)) * 2) + 1) (rg lv (i + 1)) c\n\tseq2 (rect (x - (rg lv (i + 2))) (y + (rg lv i)) (((rg lv (i + 2)) * 2) + 1) (rg lv (i + 1)) c) (drawruns x y c lv (i + 3) n)")
rep("draw_rec : [px py lv] ? drawruns px py (col lv) (get (RUNS + lv * 4))",
    "draw_rec : [px py lv] ? drawruns px py (col lv) lv 0 (@(RN + (lv * 8)))")
rep("drawruns (@(G + 4)) 8 (col (@(G + 12))) (get (RUNS + (@(G + 12)) * 4))",
    "drawruns (@(G + 4)) 8 (col (@(G + 12))) (@(G + 12)) 0 (@(RN + ((@(G + 12)) * 8)))")

# ---- RS・AL・SL・CL: 間隔 8
rep("get (RS + i * 4)", "get (RS + (i * 8))")
rep("RS + i * 4 # v", "(RS + (i * 8)) # v")
rep("(SL + ((get SLN) * 4) # i)", "((SL + ((get SLN) * 8)) # i)")
rep("(AL + ((get ALN) * 4) # i)", "((AL + ((get ALN) * 8)) # i)")
rep("(get (AL + (p * 4)))", "(get (AL + (p * 8)))", 2)
rep("(get (base + (q * 4)))", "(get (base + (q * 8)))")
rep("(CL + ((get CLN) * 8) # i) (CL + (((get CLN) * 8) + 4) # j)", "((CL + ((get CLN) * 16)) # i) ((CL + ((get CLN) * 16) + 8) # j)")
rep("(get (CL + (p * 8))) (get (CL + ((p * 8) + 4)))", "(get (CL + (p * 16))) (get (CL + ((p * 16) + 8)))")
rep("SLN : 0x700004\nABORT : 0x700008\nCLN : 0x70000C", "SLN : 0x700008\nABORT : 0x700010\nCLN : 0x700018")

# ---- G: 間隔 8
rep("gs : k ? get (G + k)\nss : k v ? G + k # v", "gs : k ? get (G + (k * 2))\nss : k v ? (G + (k * 2)) # v")
s = re.sub(r"G \+ (\d+)", lambda m: "G + %d" % (int(m.group(1)) * 2), s)

# ---- 装置の番地(4 byte 間隔): 幅つき
rep("color : gfx + 0x08\npx : gfx + 0x0C\npy : gfx + 0x10\ncmd : gfx + 0x14\narg0 : gfx + 0x18\narg1 : gfx + 0x1C\nsleep : timer + 0x04\ncount : inp + 0x00\netype : inp + 0x04\necode : inp + 0x08\npop : inp + 0x14",
    "color : 4x09100008\npx : 4x0910000C\npy : 4x09100010\ncmd : 4x09100014\narg0 : 4x09100018\narg1 : 4x0910001C\nsleep : 4x09200004\ncount : 4x09300000\netype : 4x09300004\necode : 4x09300008\npop : 4x09300014")

# ---- ループの中で器(リスト)を作らない: 1 つずつ別の関数へ
rep("mv_all : i K ?", "mvone : i ? put i (mv (fr i))\n\nmv_all : i K ?")
rep("seq2 (put i (mv (fr i))) (mv_all (i + 1) K)", "seq2 (mvone i) (mv_all (i + 1) K)")

rep("fence_all : i K ?", "fenceone : i ? put i (fence (fr i))\n\nfence_all : i K ?")
rep("seq2 (put i (fence (fr i))) (fence_all (i + 1) K)", "seq2 (fenceone i) (fence_all (i + 1) K)")
rep("settle : i K ?", "settleone : i ? settle1 i (fr i)\n\nsettle : i K ?")
rep("seq2 (settle1 i (fr i)) (settle (i + 1) K)", "seq2 (settleone i) (settle (i + 1) K)")
rep("erase_all : i ?", "eone : i ? erase_i (pixrec i) (ldget i)\n\ndone : j ? draw_j j (pixrec j) (ldget j)\n\nerase_all : i ?")
rep("seq2 (erase_i (pixrec i) (ldget i)) (erase_all (i + 1))", "seq2 (eone i) (erase_all (i + 1))")
rep("seq2 (draw_j j (pixrec j) (ldget j)) (draw_all (j + 1))", "seq2 (done j) (draw_all (j + 1))")
rep("fF : i k ?" if False else "fr : i ? [", "fF : i k ? @(F + ((i * 64) + (k * 8)))\n\nfr : i ? [")
rep("\tabove2 i (fr i)", "\tabove2 i")
rep("above2 : i [lv x y vx vy pin r m] ?\n\t(y - r) < (TOP * 16) : 1", "above2 : i ?\n\t((fF i 2) - (fF i 6)) < (TOP * 16) : 1")
rep("near1 : a x y r j K [lj xj yj vxj vyj pj rj mj] ? near2 a x y r j K rj (xj - x) (yj - y)", "near1 : a x y r j K ? near2 a x y r j K (fF j 6) ((fF j 1) - x) ((fF j 2) - y)")
rep("\tnear1 a x y r j K (fr j)", "\tnear1 a x y r j K")
rep("(mn2 ht (top (fr i)))", "(mn2 ht ((fF i 2) - (fF i 6)))")
rep("start : i base q n ? start2 i (fr i) base q n", "start : i base q n ? start2 i base q n")
rep("start2 : i ri base q n ? scan i ri (ri ' 1) (ri ' 2) (ri ' 6) (rsget i) base q n", "start2 : i base q n ? scan i (fF i 1) (fF i 2) (fF i 6) (rsget i) base q n")
rep("scan : i ri xi yi rr si base q n ?\n\tq >= n : 0\n\tscan2 i ri xi yi rr si base q n (get (base + (q * 8)))", "scan : i xi yi rr si base q n ?\n\tq >= n : 0\n\tscan2 i xi yi rr si base q n (get (base + (q * 8)))")
rep("scan2 : i ri xi yi rr si base q n j ? probe i ri xi yi rr si base q n j (fr j)", "scan2 : i xi yi rr si base q n j ? probe2 i xi yi rr si base q n j (fF j 6) (((((fF j 1) - xi) * ((fF j 1) - xi)) + (((fF j 2) - yi) * ((fF j 2) - yi))))")
rep("probe : i ri xi yi rr si base q n j [lj xj yj vxj vyj pj rj mj] ? probe2 i ri xi yi rr si base q n j rj ((((xj - xi) * (xj - xi)) + ((yj - yi) * (yj - yi))))\n\n", "")
rep("probe2 : i ri xi yi rr si base q n j rj d2 ?", "probe2 : i xi yi rr si base q n j rj d2 ?")
rep("scan i ri xi yi rr si base (q + 1) n", "scan i xi yi rr si base (q + 1) n")
rep("scan i ri xi yi rr (wake1 i j si) base (q + 1) n", "scan i xi yi rr (wake1 i j si) base (q + 1) n")
rep("(touch i j ri (fr j))", "(touch i j)")
rep("touch : i j ri rj ? seq2 (cl_add i j) (chk i j ri rj ri rj)", "touch : i j ? seq2 (cl_add i j) (chk i j (fr i) (fr j) (fr i) (fr j))")
open('suika_flat.sn', 'w', encoding='utf-8').write(s)
print("ok")
