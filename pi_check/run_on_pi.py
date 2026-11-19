#!/usr/bin/env python3
"""run_on_pi.py — Raspberry Pi 実機で bin/ の各プログラム(Sign を --real-dev で AArch64 の静的 ELF にしたもの)を走らせ、
疑似カーネル(fake_kernel.py)の予想(expected.json)と突き合わせて、食い違いを report.md / report.json に書く。
  使い方:  python3 run_on_pi.py            ← この箱で
  GPIO は PIN(既定 26 = 基板の 37 番ピン)を使う。何もつないでいない空きピンにすること。出力にして HIGH/LOW を出し、プルアップ・プルダウンで読む。
  I2C: 何もつながなくてよい(応答しない相手への PROBE の失敗番号を見る)。AHT25(0x38)をつなげば t_i2c_probe が 0 になる。
  SPI: MOSI と MISO(GPIO10 と GPIO9)を線 1 本でつなぐとループバックになる(つながなくても ioctl の通り方は確かめられる)。
  strace があれば、openat・ioctl・mmap の戻りを trace/ に残す(食い違いの原因探し用)。
"""
import resource, json, os, re, shutil, subprocess, sys, time
HERE = os.path.dirname(os.path.abspath(__file__))
exp = json.load(open(os.path.join(HERE, "expected.json"), encoding="utf-8"))

def sh(cmd):
    try: return subprocess.run(cmd, shell=True, capture_output=True, text=True, timeout=20).stdout.strip()
    except Exception as e: return "(%s)" % e

env = {
    "model": sh("cat /proc/device-tree/model | tr -d '\\0'"), "kernel": sh("uname -srm"), "os": sh("grep PRETTY /etc/os-release | cut -d= -f2"),
    "mmap_min_addr": sh("cat /proc/sys/vm/mmap_min_addr"), "overcommit_memory": sh("cat /proc/sys/vm/overcommit_memory"),
    "devices": sh("ls /dev/i2c-* /dev/spidev* /dev/gpiochip* 2>&1 | tr '\\n' ' '"), "user": sh("id"),
    "strace": bool(shutil.which("strace")),
}

def run(name, timeout=15):
    if os.environ.get("DRY"):                                    # 疑似カーネルの予想をそのまま実機の出力とみなす(判定の書き方の確認用)
        e = exp[name]; return e["stdout"], e["exit"] or 0, "", 0.0
    exe = os.path.join(HERE, "bin", name); os.chmod(exe, 0o755)
    cmd = [exe]
    if env["strace"]:
        os.makedirs(os.path.join(HERE, "trace"), exist_ok=True)
        cmd = ["strace", "-f", "-e", "trace=" + ("read," if name.startswith("t_input") else "") + "openat,ioctl,mmap,nanosleep,clock_nanosleep,clock_gettime,socket,connect,bind,listen,accept,accept4,getsockname,setsockopt,sendto,recvfrom,ppoll,close", "-o", os.path.join(HERE, "trace", name + ".txt")] + cmd
    t0 = time.time()
    try: r = subprocess.run(cmd, capture_output=True, timeout=timeout, stdin=subprocess.DEVNULL); out, code, err = r.stdout.decode("utf-8", "replace"), r.returncode, r.stderr.decode("utf-8", "replace")
    except subprocess.TimeoutExpired: out, code, err = "", "timeout", ""
    return out, code, err, time.time() - t0

def num(s):
    m = re.fullmatch(r"\s*(-?\d+)\s*", s); return int(m.group(1)) if m else None

# (名前, 判定 → (結果, 一言), 食い違ったときの見立て)
def j_exact(want): return lambda o: ("一致" if o.strip() == want else "食い違い", "")
checks = {
 "t_map": (lambda o: ("一致" if o.strip() == "79" else "食い違い", ""), "mmap の確保が通らない(終了コード 1 と標準エラー)か、--image-base が効いていない。mmap_min_addr と overcommit_memory を見る"),
 "t_clock": (lambda o: ("一致" if num(o) is not None and 200 <= num(o) <= 260 else "食い違い", "経過 %s ms(200〜260 を期待)" % o.strip()), "clock_gettime / nanosleep の単位(秒・ナノ秒の構造体の並び)"),
 "t_uart": (lambda o: ("一致" if o.startswith("Hi\n") else "食い違い", ""), "write(1) の出力"),
 "t_gpio_out": (lambda o: ("一致" if o.strip() == "10" else "食い違い", "出力 HIGH → LOW を読み戻して %s(10 を期待)" % o.strip()), "GPIO v2 の構造体(行の要求 592 バイト・値 16 バイト)の並び、chip の番号(Pi 5 は gpiochip4 のことがある)、権限(gpio グループ)"),
 "t_gpio_bias": (lambda o: ("一致" if o.strip() == "10" else "食い違い", "プルアップ・プルダウンで %s(何もつないでいなければ 10)" % o.strip()), "BIAS フラグ(1<<8, 1<<9)・反映までの待ち。外付けの抵抗が付いていないか"),
 "t_i2c_probe": (lambda o: ("一致" if num(o) in (-6, 0) else "食い違い", "PROBE の戻り %s(応答しなければ -6、応答すれば 0。実機の Pi 4 は読みが -5 で失敗するので、中継ルーチンが -6 にそろえる)" % o.strip()), "I2C が有効でない(-2 = /dev/i2c-1 が無い)、権限(i2c グループ)"),
 "t_i2c_nobus": (lambda o: ("一致" if num(o) == -2 else "食い違い", "存在しないバス 99 → %s(-2 = ENOENT を期待)" % o.strip()), "openat のエラー番号の符号"),
 "t_i2c_aht25": (lambda o: ("参考", "AHT25 をつないだときの温度(0.01℃)= %s。つないでいなければ 0 か負" % o.strip()), "AHT25 のとき: I2C_RDWR の 2 メッセージの通り方"),
 "t_spi_ret": (lambda o: ("一致" if num(o) == 4 else ("食い違い" if num(o) is not None and num(o) != -2 else "食い違い"), "SPI の戻り %s(4 = 通った、-2 = /dev/spidev0.0 が無い)" % o.strip()), "SPI が有効でない、構造体 spi_ioc_transfer の並び(bits_per_word は +25)、SPI_IOC_WR_MODE の番号"),
 "t_spi_rx": (lambda o: ("一致" if num(o) == 4027538085 else ("許容" if num(o) in (0, 4294967295) else "食い違い"), "受信 %s(%d = ループバックが通った。0 か 4294967295 = MOSI と MISO をつないでいない)" % (o.strip(), 4027538085)), "MOSI-MISO の配線"),
 "t_net_tcp": (lambda o: ("一致" if o.split() == "5 5 104 111 0 0 0 0 -9 0".split() else "食い違い", "ループバックの TCP 往復 %s" % o.split()), "socket/connect/accept の戻り、ppoll の待ち、recvfrom の MSG_DONTWAIT(0x40)"),
 "t_net_udp": (lambda o: ("一致" if o.split()[:7] == "5 5 104 49 49 58 50".split() and o.split()[7:9] == ["0", "-11"] else "食い違い", "UDP %s(送り主は 127.0.0.1:ポート)" % o.split()), "recvfrom の sockaddr(port は前後入れ替え)、SETTIMEOUT 100 の後の -11"),
 "t_net_refused": (lambda o: ("一致" if num(o.split()[0]) == -111 else "食い違い", "閉じたポートへの CONNECT %s(-111)" % o.split()), "connect の errno"),
 "t_net_timeout": (lambda o: ("一致" if o.split()[0] == "-11" and 190 <= int(o.split()[1]) <= 400 else "食い違い", "待ち時間切れ %s(-11 と、200 ms 前後の経過)" % o.split()), "ppoll の timespec の ms → 秒・ナノ秒"),
 "t_net_names": (lambda o: ("一致" if o.split()[:2] == ["-2", "-2"] else "食い違い", "数字でない名前 %s(-2)" % o.split()), "名前の解決は IPv4 の数字と localhost だけ(DNS は無い)"),
 "t_net_tls": (lambda o: ("一致" if o.split()[:2] == ["-38", "-9"] else "食い違い", "TLS_START %s(-38、知らないハンドルは -9)" % o.split()), "TLS は未対応"),
 "t_sys_file": (lambda o: ("一致" if o.split()[:10] == "1 5 0 5 5 104 0 -2 -13 -13".split() and o.split()[10] == "1" and o.split()[11:13] == ["-9", "-38"] else "食い違い", "sys %s" % o.split()), "openat2(437)・RESOLVE_BENEATH(外は EXDEV → -13)・lseek(62)。カーネルが 5.6 より古いと -38"),
 "t_dns_name": (lambda o: ("参考", "example.com の解決 %s(つながっていれば 9〜15 の長さ、つながっていなければ -2)" % o.split()[0]), "/etc/resolv.conf の最初の nameserver(IPv4)へ UDP 53。nameserver が 127.0.0.53(systemd-resolved)なら通るはず。IPv6 だけの nameserver だと -2"),
 "t_input_idle": (lambda o: (("参考" if len(o.split()) == 5 and all(num(x) is not None for x in o.split()) else "食い違い"), "何も触らない間の 件数・MX・MY・ボタン = %s(開けた event が無ければ全部 0。触っていれば件数や位置が出る)" % o.split()), "/dev/input/event* が開けない(input グループ)だけなら 0 のまま。出力の形が崩れているなら 0x9300000 の読み"),
 "t_input_live": (lambda o: (("参考" if o.split() and all(num(x) is not None for x in o.split()) and len(o.split()) >= 2 and (len(o.split()) - 2) % 2 == 0 else "食い違い"), "3 秒のあいだに出た出来事 %s 件(押すと『種類 符号』= 1 97 のように並ぶ。この間にキーを押す・マウスを動かすと増える)" % (o.split()[-2] if len(o.split()) >= 2 else "?")), "evdev の input_event の並び(24 バイト: 時刻 16・種類 2・符号 2・値 4)・キー表"),
 "t_gfx_fb": (lambda o: ("参考", "PRESENT 後の FRAME・STATUS(+末尾の 0) = %s(1 0 なら呼び出しは通った。画面に出るかは tty コンソールでだけ見える。stderr に ERR が出ていれば /dev/fb0 が開けなかった)" % o.split()), "gfx は /dev/fb0(要 video グループ・コンソール)"),
 "t_sound_tone": (lambda o: ("一致" if o.split()[:3] in (["0", "1", "0"], ["-19", "0", "0"]) else "食い違い", "TONE の RET と BUSY・STOP 後の BUSY = %s(aplay があれば 0 1 0、無ければ -19 0 0)" % o.split()), "音は aplay を子プロセスにして標準入力へ WAV(要 alsa-utils・audio グループ)"),
 "t_alarm": (lambda o: ("一致" if re.fullmatch(r"\.{5,10}1\.{5,10}2\.{5,10}30\n?", o) else "食い違い", "パターン %r(点は 1 こま = 16 ms。100 ms ごとに数字、3 で終わり)" % o), "こまの待ちの引き算(nanosleep の戻り・実時間のぶれ)。1 こまの上下は許容"),
}
rows, fails = [], 0
for name in sorted(checks):
    if not os.path.exists(os.path.join(HERE, "bin", name)): continue
    out, code, err, dt = run(name)
    verdict, note = checks[name][0](out)
    if code not in (0, "timeout") and verdict == "一致": verdict = "食い違い"
    if verdict == "食い違い": fails += 1
    rows.append(dict(name=name, verdict=verdict, note=note, stdout=out, exit=code, stderr=err.strip()[:300], seconds=round(dt, 2), fake_kernel_expected=exp.get(name, {}).get("stdout"), hint=checks[name][1] if verdict == "食い違い" else ""))

# ---- 並列(--par): 直列(_s)・--par=2(_p2)・--par=4(_p4)の答えが同じか、かかった時間(周回の最短。周回数は環境変数 PAR_REPEAT・OPT_REPEAT・SPEC_REPEAT、既定 5)と直列に対する倍率 ----
# strace は付けない(スレッドが入ると極端に遅くなり、時間が測れない)。clone・futex が通らなければ、答えが出るが速くならない(直列に戻る)か、止まる(timeout)。
def _sysnum(path):
    try: return int(open(path).read().strip())
    except Exception: return None
def _throttled():
    try: return subprocess.run(["vcgencmd", "get_throttled"], capture_output=True, text=True, timeout=5).stdout.strip()
    except Exception: return "vcgencmd なし"

def _measure_arm():
    try:
        o = subprocess.run(["vcgencmd", "measure_clock", "arm"], capture_output=True, text=True, timeout=2).stdout.strip()
        return int(o.split("=")[1]) // 1000
    except Exception: return None

def _thr_bits(s):
    try: return int(s.split("=")[1], 16)
    except Exception: return 0

LAPS = {}      # 名前 → [(wall, cpu, 自発切替, 強制切替) …](周の順)
FREQS = {}     # 名前 → [(最小kHz, 最大kHz, 制限ビットの和, 温度最大ミリ℃) …](周の順)。実行中に 100 ms ごとの cpu0 周波数・500 ms ごとの get_throttled を拾う
import threading
class Sampler(threading.Thread):
    """周回の間、cpu0 の scaling_cur_freq(kHz)・温度・get_throttled を拾う(クロックが落ちるか、電圧低下・熱の制限が立つかを実行中に見る)。"""
    def __init__(self):
        threading.Thread.__init__(self, daemon=True); self.stop_ = False; self.f = []; self.bits = 0; self.tmax = 0
    def run(self):
        n = 0
        while not self.stop_:
            v = _measure_arm()          # 実際の ARM クロック(kHz)。scaling_cur_freq は要求の値で、制限中でも下がらないことがある
            if not v: v = _sysnum("/sys/devices/system/cpu/cpu0/cpufreq/scaling_cur_freq")
            if v: self.f.append(v)
            t = _sysnum("/sys/class/thermal/thermal_zone0/temp")
            if t: self.tmax = max(self.tmax, t)
            if n % 5 == 0: self.bits |= _thr_bits(_throttled())
            n += 1; time.sleep(0.1)
    def done(self):
        self.stop_ = True; self.join(1.0)
        return (min(self.f) if self.f else 0, max(self.f) if self.f else 0, self.bits, self.tmax)

def _rounds(names, want, envname, outs, codes):
    """変種を 1 周ずつ順に走らせる(変種ごとにまとめて走らせると、熱や時間の流れの偏りが特定の変種に乗る)。周回数は環境変数 envname(既定 5)。全周の時間 {名前: [秒…]} を返す。"""
    R = int(os.environ.get(envname, "5")); all_ts = {n: [] for n in names}
    for _ in range(R):
        for n in names:
            if codes.get(n, 0) != 0: continue
            ru0 = resource.getrusage(resource.RUSAGE_CHILDREN); smp = Sampler(); smp.start()
            if os.environ.get("DRY"): outs[n], codes[n], dt = want, 0, 0.01
            else:
                exe = os.path.join(HERE, "bin", n); os.chmod(exe, 0o755); t0 = time.time()
                try: r = subprocess.run([exe], capture_output=True, timeout=180, stdin=subprocess.DEVNULL); outs[n], codes[n] = r.stdout.decode("utf-8", "replace"), r.returncode
                except subprocess.TimeoutExpired: outs[n], codes[n] = "", "timeout"
                dt = time.time() - t0
            FREQS.setdefault(n, []).append(smp.done())
            ru1 = resource.getrusage(resource.RUSAGE_CHILDREN)      # この 1 周で子が使った CPU 時間(user+sys)と文脈切り替え(自発・強制)
            LAPS.setdefault(n, []).append((dt, ru1.ru_utime + ru1.ru_stime - ru0.ru_utime - ru0.ru_stime, ru1.ru_nvcsw - ru0.ru_nvcsw, ru1.ru_nivcsw - ru0.ru_nivcsw))
            all_ts[n].append(dt)
    return all_ts

def _spread(ts, name=None):
    t = "%d 周の最短。中央値 %.2f・平均 %.2f・最大 %.2f" % (len(ts), sorted(ts)[len(ts) // 2], sum(ts) / len(ts), max(ts))
    laps = LAPS.get(name) or []
    if len(laps) == len(ts) and ts and max(ts) > 1.3 * min(ts) and max(l[1] for l in laps) > 0:      # 二つの山: 最短の周と最長の周の CPU 時間/wall・文脈切り替えを並べる
        a = min(laps); b = max(laps)
        t += "。【山あり】最短の周 wall %.2f・CPU %.2f(CPU/wall %.2f、切替 自発%d 強制%d)、最長の周 wall %.2f・CPU %.2f(CPU/wall %.2f、切替 自発%d 強制%d)" % (a[0], a[1], a[1] / a[0] if a[0] else 0, a[2], a[3], b[0], b[1], b[1] / b[0] if b[0] else 0, b[2], b[3])
    fr = FREQS.get(name) or []
    if fr and any(x[1] for x in fr):
        lo = min(x[0] for x in fr if x[0]) if any(x[0] for x in fr) else 0; hi = max(x[1] for x in fr); bits = 0
        for x in fr: bits |= x[2]
        t += "。実行中の ARM クロック %d〜%d MHz・制限ビット 0x%X(bit0 電圧低下・bit1 周波数上限・bit2 制限中・bit3 温度上限が実行中に立った)・温度最大 %.1f ℃" % (lo // 1000, hi // 1000, bits & 0xF, max(x[3] for x in fr) / 1000.0)
        slow = [(l[0], x[0]) for l, x in zip(LAPS.get(name) or [], fr) if x[0]]
        if slow and len(slow) > 1 and max(w for w, _ in slow) > 1.3 * min(w for w, _ in slow): t += "。遅い周ほど周波数が低いか: " + " / ".join("%.2f秒=%dMHz" % (w, f // 1000) for w, f in slow)
    return t

def par_group(base):
    names = [base + "_s", base + "_p2", base + "_p4"] + [base + x for x in ("_p3", "_p4site", "_p4l1000", "_p4l0") if os.path.exists(os.path.join(HERE, "bin", base + x))]
    if not all(os.path.exists(os.path.join(HERE, "bin", n)) for n in names): return
    want = exp.get(names[0], {}).get("stdout"); best = {}; outs = {}; codes = {}; th_a = _throttled()
    all_ts = _rounds(names, want, "PAR_REPEAT", outs, codes)
    for n in names: best[n] = min(all_ts[n])
    global fails
    th_b = _throttled(); throttled_ = bool(_thr_bits(th_a) & 0x5 or _thr_bits(th_b) & 0x5)
    for n in names:
        ok = outs[n] == want and codes[n] == 0
        sp = "" if n.endswith("_s") else "、直列の %.2f 倍速い" % (best[names[0]] / best[n] if best[n] else 0)
        if not ok: fails += 1
        q3 = base + "_p3"
        if "_p4" in n and q3 in all_ts and all_ts[q3] and all_ts[n]: sp += "、_p3 の平均 %.2f 秒に対し平均 %.2f 秒(_p3 の %.2f 倍)" % (sum(all_ts[q3]) / len(all_ts[q3]), sum(all_ts[n]) / len(all_ts[n]), (sum(all_ts[q3]) / len(all_ts[q3])) / (sum(all_ts[n]) / len(all_ts[n])))      # 4 コアに 4 本だと山が出るなら、平均は 3 本(_p3)に負けうる
        rows.append(dict(name=n, verdict="一致" if ok else "食い違い", note="%.2f 秒%s(%s。答えは直列と同じ・終了コード 0 を期待。4 コアなら _p4 は 1.6〜2 倍を見込む)%s" % (best[n], sp, _spread(all_ts[n], n), ("【電源の電圧低下・熱の制限が出ていた(get_throttled %s → %s)ので、時間の比べは当てになりません】" % (th_a, th_b)) if throttled_ else ""), stdout=outs[n], exit=codes[n], stderr="", seconds=round(best[n], 2), all_seconds=[round(x, 3) for x in all_ts[n]], laps=[[round(v, 3) for v in l] for l in LAPS.get(n, [])],
                         fake_kernel_expected=want, hint="clone(スレッド)・mmap(積み)・futex が通らない(戻りの errno)か、cntvct_el0 が読めない。_s と _p* の答えが違えば並列の不具合(報告してほしい)。timeout は合流の待ちが終わらない"))
env["cpus"] = os.cpu_count()
for base in ("t_par_fib", "t_par_fib1", "t_par_fib4", "t_par_args", "t_par_local", "t_par_list", "t_par_loop", "t_hof_par"): par_group(base)

# ---- スレッドごとの自発的切替(第109段 続き 23)。実行中に /proc/<pid>/task/*/status を 5 ms ごとに読み、各スレッドの最後の値を残す(strace なし。終了の直前の値で、最後の数 ms は欠ける) ----
def thread_sw(name):
    exe = os.path.join(HERE, "bin", name)
    if os.environ.get("DRY") or not os.path.exists(exe): return None
    os.chmod(exe, 0o755); t0 = time.time()
    pr = subprocess.Popen([exe], stdout=subprocess.DEVNULL, stdin=subprocess.DEVNULL); last = {}; order = []
    while pr.poll() is None:
        try:
            for tid in os.listdir("/proc/%d/task" % pr.pid):
                try: st = open("/proc/%d/task/%s/status" % (pr.pid, tid)).read()
                except OSError: continue
                v = n = None
                for ln in st.splitlines():
                    if ln.startswith("voluntary_ctxt_switches"): v = int(ln.split()[1])
                    elif ln.startswith("nonvoluntary_ctxt_switches"): n = int(ln.split()[1])
                try: cpu_ms = int(open("/proc/%d/task/%s/schedstat" % (pr.pid, tid)).read().split()[0]) // 1000000
                except (OSError, ValueError, IndexError): cpu_ms = -1
                if v is not None:
                    if tid not in last: order.append(tid)
                    last[tid] = (v, n, cpu_ms)
        except OSError: pass
        time.sleep(0.005)
    return round(time.time() - t0, 2), [last[t] for t in order]
if not os.environ.get("DRY"):
    for base in ("t_par_fib", "t_par_fib4"):
        for x in ("_p4", "_p4site"):
            n = base + x; laps_ = []
            for _ in range(max(8, int(os.environ.get("PAR_REPEAT", "5"))) if x in ("_p4", "_p4site") else int(os.environ.get("PAR_REPEAT", "5"))):
                r_ = thread_sw(n)
                if r_: laps_.append(r_)
            if not laps_: continue
            rows.append(dict(name=n + "_threads", verdict="参考", note="スレッドごとの自発的切替/強制切替/CPU 時間 ms(先頭が主スレッド、続きが労働者。壁時計 秒: 自発/強制/CPU ms ...。CPU は schedstat の最後の読み) = " + " | ".join("%.2f: %s" % (w_, " ".join("%d/%d/%dms" % t for t in th)) for w_, th in laps_), stdout="", exit=0, stderr="", seconds=0.0, fake_kernel_expected="", hint=""))

# ---- 最適化の効果(第108段): 同じプログラムの最適化あり(_opt)となし(_noopt)の答えが同じか、かかった時間(周回の最短。周回数は環境変数 PAR_REPEAT・OPT_REPEAT・SPEC_REPEAT、既定 5)と倍率 ----
def opt_group(base):
    names = [base + "_noopt", base + "_opt"]
    if not all(os.path.exists(os.path.join(HERE, "bin", n)) for n in names): return
    want = exp.get(names[0], {}).get("stdout"); best = {}; outs = {}; codes = {}
    all_ts = _rounds(names, want, "OPT_REPEAT", outs, codes)
    for n in names: best[n] = min(all_ts[n])
    global fails
    for n in names:
        ok = outs[n] == want and codes[n] == 0
        if not ok: fails += 1
        sp = "" if n.endswith("_noopt") else "、最適化なしの %.2f 倍速い" % (best[names[0]] / best[n] if best[n] else 0)
        rows.append(dict(name=n, verdict="一致" if ok else "食い違い", note="%.2f 秒%s(%s。答えは期待どおり・終了コード 0 を期待)" % (best[n], sp, _spread(all_ts[n], n)), stdout=outs[n], exit=codes[n], stderr="", seconds=round(best[n], 2), all_seconds=[round(x, 3) for x in all_ts[n]], laps=[[round(v, 3) for v in l] for l in LAPS.get(n, [])],
                         fake_kernel_expected=want, hint="_noopt と _opt の答えが違えば最適化の誤り(第108段)。どちらも違えば疑似カーネルとの食い違い。"))
for base in ("t_opt_fib", "t_opt_loop", "t_opt_list"): opt_group(base)

# ---- 特殊化(第110段): 高階関数の版(_hof)と、手で特殊化した版(_dir)の答えが同じか、かかった時間(周回の最短。周回数は環境変数 HOF_REPEAT、既定 5)と比 ----
def hof_group(base):
    names = [base + "_dir", base + "_hof"]
    if not all(os.path.exists(os.path.join(HERE, "bin", n)) for n in names): return
    want = exp.get(names[0], {}).get("stdout"); best = {}; outs = {}; codes = {}
    all_ts = _rounds(names, want, "HOF_REPEAT", outs, codes)
    for n in names: best[n] = min(all_ts[n])
    global fails
    for n in names:
        ok = outs[n] == want and codes[n] == 0
        if not ok: fails += 1
        sp = "" if n.endswith("_dir") else "、手で特殊化した版(_dir)の %.2f 倍の時間" % (best[n] / best[names[0]] if best[names[0]] else 0)
        rows.append(dict(name=n, verdict="一致" if ok else "食い違い", note="%.2f 秒%s(%s。答えは期待どおり・終了コード 0 を期待。特殊化が効いていれば _hof は _dir とほぼ同じ時間)" % (best[n], sp, _spread(all_ts[n], n)), stdout=outs[n], exit=codes[n], stderr="", seconds=round(best[n], 2), all_seconds=[round(x, 3) for x in all_ts[n]], laps=[[round(v, 3) for v in l] for l in LAPS.get(n, [])],
                         fake_kernel_expected=want, hint="_hof と _dir の答えが違えば特殊化の誤り(第110段。報告してほしい)。どちらも違えば疑似カーネルとの食い違い。"))
for base in ("t_hof_rep", "t_hof_fold", "t_hof_map", "t_hof_cap"): hof_group(base)

# ---- 投機(第109段 --par-spec): 直列(_s)・--par=4(_p4)・--par-spec(_spec)の答えが同じか、かかった時間(周回の最短。周回数は環境変数 PAR_REPEAT・OPT_REPEAT・SPEC_REPEAT、既定 5)と直列に対する倍率 ----
def spec_group(base):
    names = [base + "_s", base + "_p4", base + "_spec"] + [base + x for x in ("_p2", "_p2spec", "_p3", "_p3spec", "_specab", "_p3specab", "_look", "_p3look") if os.path.exists(os.path.join(HERE, "bin", base + x))]
    if not all(os.path.exists(os.path.join(HERE, "bin", n)) for n in names): return
    want = exp.get(names[0], {}).get("stdout"); best = {}; outs = {}; codes = {}; th_a = _throttled()
    all_ts = _rounds(names, want, "SPEC_REPEAT", outs, codes)
    for n in names: best[n] = min(all_ts[n])
    global fails
    th_b = _throttled(); throttled_ = bool(_thr_bits(th_a) & 0x5 or _thr_bits(th_b) & 0x5)
    what = {"t_spec_or": "左 fib 36 が __ → 右 fib 35 が要る(直列は 36+35、投機は 2 コアで約 max。速くなるはず)", "t_spec_gtrue": "条件 fib 36 が成り立つ → 値 fib 35(速くなるはず)",
            "t_spec_gfalse": "条件が外れる → 値 fib 35 は捨てる(無駄な仕事。速くならない・遅くもならないはず。捨てるのは走行中の仕事を止めない)", "t_spec_rows": "行が 2 つ: 1 行目の条件(fib 34)は外れ、2 行目の条件(fib 33)が成り立つ → 値 fib 35。_look は 2 行目の値も 1 行目の条件を調べる間に先に走らせる(_look は _spec と、_p3look は _p3spec と比べる)", "t_spec_trap": "左 fib 36 が決める・右は罠(溢れ): 投機は巻き戻して捨てる。止まらず答えは左(速さは直列と同じ程度のはず)"}[base]
    for n in names:
        ok = outs[n] == want and codes[n] == 0
        sp = "" if n.endswith("_s") else "、直列の %.2f 倍速い" % (best[names[0]] / best[n] if best[n] else 0)
        if n.endswith(("_spec", "_p2spec", "_p3spec", "_specab", "_p3specab", "_look", "_p3look")):      # 投機あり/なしの比 = 投機だけの効き(_spec は _p4 と、_p2spec は _p2 と比べる)
            q = base + ("_p2" if n.endswith("_p2spec") else "_p3" if n.endswith(("_p3spec", "_p3specab")) else "_spec" if n.endswith("_look") else "_p3spec" if n.endswith("_p3look") else "_p4")
            if q in best and best[n]: sp += "、投機なし(%s)の %.2f 倍速い" % (q[len(base):], best[q] / best[n])
        if not ok: fails += 1
        rows.append(dict(name=n, verdict="一致" if ok else "食い違い", note="%.2f 秒%s(%s。%s)%s" % (best[n], sp, _spread(all_ts[n], n), what, ("【電源の電圧低下・熱の制限が出ていた(get_throttled %s → %s)ので、時間の比べは当てになりません】" % (th_a, th_b)) if throttled_ else ""), stdout=outs[n], exit=codes[n], stderr="", seconds=round(best[n], 2), all_seconds=[round(x, 3) for x in all_ts[n]], laps=[[round(v, 3) for v in l] for l in LAPS.get(n, [])],
                         fake_kernel_expected=want, hint="3 本の答えが違えば投機の不具合(報告してほしい)。timeout は投機の合流・捨てるの待ちが終わらない。_trap で止まる(終了コードが 0 でない・出力が空)なら、巻き戻し(mrs tpidr_el0 の TLS+16)が実機で効いていない"))
for base in ("t_spec_or", "t_spec_gtrue", "t_spec_gfalse", "t_spec_trap", "t_spec_rows"): spec_group(base)

# ---- 対照(第104段): 直列版 t_par_loop_s を k 本(1・2・3・4)同時に走らせる。--par を使わない。k 本のどれも 1 本のときと同じ時間なら、コアは k 本とも本当に並行に走れる。
# k が増えて 1 本ごとの時間が伸びるなら、コアの数・周波数の制限・熱・電源(スロットル)の側で、--par の実装のせいではない。前後に vcgencmd の get_throttled・温度・周波数も書く。
exe_c = os.path.join(HERE, "bin", "t_par_loop_s")
if os.path.exists(exe_c) and not os.environ.get("DRY"):
    os.chmod(exe_c, 0o755)
    for k_ in (1, 2, 3, 4):
        th0, t_c0, f0 = _throttled(), _sysnum("/sys/class/thermal/thermal_zone0/temp"), _sysnum("/sys/devices/system/cpu/cpu0/cpufreq/scaling_cur_freq")
        smp_ = Sampler(); smp_.start(); t0 = time.time(); ps = [subprocess.Popen([exe_c], stdout=subprocess.PIPE, stdin=subprocess.DEVNULL) for _ in range(k_)]; each = []
        for pr in ps: pr.communicate(); each.append(round(time.time() - t0, 2))
        smp_r = smp_.done()
        th1, t_c1, f1 = _throttled(), _sysnum("/sys/class/thermal/thermal_zone0/temp"), _sysnum("/sys/devices/system/cpu/cpu0/cpufreq/scaling_cur_freq")
        rows.append(dict(name="対照_並行%d本" % k_, verdict="参考", note="t_par_loop_s を %d 本同時に: 各本の終わるまで %s 秒(1 本なら約 7.4 秒。増えて伸びるならコア・周波数・熱・電源の側)。get_throttled %s → %s、温度(ミリ℃) %s → %s、cpu0 周波数(kHz) %s → %s。実行中: 周波数 %d〜%d MHz・制限ビット 0x%X・温度最大 %.1f ℃(1 本の時の各本の時間と比べる。周波数が落ちるなら電源・熱の側)" % (k_, each, th0, th1, t_c0, t_c1, f0, f1, smp_r[0] // 1000, smp_r[1] // 1000, smp_r[2] & 0xF, smp_r[3] / 1000.0), stdout="", exit=0, stderr="", seconds=max(each), fake_kernel_expected="", hint=""))

# ---- SQLite(--real-db): Pi 上で gcc と libsqlite3-dev があれば、一式を組み立てて走らせる ----
import shutil, tempfile
bdir_root = os.path.join(HERE, "dbbundle")
if os.path.isdir(bdir_root):
    import platform
    have = shutil.which("gcc") and os.path.exists("/usr/include/sqlite3.h") and platform.machine() in ("aarch64", "arm64") and not os.environ.get("DRY")
    for name in sorted(os.listdir(bdir_root)):
        want = exp.get(name, {}).get("stdout")
        if not have:
            rows.append(dict(name=name, verdict="未実施", note="gcc か libsqlite3-dev が無い(sudo apt install gcc libsqlite3-dev のあと、もう一度)", stdout="", exit=None, stderr="", seconds=0, fake_kernel_expected=want, hint="")); continue
        bd = os.path.join(bdir_root, name); t0 = time.time()
        b = subprocess.run(["sh", "build.sh"], cwd=bd, capture_output=True, text=True)
        if b.returncode != 0:
            fails += 1; rows.append(dict(name=name, verdict="食い違い", note="gcc で組み立てに失敗", stdout="", exit=b.returncode, stderr=b.stderr.strip()[:300], seconds=round(time.time() - t0, 2), fake_kernel_expected=want, hint="-Ttext-segment・-nostartfiles・-lsqlite3 のどれか")); continue
        wd = tempfile.mkdtemp()
        cmd = [os.path.join(bd, "prog")]
        if env["strace"]:
            cmd = ["strace", "-f", "-o", os.path.join(HERE, "trace", name + ".txt")] + cmd
            os.makedirs(os.path.join(HERE, "trace"), exist_ok=True)
        try: r = subprocess.run(cmd, cwd=wd, capture_output=True, timeout=60, stdin=subprocess.DEVNULL); out, code, err = r.stdout.decode("utf-8", "replace"), r.returncode, r.stderr.decode("utf-8", "replace")
        except subprocess.TimeoutExpired: out, code, err = "", "timeout", ""
        ok = out == want and code == 0
        if not ok: fails += 1
        rows.append(dict(name=name, verdict="一致" if ok else "食い違い", note="libsqlite3 で表・束縛・読み・小数・エラー・ファイルが処理系と同じか", stdout=out, exit=code, stderr=err.strip()[:300], seconds=round(time.time() - t0, 2), fake_kernel_expected=want, hint="" if ok else "sign_db.c の移植(エラー番号・小数の文字列)か、リンク(-no-pie・0x10000000)・作業メモリの確保"))
json.dump(dict(env=env, results=rows), open(os.path.join(HERE, "report.json"), "w"), ensure_ascii=False, indent=1)
with open(os.path.join(HERE, "report.md"), "w", encoding="utf-8") as f:
    f.write("# 実機との食い違い洗い出し\n\n")
    for k, v in env.items(): f.write("- %s: %s\n" % (k, v))
    f.write("\n| プログラム | 判定 | 実機の出力 | 疑似カーネルの予想 | 備考 |\n|---|---|---|---|---|\n")
    for r in rows: f.write("| %s | %s | `%s` | `%s` | %s%s |\n" % (r["name"], r["verdict"], r["stdout"].strip()[:40].replace("|", "/").replace("\n", "\\n"), (r["fake_kernel_expected"] or "").strip()[:40].replace("|", "/").replace("\n", "\\n"), r["note"], (" → 見立て: " + r["hint"]) if r["hint"] else ""))
    f.write("\n食い違い %d 件。trace/ に strace の記録(あれば)。\n" % fails)
print(open(os.path.join(HERE, "report.md"), encoding="utf-8").read())
