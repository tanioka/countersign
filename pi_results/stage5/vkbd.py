#!/usr/bin/env python3
"""仮想キーボード(/dev/uinput)で、Sign の入力テスト(input_events.sn)にキーを送る。python3 標準だけ。root が要る: sudo python3 vkbd.py
 1. 仮想キーボードを作り、5 秒待つ(その間に別の ssh でテストを走らせる。テストは最初に触れた時に event を開く)
 2. a を押して離し、(1 秒おいて)b、(1 秒おいて)q を送る。q でテストは終わる。
  python3 vkbd.py [待ち秒=5]"""
import os, sys, time, struct, fcntl
UI_SET_EVBIT, UI_SET_KEYBIT, UI_DEV_CREATE, UI_DEV_DESTROY = 0x40045564, 0x40045565, 0x5501, 0x5502
EV_SYN, EV_KEY = 0, 1
fd = os.open("/dev/uinput", os.O_WRONLY | os.O_NONBLOCK)
fcntl.ioctl(fd, UI_SET_EVBIT, EV_KEY); fcntl.ioctl(fd, UI_SET_EVBIT, EV_SYN)
for k in range(1, 120): fcntl.ioctl(fd, UI_SET_KEYBIT, k)
os.write(fd, struct.pack("80sHHHHi" + "i" * 64 * 4, b"sign-vkbd", 3, 0x1234, 0x5678, 1, 0, *([0] * 256)))   # uinput_user_dev
fcntl.ioctl(fd, UI_DEV_CREATE)
def ev(t, c, v): os.write(fd, struct.pack("llHHi", 0, 0, t, c, v))
def key(c):
    for v in (1, 0): ev(EV_KEY, c, v); ev(EV_SYN, 0, 0); time.sleep(0.1)
wait = float(sys.argv[1]) if len(sys.argv) > 1 else 5
print("仮想キーボードを作りました。%g 秒後に a b q を送ります。この間にテストを走らせてください。" % wait, flush=True)
time.sleep(wait)
for c, n in ((30, "a"), (48, "b"), (16, "q")): key(c); print("送った:", n, flush=True); time.sleep(1)
time.sleep(1); fcntl.ioctl(fd, UI_DEV_DESTROY); os.close(fd)
