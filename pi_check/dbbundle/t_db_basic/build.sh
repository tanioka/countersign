#!/bin/sh
# Raspberry Pi 上で:  sudo apt install gcc libsqlite3-dev   のあと   sh build.sh   →  ./prog
# (データベースのファイルは、./prog を起動したフォルダの下に作られる)
set -e
gcc -O2 -nostartfiles -no-pie -Wl,-Ttext-segment=0x10000000 -o prog prog.s sign_db.c -lsqlite3
