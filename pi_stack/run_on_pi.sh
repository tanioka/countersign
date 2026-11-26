#!/bin/sh
# 各プログラムを 8MB のスタックで走らせ、標準出力・標準エラー・終了コードを report.txt に書く
cd "$(dirname "$0")" || exit 1
( echo "# stack check"; uname -m; for b in s_ok s_deep s_branch; do ( ulimit -s 8192; timeout 60 ./bin/$b > /tmp/o.$$ 2> /tmp/e.$$; echo "$b: rc=$? out=$(cat /tmp/o.$$) err=$(cat /tmp/e.$$)" ); done ) | tee report.txt
