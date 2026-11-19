#!/usr/bin/env python3
"""sign.py — Sign の起動口。`python sign.py 〈プログラム〉 [オプション]` は `python sign_interp.py …` と同じ。
sign_interp.py を『読み込み』として使うので、翻訳済みの形(__pycache__)が再利用され、毎回の翻訳(約 0.07 秒)が要らない。"""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sign_interp
sign_interp._cli()
