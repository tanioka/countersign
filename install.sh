#!/bin/sh
# Sign の簡単インストーラ(Linux・macOS・Raspberry Pi)。
#   入れるもの: インタープリタと std.sn だけ(install_manifest.txt)。コンパイラ(--asm)・試験・本は入れない。
#   使い方:  sh install.sh                 入れる(~/.sign に置き、~/.local/bin/sign を作る)
#            sh install.sh --uninstall     消す
#            sh install.sh --prefix DIR --bin DIR --ref ブランチ名
#   手元にリポジトリがあれば(この install.sh の隣に sign.py があれば)それを使い、無ければ GitHub から取る。
set -eu

REPO=tanioka/countersign
REF=main
PREFIX=${SIGN_PREFIX:-$HOME/.sign}
BIN=${SIGN_BIN:-$HOME/.local/bin}
ACTION=install
MARK="# sign-installer"

usage() { sed -n '2,8p' "$0" | sed 's/^# \{0,1\}//'; }

while [ $# -gt 0 ]; do
  case "$1" in
    --prefix) [ $# -ge 2 ] || { echo "--prefix にはフォルダを書いてください" >&2; exit 2; }; PREFIX=$2; shift 2 ;;
    --bin)    [ $# -ge 2 ] || { echo "--bin にはフォルダを書いてください" >&2; exit 2; }; BIN=$2; shift 2 ;;
    --ref)    [ $# -ge 2 ] || { echo "--ref にはブランチ名を書いてください" >&2; exit 2; }; REF=$2; shift 2 ;;
    --uninstall) ACTION=uninstall; shift ;;
    -h|--help) usage; exit 0 ;;
    *) echo "知らないオプションです: $1" >&2; usage >&2; exit 2 ;;
  esac
done

case "$PREFIX" in ""|/|"$HOME"|"$HOME/") echo "置き場所が危ないので止めます: '$PREFIX'" >&2; exit 2 ;; esac

if [ "$ACTION" = uninstall ]; then
  if [ -f "$BIN/sign" ] && grep -q "$MARK" "$BIN/sign" 2>/dev/null; then rm -f "$BIN/sign"; echo "消しました: $BIN/sign"; fi
  if [ -f "$PREFIX/.sign-installed" ]; then rm -rf "$PREFIX"; echo "消しました: $PREFIX"
  else echo "$PREFIX はこのインストーラが作った物ではないので、触りません"; fi
  exit 0
fi

# --- Python 3.12 以上を探す ---
PY=
for c in python3 python; do
  if command -v "$c" >/dev/null 2>&1 && "$c" -c 'import sys; sys.exit(0 if sys.version_info >= (3, 12) else 1)' 2>/dev/null; then PY=$(command -v "$c"); break; fi
done
if [ -z "$PY" ]; then
  echo "Python 3.12 以上が見つかりません。" >&2
  echo "  Raspberry Pi OS / Debian: sudo apt install python3     macOS: brew install python" >&2
  exit 1
fi

# --- 元のファイルを用意する ---
HERE=$(cd "$(dirname "$0")" 2>/dev/null && pwd || echo .)
TMP=
cleanup() { [ -z "$TMP" ] || rm -rf "$TMP"; }
trap cleanup EXIT
if [ -f "$HERE/sign.py" ] && [ -f "$HERE/install_manifest.txt" ]; then
  SRC=$HERE
  echo "手元のファイルから入れます: $SRC"
else
  TMP=$(mktemp -d)
  URL="https://github.com/$REPO/archive/refs/heads/$REF.tar.gz"
  echo "取ってきます: $URL"
  if command -v curl >/dev/null 2>&1; then curl -fsSL "$URL" -o "$TMP/src.tar.gz"
  elif command -v wget >/dev/null 2>&1; then wget -q "$URL" -O "$TMP/src.tar.gz"
  else echo "curl か wget が要ります" >&2; exit 1; fi
  mkdir "$TMP/src" && tar -xzf "$TMP/src.tar.gz" -C "$TMP/src" --strip-components=1
  SRC=$TMP/src
fi

# --- 置く ---
if [ -e "$PREFIX" ] && [ ! -f "$PREFIX/.sign-installed" ] && [ -n "$(ls -A "$PREFIX" 2>/dev/null)" ]; then
  echo "$PREFIX には、このインストーラが作った物ではない中身があります。別の場所を --prefix で指してください。" >&2; exit 1
fi
mkdir -p "$PREFIX" "$BIN"
n=0
while IFS= read -r f; do
  case "$f" in ""|"#"*) continue ;; esac
  [ -f "$SRC/$f" ] || { echo "元に $f がありません(install_manifest.txt と合っていません)" >&2; exit 1; }
  cp "$SRC/$f" "$PREFIX/$f"; n=$((n + 1))
done < "$SRC/install_manifest.txt"
echo "installed from $REPO@$REF" > "$PREFIX/.sign-installed"

cat > "$BIN/sign" <<LAUNCH
#!/bin/sh
$MARK
PYTHONUTF8=1 exec "$PY" "$PREFIX/sign.py" "\$@"
LAUNCH
chmod +x "$BIN/sign"

# --- 動くか確かめる ---
CHK=$(mktemp -d); printf '1 + 2\n' > "$CHK/t.sn"
GOT=$("$BIN/sign" "$CHK/t.sn" 2>&1 || true); rm -rf "$CHK"
if [ "$GOT" != "3" ]; then echo "確かめに失敗しました(1 + 2 が '$GOT' でした)。$PREFIX を見てください。" >&2; exit 1; fi
echo "入りました($n ファイル、$("$BIN/sign" --version | head -1))。"
echo "  実行コマンド: $BIN/sign"
case ":$PATH:" in *":$BIN:"*) ;; *) echo "  $BIN が PATH にありません。次を ~/.profile に足してください:  export PATH=\"$BIN:\$PATH\"" ;; esac
echo "  試す: echo '1 + 2' > t.sn && sign t.sn"
