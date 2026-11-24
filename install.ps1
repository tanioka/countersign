# Sign の簡単インストーラ(Windows 11)。
#   入れるもの: インタープリタと std.sn だけ(install_manifest.txt)。コンパイラ(--asm)・試験・本は入れない。
#   使い方:  irm https://raw.githubusercontent.com/tanioka/countersign/main/install.ps1 | iex   (入れる)
#            & ([scriptblock]::Create((irm https://raw.githubusercontent.com/tanioka/countersign/main/install.ps1))) -Uninstall   (消す)
#   ファイルで:  powershell -ExecutionPolicy Bypass -File install.ps1               入れる(%LOCALAPPDATA%\Sign に置き、sign コマンドを PATH に足す)
#            powershell -ExecutionPolicy Bypass -File install.ps1 -Uninstall    消す
#            -Prefix フォルダ  -Ref ブランチ名  -NoPath(PATH を触らない)
#   手元にリポジトリがあれば(この install.ps1 の隣に sign.py があれば)それを使い、無ければ GitHub から取る。
param(
  [string]$Prefix = (Join-Path $env:LOCALAPPDATA "Sign"),
  [string]$Ref = "main",
  [switch]$Uninstall,
  [switch]$NoPath
)
$ErrorActionPreference = "Stop"
$Repo = "tanioka/countersign"
$Mark = "REM sign-installer"
$Bin = Join-Path $Prefix "bin"
$Marker = Join-Path $Prefix ".sign-installed"

if ([string]::IsNullOrWhiteSpace($Prefix) -or $Prefix.TrimEnd('\') -eq $env:USERPROFILE.TrimEnd('\') -or $Prefix.Length -le 3) {
  throw "置き場所が危ないので止めます: '$Prefix'"
}

function Remove-FromUserPath([string]$dir) {
  $cur = [Environment]::GetEnvironmentVariable("Path", "User")
  if (-not $cur) { return }
  $parts = $cur.Split(";") | Where-Object { $_ -and ($_.TrimEnd('\') -ne $dir.TrimEnd('\')) }
  [Environment]::SetEnvironmentVariable("Path", ($parts -join ";"), "User")
}

if ($Uninstall) {
  if (Test-Path $Marker) {
    Remove-FromUserPath $Bin
    Remove-Item -Recurse -Force $Prefix
    Write-Host "消しました: $Prefix(PATH からも外しました。開いている端末は閉じて開き直してください)"
  } else {
    Write-Host "$Prefix はこのインストーラが作った物ではないので、触りません"
  }
  return
}

# --- Python 3.12 以上を探す(Microsoft Store の見せかけの python.exe は、実行して確かめて外す) ---
function Test-Python($exe, $pre) {
  try {
    $out = & $exe @pre -c "import sys; print(int(sys.version_info >= (3, 12))); print(sys.executable)" 2>$null
    if ($LASTEXITCODE -eq 0 -and $out -and $out[0] -eq "1") { return $out[1] }
  } catch { }
  return $null
}
$Py = $null
foreach ($cand in @(@("py", @("-3")), @("python3", @()), @("python", @()))) {
  if (Get-Command $cand[0] -ErrorAction SilentlyContinue) {
    $Py = Test-Python $cand[0] $cand[1]
    if ($Py) { break }
  }
}
if (-not $Py) {
  Write-Host "Python 3.12 以上が見つかりません。"
  Write-Host "  winget install Python.Python.3.13   または https://www.python.org/downloads/ から入れてください。"
  throw "Python 3.12 以上が必要です"
}

# --- 元のファイルを用意する ---
$Here = $null
if ($PSCommandPath) { $Here = Split-Path -Parent $PSCommandPath }   # irm | iex では空(ファイルではないため)
$Tmp = $null
if ($Here -and (Test-Path (Join-Path $Here "sign.py")) -and (Test-Path (Join-Path $Here "install_manifest.txt"))) {
  $Src = $Here
  Write-Host "手元のファイルから入れます: $Src"
} else {
  $Tmp = Join-Path ([IO.Path]::GetTempPath()) ("sign-install-" + [Guid]::NewGuid().ToString("N"))
  New-Item -ItemType Directory -Path $Tmp | Out-Null
  $Url = "https://github.com/$Repo/archive/refs/heads/$Ref.zip"
  Write-Host "取ってきます: $Url"
  Invoke-WebRequest -Uri $Url -OutFile (Join-Path $Tmp "src.zip") -UseBasicParsing
  Expand-Archive -Path (Join-Path $Tmp "src.zip") -DestinationPath (Join-Path $Tmp "x")
  $Src = (Get-ChildItem (Join-Path $Tmp "x") -Directory | Select-Object -First 1).FullName
}

try {
  # --- 置く ---
  if ((Test-Path $Prefix) -and -not (Test-Path $Marker) -and (Get-ChildItem $Prefix -Force | Select-Object -First 1)) {
    throw "$Prefix には、このインストーラが作った物ではない中身があります。別の場所を -Prefix で指してください。"
  }
  New-Item -ItemType Directory -Force -Path $Prefix, $Bin | Out-Null
  $n = 0
  foreach ($line in Get-Content (Join-Path $Src "install_manifest.txt") -Encoding UTF8) {
    $f = $line.Trim()
    if (-not $f -or $f.StartsWith("#")) { continue }
    $from = Join-Path $Src $f
    if (-not (Test-Path $from)) { throw "元に $f がありません(install_manifest.txt と合っていません)" }
    Copy-Item $from (Join-Path $Prefix $f) -Force
    $n++
  }
  Set-Content -Path $Marker -Value "installed from $Repo@$Ref" -Encoding ascii

  # sign.cmd: 日本語の .sn を UTF-8 で読むために PYTHONUTF8 を立てる
  $cmd = "@echo off`r`n$Mark`r`nset PYTHONUTF8=1`r`n`"$Py`" `"$(Join-Path $Prefix 'sign.py')`" %*`r`n"
  [IO.File]::WriteAllText((Join-Path $Bin "sign.cmd"), $cmd, [Text.Encoding]::ASCII)
  # ASCII に収まらない道(日本語のユーザー名など)なら、cmd の文字コードに任せず止める
  if ($cmd -match '[^\x00-\x7F]') { throw "インストール先の道に日本語が含まれています。-Prefix で半角英数の場所を指してください(例: C:\Sign)。" }

  # --- 動くか確かめる ---
  $chk = Join-Path ([IO.Path]::GetTempPath()) ("sign-chk-" + [Guid]::NewGuid().ToString("N") + ".sn")
  [IO.File]::WriteAllText($chk, "1 + 2`n", (New-Object Text.UTF8Encoding($false)))
  $got = (& (Join-Path $Bin "sign.cmd") $chk 2>&1 | Out-String).Trim()
  Remove-Item $chk -Force -ErrorAction SilentlyContinue
  if ($got -ne "3") { throw "確かめに失敗しました(1 + 2 が '$got' でした)。$Prefix を見てください。" }

  # --- PATH(利用者の分だけ) ---
  if (-not $NoPath) {
    $cur = [Environment]::GetEnvironmentVariable("Path", "User")
    $has = $cur -and ($cur.Split(";") | Where-Object { $_.TrimEnd('\') -eq $Bin.TrimEnd('\') })
    if (-not $has) {
      [Environment]::SetEnvironmentVariable("Path", ($(if ($cur) { "$cur;" } else { "" }) + $Bin), "User")
      Write-Host "PATH に足しました: $Bin(開いている端末は閉じて開き直すと、sign が使えます)"
    }
  }
  Write-Host "入りました($n ファイル)。実行コマンド: $(Join-Path $Bin 'sign.cmd')"
  Write-Host "  試す: 'echo 1 + 2> t.sn' のあと  sign t.sn"
} finally {
  if ($Tmp -and (Test-Path $Tmp)) { Remove-Item -Recurse -Force $Tmp -ErrorAction SilentlyContinue }
}
