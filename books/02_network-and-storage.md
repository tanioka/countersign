# Sign で作る — ネットワークと保存

Nov 3, 2026 · @たににゃん

## 目次

- はじめに
- 第1章 HTTP で取りに行く
  - レシピ1 ページを取ってくる
- 第2章 MQTT で送る・受ける
  - レシピ2 メッセージを出して、来たメッセージを表示する
- 第3章 SQLite に保存する
  - レシピ3 表を作って、行を入れて、選んで出す
- 第4章 全部つなぐ
  - レシピ4 測って、記録して、送って、命令を聞く
- 付録 実行するコマンドの一覧

## はじめに

この巻は、Sign のプログラムを通信とデータベースにつなぐレシピ集です。『動くレシピ集』の続きですが、単独でも読めます。文法の説明は『Sign入門』に任せ、ここでは動くコードと結果を並べます。

各レシピは「やりたいこと、全コード、実行結果、ひとこと」の順です。コードは実際に動かして結果を取っています。実行は既定のモードで行い、確かめた版は「alpha1 実装 2026-11-06 00:50 JST」です。

コマンドは、bash で打つ形で書いています。確かめたのは Linux の上だけで、Windows や macOS では試していません。

結果の出どころは、入れた印で区別します。

- **【仕様】** 配布された仕様書に書かれている動作です。この巻では、メモリの番地を `#` で書き `@` で読む動作がこれにあたります。
- **【実装】** `sign_interp.py` がそう動くだけで、仕様書に見つからない動作です。別の処理系では同じになるとは限りません。
- **【拡張】** 仕様に無い、この実装に添えた道具です。

この巻の主役は、ほぼすべて【拡張】です。ネットワーク装置、SQLite 装置、`mqtt.sn`、`sqlite.sn`、`std.sn` は、仕様書には出てきません。仕様にある `#` と `@` で装置の番地を読み書きするので、仕組みは仕様の上に載っています。ただし、ほかの処理系で同じ名前の装置が使えるとは限りません。

実機やインターネットでは確かめていません。確かめたパソコンからは外へ通信できなかったので、通信の相手はすべて同じパソコンの中の自作の相手です。練習用の小さな MQTT ブローカー(`iot_broker.py`)と、Python の簡易 Web サーバーを使いました。

印の無い記述は、ゲームやツールのルール、動かして見た結果の説明です。仕様書との一致を示すのは【仕様】の印だけです。Sign の資料は [johnny-shaman/Sign](https://github.com/johnny-shaman/Sign) にあり、仕様書に無い話は [Discussions](https://github.com/johnny-shaman/Sign/discussions) に出てきます。

## 第1章 HTTP で取りに行く

この章は、Web サーバーにページを取りに行きます。HTTP の話をする部品は Sign に無いので、通信の道具(TCP)を踏み台に、HTTP の会話を Sign で書きます。

### レシピ1 ページを取ってくる

**やりたいこと**: Web サーバーの `/` を HTTP/1.0 で取ってきて、返ってきたものをそのまま出します。

練習用に、自分のパソコンで簡易 Web サーバーを立てます。適当なフォルダで `index.html` を作り、次の 2 つを実行します。

```
echo '<h1>hello sign</h1>' > index.html
python3 -m http.server 8081 --bind 127.0.0.1
```

コードは、配布物の `http_get.sn` の先頭の説明を省き、`HOST` と `PORT` をこのサーバーに合わせたものです。

```
`std.sn`@~

HOST : `127.0.0.1`
PORT : 8081
TLS : 0

NET : 0x9900000
HB : 0x600000
REQ : 0x610000
RESP : 0x620000
TMP : 0x605000

`ネットワーク装置を呼ぶ: 番号 n と引数 a〜f を書いて GO を押し、結果(RET)を返す`
net_call : n a b c d e f ? seq9 (NET # n) ((NET + 4) # a) ((NET + 8) # b) ((NET + 12) # c) ((NET + 16) # d) ((NET + 20) # e) ((NET + 24) # f) ((NET + 0x20) # 1) (@(NET + 0x24))

`改行(13 10)を REQ の終わりに足す`
add_crlf : z ? seq4 (TMP # 13) ((TMP + 4) # 10) ((TMP + 8) # 0) (str_cat REQ TMP)
`リクエスト「GET / HTTP/1.0」「Host: ホスト」と空行`
build : z ? seq9 (str_put REQ `GET / HTTP/1.0`) (add_crlf 0) (str_put TMP `Host: `) (str_cat REQ TMP) (str_cat REQ HB) (add_crlf 0) (add_crlf 0) 0 0

`受け取った分を出して、また受け取る。0 以下(相手が閉じた・時間切れ・エラー)で終わる`
pump : h ? pump2 h (net_call 3 h RESP 1000 0 0 0)
pump2 : h n ?
	n < 1 : n
	(show n) : pump h
show : n ? seq2 ((RESP + (4 * n)) # 0) (print_mem RESP)

run : h ?
	h < 0 : seq2 (print `つなげませんでした: エラー `) (println_int h)
	seq4 (build 0) (net_call 2 h REQ (str_len REQ) 0 0 0) (pump h) (net_call 4 h 0 0 0 0 0)

`つないで、TLS が 1 なら暗号化にする(失敗するとエラー番号が h に入って、run が出す)`
open : z ? open2 (net_call 1 HB (str_len HB) PORT 0 0 0)
open2 : h ?
	h < 0 : h
	TLS = 1 : tls h (net_call 13 h HB (str_len HB) 0 0 0)
	h
tls : h r ?
	r < 0 : r
	h

run (seq2 (str_put HB HOST) (open 0))
```

`http_get_local.sn` として保存し、ネットワーク装置を入れて(`--net=local`)実行します。`std.sn` は同じフォルダに置きます。

```
python3 sign_interp.py http_get_local.sn --net=local
```

実行結果は次のとおりです(`Date` と `Last-Modified` の行は実行するたびに違います)。

```
HTTP/1.0 200 OK
Server: SimpleHTTP/0.6 Python/3.13.16
Date: Mon, 02 Nov 2026 15:28:40 GMT
Content-type: text/html
Content-Length: 20
Last-Modified: Mon, 02 Nov 2026 15:28:38 GMT

<h1>hello sign</h1>
0
```

**ひとこと**: ネットワーク装置は、メモリの番地 `0x9900000` から始まる「窓口」です【拡張】。命令の番号と引数を書いて、`0x20` バイト目(窓口の先頭からの位置)に `1` を書くと呼び出しが始まり、結果は `0x24` バイト目から読まれます【拡張】。`net_call` はその手順を 1 つの関数にしたものです。`#` と `@` は仕様にある演算子です【仕様】。命令の番号は、`1` がつなぐ、`2` が送る、`3` が受け取る、`4` が閉じる、`13` が暗号化(TLS)の開始です【拡張】。結果が負の数ならエラーです【拡張】。

最後の `0` は、プログラムの最後の式の値です。『動くレシピ集』のレシピ1の「最後の `0`」と同じです。

HTTP の解釈はしていません。ヘッダーも本文も、届いた順にそのまま出しています。`HTTP/1.0` で要求しているのは、このとき相手が返事の後に接続を閉じるので、`pump` が「ここで終わり」を判断できるからです。待ち時間は 1000 ミリ秒です。

### うまくいかないとき

次の 3 つを確かめました。エラー番号は、【拡張】の装置が返すものです。

| やったこと | 結果 |
| --- | --- |
| `--net=local` を付けない | 何も起きず、`__` とだけ出ました【実装】 |
| サーバーが待っていない番号につなぐ | `つなげませんでした: エラー -111` |
| 許可していない相手(`--net=example.com` で `127.0.0.1` を試す) | `つなげませんでした: エラー -13` |

`--net` は「どこへつないでよいか」を宣言するオプションです。`--net=local` は自分のパソコンだけ、`--net=名前` は並べた相手だけを許します【拡張】。

### 暗号化とプロキシ

`TLS : 1` と `PORT : 443` にすると https になります。証明書はすべて確認し、「確認しない」設定はありません。社内の認証局などは `--net-ca=ファイル.pem` で足し、プロキシ越しは `--net-proxy=http://プロキシ:8080` (`socks5://` も)です【拡張】。このうち実際に確かめたのは、自作の試験用の TLS サーバーとプロキシに対する動作だけです。本物の https サイトと本物のプロキシでは確かめていません。

## 第2章 MQTT で送る・受ける

MQTT は、センサーの値などを小さなメッセージでやりとりする仕組みです。ブローカーという中継役を置き、送る側は「トピック」という名前でメッセージを出し、受ける側はトピックを購読します。この章の `mqtt.sn` は、MQTT 3.1.1 のクライアントを Sign で書いたものです【拡張】。第1章のネットワーク装置の上に載っているので、`--net` が要ります。

### レシピ2 メッセージを出して、来たメッセージを表示する

**やりたいこと**: ブローカーにつないで `sign/in` を購読し、`sign/count` に 0 から 4 までを 1 秒おきに出します。`sign/in` に誰かが出したものは、画面に出します。

練習用に、配布物の小さなブローカー `iot_broker.py` を使います。起動して 2 秒後に、`sign/in` へ `hello` を出すように仕込んでおきます。

```
python3 iot_broker.py --inject 2:sign/in:hello
```

コードは、配布物の `mqtt_demo.sn` の先頭の説明を省いたものです。

```
`mqtt.sn`@~

HOST : `127.0.0.1`
PORT : 1883

`つなぐ。ハンドル(負ならエラー)`
tcp : z ? seq2 (str_put 0x600000 HOST) (mq_net 1 0x600000 (str_len 0x600000) PORT 0 0 0)

show_in : r ?
	r = 3 : seq4 (print `受信 `) (print_mem MQ_TOPIC) (print `: `) (println_mem MQ_PAYLOAD)
	0

step : h i ? seq3 (mqtt_publish_int h `sign/count` i 0 0) (show_in (mqtt_poll h 1000)) 0
loop : h i ?
	i >= 5 : 0
	(step h i) : loop h (i + 1)

run : h ?
	h < 0 : seq2 (print `つなげませんでした: エラー `) (println_int h)
	run2 h (mqtt_connect h `sign-demo` 60)
run2 : h rc ?
	(rc < 0) | (rc > 0) : seq2 (print `MQTT に断られました: `) (println_int rc)
	seq4 (mqtt_subscribe h `sign/in` 0) (loop h 0) (mqtt_disconnect h) 0

run (tcp 0)
```

`mqtt_demo_local.sn` として保存し、もう一つの端末で実行します。`std.sn` と `mqtt.sn` は同じフォルダに置きます。

```
python3 sign_interp.py mqtt_demo_local.sn --net=local
```

実行結果は次のとおりです。

```
受信 sign/in: hello
0
```

ブローカーの端末には、出したメッセージが次のように映ります(時刻は実行ごとに少しずれます)。

```
[  0.0] 待っています 127.0.0.1:1883(止めるのは Ctrl+C)
[  1.2] sign/count = 0
[  2.0] (命令) sign/in = hello
[  2.0] sign/count = 1
[  3.0] sign/count = 2
[  4.0] sign/count = 3
[  5.0] sign/count = 4
```

**ひとこと**: `mqtt_publish_int h トピック 整数 QoS 保持` が送る関数、`mqtt_poll h ミリ秒` が「来るのを指定の時間待つ」関数です【拡張】。`mqtt_poll` は、パケットが来ればその種類を返します。メッセージは種類 `3` で、トピックは `MQ_TOPIC`、本文は `MQ_PAYLOAD` というメモリに入ります【拡張】。`show_in` は、`r = 3` のときだけ表示します。『動くレシピ集』で使った「効果を条件に書いた行から次へ」の形(`(step h i) : loop h (i + 1)`)で繰り返しています。

`mqtt_connect` は、成功で `0` を返し、ブローカーに断られると 1 から 5 の数、通信のエラーは負の数を返します【拡張】。`run2` の `(rc < 0) | (rc > 0)` は、どちらでも失敗とみなします。ブローカーを立ち上げずに実行すると、`つなげませんでした: エラー -111` と出ました。

### このクライアントの限度

実際の運用で引っかかりやすい点を、先に書いておきます。すべて【拡張】の制限です。

- QoS は 0 と 1 だけです。QoS 2 を求めると、引数エラーの `-22` を返します。
- 1 つのパケットは 8000 バイトまでです。超えると `-90` を返して、接続を閉じます。
- 生存秒(`mqtt_connect` の最後の引数)を超えて黙っていると、MQTT の決まりでは切られます(長時間は確かめていません)。ただし PING は自動では打ちません。Sign にスレッドや割り込みが無いためで、長く待つときは呼ぶ側が `mqtt_ping` を呼びます。
- 接続や購読の応答を待っている間に届いたメッセージは、応答だけ返して捨てます。
- Will、セッションの引き継ぎ、MQTT 5 はありません。

ユーザー名とパスワードが要るブローカーには `mqtt_connect_auth` を、暗号化した接続(8883 番など)には、つないだあとに第1章の `TLS_START`(番号 13)を呼びます。この 2 つは、試験はしていますが、この章では動かしていません。練習用ブローカーは認証も暗号化も持ちません。本物の Mosquitto などとのやりとりは、確かめていません。

## 第3章 SQLite に保存する

この章は、表を作って行を入れ、条件で選んで読みます。SQLite は Python に最初から付いているデータベースで、第1章のネットワーク装置と同じ形の「窓口」(基点 `0x9A00000`)を通して使います【拡張】。Sign 側の道具は `sqlite.sn` です【拡張】。実行には `--db` が要ります。

### レシピ3 表を作って、行を入れて、選んで出す

**やりたいこと**: 果物の表 `fruit`(名前と個数)を作り、3 行を入れて、個数が 5 より多い行を多い順に出します。ここではメモリ上のデータベースを使うので、ファイルは作られません。

コードは、配布物の `sqlite_demo.sn` の先頭の説明を省いたものです。

```
`sqlite.sn`@~

fail : what ? seq3 (print `error `) (println_int what) what
add : h name qty ? add2 (db_prep h `INSERT INTO fruit(name, qty) VALUES (?, ?)`) name qty
add2 : s name qty ? seq4 (db_bind_text s 1 name) (db_bind_int s 2 qty) (db_step s) (db_done s)
bind5 : s ? seq2 (db_bind_int s 1 5) s
rows : s ?
	(db_step s) = 1 : seq2 (db_print_row s) (rows s)
	0
run : h ? seq6 (db_exec h `CREATE TABLE fruit(id INTEGER PRIMARY KEY, name TEXT NOT NULL UNIQUE, qty INTEGER)`) (add h `apple` 3) (add h `banana` 12) (add h `cherry` 7) (rows (bind5 (db_prep h `SELECT id, name, qty FROM fruit WHERE qty > ? ORDER BY qty DESC`))) (db_close h)
start : h ?
	h < 0 : fail h
	run h
start (db_open `:memory:` 0)
```

`sqlite_demo_local.sn` として保存し、`--db` を付けて実行します。`std.sn` と `sqlite.sn` は同じフォルダに置きます。

```
python3 sign_interp.py sqlite_demo_local.sn --db
```

実行結果は次のとおりです(列はタブで区切られます)。

```
2	banana	12
3	cherry	7
0
```

**ひとこと**: SQL の文は、`db_prep` で一度「準備」してから、`?` の位置に値を結びつけて(`db_bind_int`、`db_bind_text`。位置は 1 から)実行します【拡張】。SQL の文字列を組み立てて値を埋め込むより、こちらが安全です。`db_step s` は、行が読めたとき `1`、もう無いとき `0`、エラーは負の数を返し、`rows` は `1` の間だけ繰り返します【拡張】。`db_print_row` は、今の行をタブ区切りで 1 行に出します【拡張】。Sign の文字列はメモリの番地ではないので、`sqlite.sn` が内部でメモリへ写してから装置に渡しています。この経路で渡せるのは ASCII の文字だけです。日本語を扱うときは、メモリ上の文字列を直接渡す名前の後ろに `_mem` をつけた版を使います【拡張】。この本では日本語のデータは試していません。

### ファイルに残す

`db_open` の名前を `:memory:` から `notes.db` に変えると、ファイルに残ります。ファイルを置くフォルダは `--db=フォルダ` で指し、省くと今のフォルダです【拡張】。

```
python3 sign_interp.py sqlite_demo_local.sn --db=dbd
```

実行結果は同じで、`dbd/notes.db` を Python の `sqlite3` で開くと、中身は次のとおりでした。

```
[(1, 'apple', 3), (2, 'banana', 12), (3, 'cherry', 7)]
```

ファイルは `--db` のフォルダの下だけです。フォルダの外を指す名前(`../x.db` など)を使うと、`db_open` が `-95` を返します【拡張】。`--db` を付けないと何も起きず、`__` とだけ出ました【実装】。

### この見本の落とし穴

ファイルを残した状態でもう一度同じプログラムを実行すると、同じ結果が出て、エラーは何も出ませんでした。表はすでにあり、同じ名前の行は `UNIQUE` で入れられないので、`CREATE TABLE` と 3 回の `INSERT` は失敗していました。この見本は `db_exec` と `add` の結果を見ていないため、失敗を拾いません。表の中身は一度目のままでした。

直すには、表の作成を `CREATE TABLE IF NOT EXISTS` にして「すでにある」を吸収し、行を入れる `db_step` の結果が負のときに `fail` へ渡します。次のように直して(`add2` 以降と `run`)2 回実行すると、一度目は `0` だけ、二度目は制約違反の `-17` が 2 行分出て、表の中身は変わりませんでした。

```
add2 : s name qty ? add3 s (seq3 (db_bind_text s 1 name) (db_bind_int s 2 qty) (db_step s))
add3 : s r ? seq2 (db_done s) (check r)
check : r ?
	r < 0 : fail r
	r
run : h ? seq4 (db_exec h `CREATE TABLE IF NOT EXISTS fruit(id INTEGER PRIMARY KEY, name TEXT NOT NULL UNIQUE, qty INTEGER)`) (add h `apple` 3) (add h `banana` 12) (db_close h)
```

## 第4章 全部つなぐ

この章は、これまでの道具を 1 本のプログラムにつなぎます。センサーで測り、SQLite に記録し、MQTT で送り、MQTT で来た命令で LED を動かします。センサーと LED は『動くレシピ集』の第4章(レシピ10、11)で使ったものです【拡張】。

### レシピ4 測って、記録して、送って、命令を聞く

**やりたいこと**: 1 秒ごとに 6 回、温湿度を測ります。測るたびに `readings` 表へ 1 行足し、MQTT で送ります。温度がしきい値(最初は 30.00 ℃)より高ければ LED を点け、しきい値は MQTT で来た命令で変えられるようにします。

温度と湿度は、小数が無いので 100 倍した整数で持ち、送ります(23.50 ℃ は `2350`)。送るトピックと意味は次のとおりです。

| トピック | 向き | 中身 |
| --- | --- | --- |
| `sign/iot/temp` | 送る | 温度×100 |
| `sign/iot/hum` | 送る | 湿度×100 |
| `sign/iot/led` | 送る | LED の状態(`1` か `0`)。変わったときだけ |
| `sign/iot/cmd/threshold` | 受ける | しきい値(温度×100 の整数。`2000` なら 20.00 ℃) |

練習は、ブローカーを動かす端末と、プログラムを動かす端末の 2 つで行います。ブローカーには、3 秒後にしきい値を 20.00 ℃へ変える命令を出させます。

```
python3 iot_broker.py --inject 3:sign/iot/cmd/threshold:2000
```

コードは、配布物の `iot_demo.sn` の先頭の説明を省いたものです。センサーのドライバ `aht25.sn` も同じフォルダに置きます。

```
`aht25.sn`@~
`sqlite.sn`@~
`mqtt.sn`@~

HOST : `127.0.0.1`
PORT : 1883
CYCLES : 6
PERIOD : 1000
LED_PIN : 17
GPIO : 0x9500000
NOW : 0x9200000
ST : 0x500000
TB : 0x600000

`状態の置き場: ST+0 しきい値(×100)  ST+4 LED の今(0・1。2 = まだ分からない)  ST+8 DB の h  ST+12 MQTT の h`

tcp : z ? seq2 (str_put TB HOST) (mq_net 1 TB (str_len TB) PORT 0 0 0)
say : msg n ? seq3 (print msg) (println_int n) n

`==================== 記録 ====================`
log_add : db ms t hum ? log_add2 (db_prep db `INSERT INTO readings VALUES (?, ?, ?)`) ms t hum
log_add2 : s ms t hum ? seq5 (db_bind_int s 1 ms) (db_bind_int s 2 t) (db_bind_int s 3 hum) (db_step s) (db_done s)
summary : db ? summary2 (db_prep db `SELECT count(*), min(t), max(t) FROM readings`)
summary2 : s ? seq5 (print `記録 件数・最低・最高(×100): `) (db_step s) (db_print_row s) (db_done s) 0

`==================== LED ====================`
led_pin : v ? seq2 ((GPIO + (4 * LED_PIN)) # v) 0
led_pub : v ?
	v = 1 : mqtt_publish (@(ST + 12)) `sign/iot/led` `1` 0 1
	mqtt_publish (@(ST + 12)) `sign/iot/led` `0` 0 1
led_to : v ?
	(@(ST + 4)) = v : 0
	(seq3 ((ST + 4) # v) (led_pin v) (led_pub v)) : 0
led_apply : t ?
	t > (@ST) : led_to 1
	led_to 0

`==================== 命令 ====================`
set_thresh : v ? seq3 (ST # v) (print `しきい値を変えた(×100): `) (println_int v)
on_msg : r ?
	r = 3 : on_cmd (str_put TB `sign/iot/cmd/threshold`)
	0
on_cmd : n ?
	((str_eq MQ_TOPIC TB) = 1) & ((str_is_int MQ_PAYLOAD) = 1) : set_thresh (str_to_int MQ_PAYLOAD)
	0

`次の測定の時刻 until まで MQTT を聞く(来たら処理して、また聞く)`
wait : until ? wait2 until (until - (@NOW))
wait2 : until left ?
	left <= 0 : 0
	wait3 until (mqtt_poll (@(ST + 12)) left)
wait3 : until r ?
	r < 0 : r
	(on_msg r) : wait until

`==================== 測って送る ====================`
publish_all : z ? seq3 (mqtt_publish_int (@(ST + 12)) `sign/iot/temp` (aht25_temp 0) 0 1) (mqtt_publish_int (@(ST + 12)) `sign/iot/hum` (aht25_hum 0) 0 1) 0

step : i ?
	(CYCLES > 0) & (i >= CYCLES) : 0
	step2 i (aht25_measure 0)
step2 : i m ?
	m < 0 : step_err i (say `センサーのエラー: ` m)
	step3 i (@NOW)
step_err : i e ? next i
step3 : i ms ?
	(seq6 (log_add (@(ST + 8)) ms (aht25_temp 0) (aht25_hum 0)) (aht25_show 0) (publish_all 0) (led_apply (aht25_temp 0)) (mqtt_ping (@(ST + 12))) 0) : next i
next : i ? next2 i (wait ((@NOW) + PERIOD))
next2 : i w ?
	w < 0 : say `MQTT のエラー: ` w
	step (i + 1)

`==================== 起動 ====================`
run : z ?
	(ST # 3000) : run1 (tcp 0)
run1 : h ?
	h < 0 : say `ブローカーにつなげません: ` h
	run2 h (mqtt_connect h `sign-iot` 60)
run2 : h rc ?
	(rc < 0) | (rc > 0) : say `MQTT に断られました: ` rc
	run3 h (db_open `iot.db` 0)
run3 : h db ?
	db < 0 : say `データベースが開けません: ` db
	(seq6 ((ST + 12) # h) ((ST + 8) # db) ((ST + 4) # 2) (db_exec db `CREATE TABLE IF NOT EXISTS readings(ms INTEGER, t INTEGER, h INTEGER)`) (mqtt_subscribe h `sign/iot/cmd/#` 0) 0) : run4 h db (aht25_init 0)
run4 : h db r ?
	r < 0 : say `センサーが使えません: ` r
	(seq2 (step 0) 0) : finish h db
finish : h db ? seq4 (summary db) (led_pin 0) (mqtt_disconnect h) (db_close db)

run 0
```

`iot_demo_local.sn` として保存し、模擬のセンサー(温度 23.5、湿度 61)、練習用の GPIO、データベース、ネットワークを付けて実行します。

```
python3 sign_interp.py iot_demo_local.sn --i2c=aht25:23.5,61 --gpio=fake --db --net=local
```

実行結果は次のとおりです。

```
T=23.50 C RH=61.00 %
[gpio] 17 = 0
T=23.50 C RH=61.00 %
しきい値を変えた(×100): 2000
T=23.50 C RH=61.00 %
[gpio] 17 = 1
T=23.50 C RH=61.00 %
T=23.50 C RH=61.00 %
T=23.50 C RH=61.00 %
記録 件数・最低・最高(×100): 6	2350	2350
[gpio] 17 = 0
0
```

ブローカーの端末には、送ったものと命令が次のように映ります(時刻は実行ごとに少しずれます)。

```
[  1.8] sign/iot/temp = 2350
[  1.9] sign/iot/hum = 6100
[  1.9] sign/iot/led = 0
[  3.0] sign/iot/temp = 2350
[  3.0] (命令) sign/iot/cmd/threshold = 2000
[  3.0] sign/iot/hum = 6100
[  4.1] sign/iot/temp = 2350
[  4.1] sign/iot/hum = 6100
[  4.1] sign/iot/led = 1
  …(以降、温度と湿度が 1 秒ごとに続く)
```

記録は `iot.db` に残りました。Python の `sqlite3` で `select count(*), min(t), max(t) from readings` を実行すると、`(6, 2350, 2350)` でした。

**ひとこと**: 23.50 ℃はしきい値の 30.00 ℃より低いので、LED は消えたままです。3 秒後に命令でしきい値が 20.00 ℃になると、次の測定で LED が点き(`[gpio] 17 = 1`)、`sign/iot/led` に `1` が送られます。最後に LED を消して(`[gpio] 17 = 0`)終わります。

次の点が、この本のほかの章にも使える形です。

- **待ち時間を MQTT の受信待ちで兼ねる**: 次の測定までの間は `wait` が `mqtt_poll` で聞き続けるので、命令は次の測定を待たずに反映されます【拡張】。Sign にスレッドや割り込みが無いので、この形にしました。
- **状態をメモリの決まった番地に置く**: しきい値、LED の今の状態、データベースと MQTT のハンドルを `ST` から並べた番地に置きます。関数どうしで引数を持ち回らずに済みます。`#` と `@` は仕様にある演算子です【仕様】。
- **繰り返しは「効果を条件に書いた行から自分を呼ぶ」形で書く**: `step3` の `: next i` がそうです。
- **失敗の扱い**: センサーが測れなかった回は飛ばして次へ進み、MQTT とデータベースの失敗は止めます。

実機の Raspberry Pi、本物のセンサー、本物のブローカーでは動かしていません。`CYCLES` を `0` にして止まるまで回す長時間の運転も、試していません。数回で終わる実行だけを確かめました。

## 付録 実行するコマンドの一覧

この巻のレシピで使った実行方法をまとめました。すべて既定のモードです。ブローカーや Web サーバーは、別の端末で先に起動しておきます。

| レシピ | 先に起動するもの | コマンド |
| --- | --- | --- |
| 1 | `python3 -m http.server 8081 --bind 127.0.0.1` | `python3 sign_interp.py http_get_local.sn --net=local` |
| 2 | `python3 iot_broker.py --inject 2:sign/in:hello` | `python3 sign_interp.py mqtt_demo_local.sn --net=local` |
| 3 | (不要) | `python3 sign_interp.py sqlite_demo_local.sn --db` (ファイルに残すときは `--db=フォルダ`) |
| 4 | `python3 iot_broker.py --inject 3:sign/iot/cmd/threshold:2000` | `python3 sign_interp.py iot_demo_local.sn --i2c=aht25:23.5,61 --gpio=fake --db --net=local` |

共通の約束が 3 つあります。

- `std.sn`、`mqtt.sn`、`sqlite.sn`、`aht25.sn` は、プログラムと同じフォルダに置きます。置かないと読み込めません。
- `--net`、`--db` は、付けないとその装置の番地が無いので、何も起きません。したいことに合わせて必ず付けます。
- 実機で動かすときは、練習用の `--gpio=fake` や `--i2c=aht25:…` を、実機用の `--gpio` と `--i2c` に変え、`HOST` を本物のブローカーに書き換えます【拡張】。この本では実機で確かめていません。
