# MINIML3 — ML-Lex / ML-Yacc 版

出自は [yaskodama/miniml](https://github.com/yaskodama/miniml) です。
その `minicaml2.sml` の手書き字句解析器と再帰下降パーザを、**ML-Lex** と
**ML-Yacc** による生成器に置き換えたものです。**文法は変えていません。**
同じプログラムを受理し、同じ型を推論し、同じ値を出します。

## ファイル

| ファイル | 内容 |
|---|---|
| `miniml.lex` | ML-Lex の字句定義。入れ子コメントと文字列は開始状態で処理 |
| `miniml.grm` | ML-Yacc の文法定義。優先順位は非終端記号の層で表現 |
| `absyn.sml` | 抽象構文木（miniml2 と同一） |
| `value.sml` | 値と評価器 |
| `types.sml` | Hindley/Milner の型推論 |
| `show.sml` | 値と型の表示 |
| `prims.sml` | 初期環境（組み込み関数） |
| `main.sml` | 生成された部品を繋ぐ REPL |
| `miniml3.mlb` | MLton のビルド定義 |
| `meta.mml` | MiniML で書いた MiniML の処理系（メタ循環評価器） |

生成される `miniml.lex.sml` / `miniml.grm.{sml,sig,desc}` と実行ファイル
`miniml3` はリポジトリに含めません。`make` で作られます。

## ビルドと実行

```sh
brew install mlton          # mllex, mlyacc, mlton が入る

make                        # miniml3 をビルド
./miniml3                   # 対話モード
./miniml3 samples/01-fizzbuzz.mml
make samples                # samples/ の 10 本をまとめて実行
```

## 構成

```
      miniml.lex  --mllex-->   miniml.lex.sml   (functor MinimlLexFun)
      miniml.grm  --mlyacc-->  miniml.grm.sml   (functor MinimlLrValsFun)
                                     |
                                     v
                    Join (LrParser, MinimlLex, MinimlLrVals)
                                     |
                                     v
                        Absyn.definition  ->  Types  ->  Value
```

`main.sml` が三つを `Join` で束ね、`MinimlParser.parse` を 1 フレーズずつ
呼びます。

## 手書き版との対応

### 優先順位

`%left` / `%right` の宣言には頼らず、非終端記号の層で表現しています。
これで手書き版の再帰下降の構造がそのまま文法規則に写り、同じ結合に
なることが目で確かめられます。結合の弱い順に

```
exp  >  tupexp(,)  >  orexp(||)  >  andexp(&&)  >  cmpexp(= <> < > <= >=)
     >  consexp(::)  >  catexp(^)  >  addexp(+ -)  >  mulexp(* / mod)
     >  appexp(単項 -)  >  appseq(適用)  >  atexp
```

### フレーズの区切り

フレーズの終端 `;` は文法規則に入れず、`%eop EOF SEMI` で受理を
打ち切らせています。角括弧の中の `;` はリストの区切りとして通常どおり
還元されます。ML-Yacc は受理時に先読みの `;` をストリームへ戻すので、
`main.sml` は次の周回の先頭でそれを読み飛ばします。

### 衝突

`mlyacc` が報告する shift/reduce 衝突は 2 件だけで、どちらも

```
cases    : caselist .
caselist : caselist . BAR motif ARROW exp
```

すなわち入れ子の `function` で `|` をどちらの場合分けが取るか、という
ものです。ML-Yacc は shift を選ぶので内側が取ります。手書き版の
`parse_cases` も `|` を貪欲に読むので、同じ解釈になります。

## meta.mml — この言語自身で書いた処理系

`./miniml3 meta.mml` で走ります。前置記法の記号列で表した対象プログラムを
評価する評価器と、それを読める式に戻す逆アセンブラを、MiniML だけで
書いたものです。`fac 100` や `countp 1 1000` などを解釈実行し、同じ計算を
MiniML 直書きでも定義して結果を突き合わせています（9 項目とも一致）。

外側の整数が多倍長なので、メタ評価器の上でも `fac 100` が正確に出ます。
`minicaml2` と `miniml3` のどちらで走らせても出力は完全に一致します。

### 何が書けて、何が書けないか

この言語で処理系を書こうとすると、次の壁に当たります。設計はこれで
決まりました。

* **字句解析器は原理的に書けません。** 文字列に使えるのは `^` と比較だけで、
  `size` も `sub` も `explode` も `ord` もありません。よってプログラムは
  文字列ではなく記号の列として与えます。
* **構文木を木として持てません。** 代数的データ型も再帰的な型定義も無いため、
  前置記法の平坦なリストで表し、節点を `(種別, 名前, 数)` の三つ組に
  しました。この型は再帰的でないので通ります。
* **値に閉包を入れられません。** `value = ... | Clo of code * (string * value) list`
  は再帰的な型だからです。よって対象言語は一階に絞り、関数は大域の
  定義表に置いています。
* **相互再帰が書けません。** `ev` と引数評価 `evargs` は互いを呼ぶので、
  `evargs` が `ev` を引数で受け取る形にしてあります。逆アセンブラの
  `unpargs` も同じです。

結果として、処理系のうち**評価器と表示器は自己記述できましたが、
字句解析器・構文解析器・型検査器は書けません**。前二者は文字列を分解
できないため、型検査器は型を表す再帰的なデータ型が持てないためです。

先へ進めるには `size` / `sub` / `ord` / `chr` あたりのプリミティブを
足すのが最短で、そうすれば字句解析器と、前置記法を吐く構文解析器までは
自己記述に載せられます。閉包の壁は残るので、高階にするにはさらに値の
直列化が要ります。

## 検証

`samples/` の 10 本と `demo.mml` / `newton.mml` / `hanoi.mml` について、
手書き版（[yaskodama/miniml](https://github.com/yaskodama/miniml) の
`minicaml2.sml`）と `miniml3` の出力を突き合わせました。

```
$ ./minicaml2 F > a; ./miniml3 F > b; diff a b
```

**12 本が完全に一致**します。唯一違うのは `demo.mml` に含まれる
わざとの構文エラー 1 行で、診断の文言だけが異なります。

| | 出力 |
|---|---|
| miniml2 | ``Parse error: an expression expected, but found `;'.`` |
| miniml3 | `Parse error: syntax error at line 126.` |

手書き版は「何を期待して何が来たか」を持っていますが、ML-Yacc の
誤り処理は表に基づく修復案を作るしくみで、こちらは修復せず位置だけを
報告しているためです。受理する言語そのものは変わりません。
