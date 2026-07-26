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
| `lexer.mml` | MiniML で書いた MiniML の字句解析器 |
| `parser.mml` | MiniML で書いた MiniML の構文解析器。原文から値まで通す |

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

* **構文木を木として持てません。** 代数的データ型も再帰的な型定義も無いため、
  前置記法の平坦なリストで表し、節点を `(種別, 名前, 数)` の三つ組に
  しました。この型は再帰的でないので通ります。
* **値に閉包を入れられません。** `value = ... | Clo of code * (string * value) list`
  は再帰的な型だからです。よって対象言語は一階に絞り、関数は大域の
  定義表に置いています。
* **相互再帰が書けません。** `ev` と引数評価 `evargs` は互いを呼ぶので、
  `evargs` が `ev` を引数で受け取る形にしてあります。逆アセンブラの
  `unpargs`、字句解析器の各走査部品も同じ方針です。

もう一つ、**文字列を分解できない**という壁がありました。使えるのが `^` と
比較だけだったので、字句解析器が原理的に書けませんでした。これは
`size` / `sub` / `ord` / `chr` / `explode` / `implode` を組み込みに
足して解消してあります（`prims.sml`。miniml2 側にも同じものを入れて
あるので、二つの版は引き続き同じ言語です）。

現在、処理系のうち**字句解析器・構文解析器・評価器・表示器が自己記述
できています**（`lexer.mml` / `parser.mml` / `meta.mml`）。残るのは型検査器
だけで、これは型を表す再帰的なデータ型が持てないため、この言語のままでは
書けません。

## lexer.mml — この言語自身で書いた字句解析器

`./miniml3 lexer.mml` で走ります。プログラムを文字列で受け取り、
`explode` で 1 文字ずつに開いて走査し、記号の列を返します。切り出す
記号は `miniml.lex`（ML-Lex 版）とちょうど同じで、入れ子コメント、
エスケープつきの文字列リテラル、2 文字の演算子、`_` とそれで始まる
識別子の区別、多倍長の整数リテラルを扱います。

記号は `(種別, 文字面, 数)` の三つ組です。

```
  原文 : let rec fac n = if n = 0 then 1 else n * fac (n-1);
  記号 : kw let | kw rec | id fac | id n | op = | kw if | id n | op = |
         num 0 | kw then | num 1 | kw else | id n | op * | id fac |
         op ( | id n | op - | num 1 | op ) | op ;
```

検証は三通りです。期待する記号列を直接書いて突き合わせるもの、記号列を
原文へ戻して再び解析しても同じになるかという往復、そして**記号列から
組み立て直した原文を miniml3 本体に食わせて、元と同じ結果が出るか**。
最後のものが、本物の ML-Lex 版と切り出しが一致していることの裏づけに
なります。

## parser.mml — 原文から値まで、全段を自己記述で

`./miniml3 parser.mml` で走ります。字句解析器・構文解析器・評価器・
表示器を繋ぎ、MiniML の原文を文字列で受け取って値まで通します。

```
  原文（文字列）
    --[ lex ]-->    記号列   (種別, 文字面, 数) のリスト
    --[ parse ]-->  前置記法 (種別, 名前, 数) のリスト
    --[ ev ]-->     値
```

構文解析器は `miniml.grm` と同じ結合・優先順位を実装します。ただし
評価器が一階なので、受理するのは `meta.mml` の対象言語（数・変数・
算術・比較・論理・単項マイナス・`if`・`let`・関数呼び出し）に限ります。

相互再帰が書けないので、式の各段は「最上位の式解析器 `pE`」を引数で
受け取って下へ渡します。`pExpr` だけが自分自身を `pE` として渡し、
輪を閉じます。左結合の二項演算は段ごとに書かず、`pBin` と `pLoop` に
「下の段」と「記号の選択関数」を渡す形にまとめてあります。

```
  let rec fac n = if n = 0 then 1 else n * fac (n-1); fac 100
      ==> 9332621544394415268169923885626670049071596826438162146859296389521759999322991...
```

検証は三通りです。手で書いた前置記法と解析結果が一致するか、
`unparse` で戻した形が期待どおりの結合・優先順位になっているか、
そして原文から得た値が MiniML 直書きの結果と一致するか。13 項目とも
一致します。

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
