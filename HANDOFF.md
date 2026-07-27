# 再開のための覚書

このリポジトリで何がどこにあり、どう動かし、何が未解決かをまとめる。
セッションをまたぐときはここから読む。

## リポジトリと作業コピー

| GitHub | 内容 |
|---|---|
| `yaskodama/miniml`  | 1996 年版 `minicaml.sml` と、拡張版 `minicaml2.sml`（Poly/ML） |
| `yaskodama/miniml3` | 同じ言語を ML-Lex / ML-Yacc で作り直した版（MLton）。本リポジトリ |

手元の作業コピー（2026-07-28 時点。四つとも最新）

| 場所 | リポジトリ | 備考 |
|---|---|---|
| `~/miniml`         | miniml  | 最新 |
| `~/miniml3`        | miniml3 | 最新。ここが主な作業場所 |
| `~/seminar/miniml` | miniml  | 最新 |
| `~/seminar/miniml3`| miniml3 | 最新 |

四つとも同期済み。作業場所が分かれているので、触る前に
`git fetch && git status -sb` で確認する習慣にしておくとよい。

## 必要な道具

```sh
brew install polyml     # minicaml2 用
brew install mlton      # miniml3 用（mllex / mlyacc / mlton を同梱）
brew install coq        # 証明の検証。Rocq Prover 9.1.0 が入る
                        # coqc は ~/.opam/5.1.1/bin/coqc にもある。PATH に注意
# LaTeX は texlive。lualatex と mathpartir と luatexja が要る
```

## 動かし方

```sh
cd ~/miniml3
make                    # mllex -> mlyacc -> mlton
./miniml3               # 対話モード。フレーズの終端は ;
./miniml3 samples/01-fizzbuzz.mml
make samples            # samples/ の 10 本

./miniml3 lexer.mml     # 自己記述の字句解析器   検証 12 項目
./miniml3 parser.mml    # 自己記述の構文解析器   検証 13 項目（原文から値まで）
./miniml3 meta.mml      # 自己記述の評価器       検証  9 項目
python3 meta_sample_runner.py   # meta.mml の Python 写し 検証 7 項目

cd coq/hm-soundness
coqc HMSoundness.v      # 型推論の健全性
coqc HMTypeSafety.v     # 多相コアの型安全性
lualatex -interaction=nonstopmode hm_safety_report_ja.tex      # 2 回
pdflatex -interaction=nonstopmode hm_safety_report.tex         # 2 回
lualatex -interaction=nonstopmode survey_mc_typeinference.tex  # 2 回
```

生成物（`miniml3` バイナリ、`*.vo`、`*.pdf` ほか）は `.gitignore` 済み。

## 言語の性質

- 整数は**多倍長**（`IntInf`）。`fac 100` も `2^64-1` も正確
- `mod` は **OCaml 準拠**（剰余の符号は被除数に従う）。ただし `/` は
  **SML の床除算のまま**。負数で `a = (a/b)*b + a mod b` が成り立たない（未修正）
- `=` `<>` `<` `>` `<=` `>=` は多相。構造的に比較する
- 文字列は `size` `sub` `ord` `chr` `explode` `implode` で分解できる
  （字句解析器を自己記述するために追加した。miniml2 にも同じものを入れてある）

## この言語で書くときにぶつかる壁

1. **相互再帰が書けない。** `let rec` は一つの関数しか束縛しない。
   片方を引数で受け取る形に畳む（`meta.mml` の `evargs`、`parser.mml` の `pExpr`）
2. **式を並べる `;` が無い。** 印字を続けるには
   `let u = print_string "..." in ...`。`let _ = ` は名前の位置に識別子が要る
3. **代数的データ型・再帰的型定義が無い。** 構文木は前置記法の平坦なリストで表す
4. **ぶら下がり else** は内側を括弧で囲む
5. コメントの中に `(*` を書くと入れ子が閉じずファイル全体を飲み込む（実際に踏んだ）

## 自己記述の到達点

字句解析器・構文解析器・評価器・表示器は書けた。**型検査器は書けない。**
型を表す再帰的なデータ型が持てないため。閉包も持てないので対象言語は一階。

## 未解決・保留

- **`/` を `Int.quot` にするか。** `mod` だけ OCaml 準拠にしたので恒等式が崩れている
- **`f = f` が型検査を通って実行時に落ちる。** 比較を多相にしたことによる
  progress の反例。等価型（SML の `''a`）を入れるか、比較を単相に戻すか
- **Coq の証明は MiniML 実装の検証ではない。** 単一化アルゴリズム、occurs check、
  principal type、`let rec`、リスト、組、パターン照合、多相比較はいずれも対象外
- 構文的な一般化（`HMSoundness.v`）と意味論的な一般化（`HMTypeSafety.v`）の橋渡し

## 解決済み（再発したら思い出す用）

- `minicaml_fixed9.sml` の `withtype` は 2026-07-28 に修正済み。`withtype` の
  束縛どうしは SML'97 では参照し合えないので、`closure` の中の `environment` を
  `(string * value) list ref` と展開した。これで `run_prolog_sample.sml` が動く。
  同種の誤りは `minicaml2.sml` でも直してある

## miniml リポジトリの Prolog サンプル

`prolog_sample.mml`（109 行）は MiniML で書いた Prolog。単一化、変数の付け替え、
バックトラックを含む SLD 導出が実装されている。

符号化は**すべて整数**。述語 `parent`=1 / `ancestor`=2、定数 `a b c d`=1 2 3 4、
**1000 以上が変数**。ゴールは `(述語, (引数1, 引数2))`。二項述語のみ。

```prolog
parent(a,b).  parent(b,c).  parent(c,d).
ancestor(X,Y) :- parent(X,Y).
ancestor(X,Y) :- parent(X,Z), ancestor(Z,Y).
```

起動は三通り、どれも同じ結果になる。

```sh
cd ~/miniml
echo 'use "run_prolog_sample.sml";' | poly -q    # 本来のドライバ
./minicaml2 prolog_sample.mml                    # make が必要
~/miniml3/miniml3 prolog_sample.mml              # lex/yacc 版
```

自分の問い合わせを立てるには、プログラム定義の部分を残して末尾に足す。
`9000` を置いた引数の答えが返る（第 1 引数でも第 2 引数でもよい）。

```sml
let ask goals = let r = solve (goals,program,nilsubst,1) in
                match r with (false,s)->0-1 | (true,s)->answer_var s;
ask ((1,(1,9000))::[]);      (* parent(a,X)   -> 2 = b *)
ask ((1,(9000,4))::[]);      (* parent(X,d)   -> 3 = c *)
ask ((2,(2,9000))::[]);      (* ancestor(b,X) -> 3 = c *)
```

見つかるのは**最初の解のみ**。全解列挙は未実装。

なお `self_eval_sample.mml` は名前に反して自己評価ではない。番号で関数を選ぶ
だけのディスパッチャで、高階関数の確認用。本物の自己記述は miniml3 側の
`lexer.mml` / `parser.mml` / `meta.mml`。

## 検証の作法

このリポジトリでは、変更のたびに次を確かめてきた。再開後も踏襲されたい。

- サンプル 10 本について `minicaml2` と `miniml3` の出力を **diff で突き合わせる**。
  一致するのが正常。唯一の差は `demo.mml` の構文エラー文言 1 行（診断の作りが違うため）
- 数値の結果は **Python で独立に計算して照合**する
- Coq は `Admitted` / `admit` / `Axiom` が無いことと、
  `Print Assumptions` が `Closed under the global context` を返すことを確認する
- push 後は **GitHub からまっさらに clone してビルドから通す**
