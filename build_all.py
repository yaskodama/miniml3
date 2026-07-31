# 生成器 2 つを束ねたうえで、各章の本体を後ろに付ける
import build_gen

CCOMP_HDR = '''(* ================================================================
   ccomp.mml -- MiniML で書いた C コンパイラとスタック仮想機械
   実行:  ./miniml3 ccomp.mml

   C の部分集合を、自作の字句解析器生成器と構文解析器生成器で読み、
   スタック仮想機械の命令列へコンパイルする。仮想機械も MiniML で
   書いてあるので、この 1 ファイルで原文から実行結果まで通る。

   扱う C の範囲
     型は int のみ。大域の関数定義、仮引数、局所変数、代入、
     if / else、while、for、return、関数呼出（再帰を含む）、
     算術 + - * / %、比較 < > <= >= == !=、論理 && || !、単項マイナス、
     組込みの print。
   扱わないもの
     ポインタ、配列、構造体、char、float、大域変数、前処理指令。

   命令は (命令名, 整数の引数, 名前) の三つ組。代数的データ型が
   無いので、この形で命令列を平坦なリストとして持つ。
   ================================================================ *)

'''

SELF_HDR = '''(* ================================================================
   selfhost.mml -- 自作の生成器 2 つで MiniML を MiniML の上に作る
   実行:  ./miniml3 selfhost.mml

   この処理系にはモジュールが無いので、mlex.mml と myacc.mml の
   生成器の本体をこのファイルに束ねてある。続けて

     (1) 字句仕様を mlex 部に食わせて DFA の遷移表を作る
     (2) 文法仕様を myacc 部に食わせて LALR(1) の ACTION/GOTO 表を作る
     (3) 生成した 2 つの表で MiniML の原文を読み、前置記法の木にする
     (4) meta.mml の評価器でその木を走らせる

   つまり字句解析器も構文解析器も手で書かず、仕様から生成したもので
   MiniML を動かす。対象言語は meta.mml と同じ一階の部分言語
   （数・変数・算術・比較・論理・単項マイナス・if・let・関数定義と呼出）。
   ================================================================ *)

'''

def cat(out, hdr, tail, extra=''):
    build_gen.build(out, hdr)
    with open(out,'a') as f:
        f.write('\n' + extra + open(tail).read())
    print(out, len(open(out).read().split('\n')), '行')

meta = open('meta.mml').read().split('\n')
partC = '\n'.join(meta[29:167])          # 評価器（meta.mml より）

cat('ccomp.mml', CCOMP_HDR, 'ccomp_tail.mml')
cat('selfhost.mml', SELF_HDR, 'selfhost_tail.mml', partC + '\n')
