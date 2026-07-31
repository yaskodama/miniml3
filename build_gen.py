# 生成器 2 つ（mlex, myacc）の本体だけを 1 つのファイルに束ねる。
# この処理系にはモジュールが無いので、連結して使う。
import sys
def build(out, header):
    mlex = open('mlex.mml').read().split('\n')
    myacc = open('myacc.mml').read().split('\n')
    partA = '\n'.join(mlex[0:516])                      # 生成器 + DFA 駆動
    partB = '\n'.join(myacc[34:533]).replace('readHead', 'gReadHead')
    open(out,'w').write(header + partA + '\n\n' + partB + '\n')
    return out
if __name__ == '__main__':
    build(sys.argv[1], open(sys.argv[2]).read() if len(sys.argv)>2 else '')
