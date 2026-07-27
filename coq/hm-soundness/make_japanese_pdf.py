import os

from PIL import Image, ImageDraw, ImageFont
from textwrap import wrap

OUT = "hm_safety_report_ja.pdf"


def _pick(candidates, what):
    for path in candidates:
        if os.path.exists(path):
            return path
    raise SystemExit(
        "no font found for %s; tried:\n  %s" % (what, "\n  ".join(candidates)))


# The original paths are Debian's.  Keep them first, then fall back to macOS.
JP_FONT = _pick([
    "/usr/share/fonts/truetype/droid/DroidSansFallbackFull.ttf",
    "/usr/share/fonts/opentype/noto/NotoSansCJK-Regular.ttc",
    "/System/Library/Fonts/ヒラギノ角ゴシック W3.ttc",
    "/System/Library/Fonts/Hiragino Sans GB.ttc",
    "/Library/Fonts/Arial Unicode.ttf",
], "Japanese text")

MONO_FONT = _pick([
    "/usr/share/fonts/truetype/noto/NotoSansMono-Regular.ttf",
    "/usr/share/fonts/truetype/dejavu/DejaVuSansMono.ttf",
    "/System/Library/Fonts/Menlo.ttc",
    "/System/Library/Fonts/Monaco.ttf",
], "monospaced code")

W, H = 1240, 1754  # A4-ish at 150 dpi
M = 90
BG = "white"
INK = (28, 32, 36)
MUTED = (90, 96, 104)
BLUE = (28, 72, 130)
LINE = (210, 216, 224)
CODE_BG = (246, 248, 250)

title_font = ImageFont.truetype(JP_FONT, 48)
h1_font = ImageFont.truetype(JP_FONT, 34)
h2_font = ImageFont.truetype(JP_FONT, 26)
body_font = ImageFont.truetype(JP_FONT, 22)
small_font = ImageFont.truetype(JP_FONT, 18)
code_font = ImageFont.truetype(MONO_FONT, 18)


def wrap_to_width(text, font, max_px):
    """Wrap on measured width, not on a character count.

    textwrap counts characters, but Japanese glyphs are about twice as wide as
    Latin ones, so a fixed character count overflows the page.  Break between
    any two characters when the text is CJK, and only at spaces otherwise.
    """
    def is_cjk(ch):
        o = ord(ch)
        return (0x3000 <= o <= 0x30ff or 0x4e00 <= o <= 0x9fff
                or 0xff00 <= o <= 0xffef)

    out, line = [], ""
    i = 0
    while i < len(text):
        ch = text[i]
        # keep a run of non-CJK, non-space characters together
        if not is_cjk(ch) and ch != " ":
            j = i
            while j < len(text) and not is_cjk(text[j]) and text[j] != " ":
                j += 1
            piece = text[i:j]
        else:
            piece = ch
            j = i + 1
        if line and font.getlength(line + piece) > max_px:
            out.append(line.rstrip())
            line = "" if piece == " " else piece
        else:
            line += piece
        i = j
    if line.strip():
        out.append(line.rstrip())
    return out or [""]


class PDF:
    def __init__(self):
        self.pages = []
        self.new_page()

    def new_page(self):
        self.img = Image.new("RGB", (W, H), BG)
        self.draw = ImageDraw.Draw(self.img)
        self.y = M
        self.pages.append(self.img)

    def ensure(self, need):
        if self.y + need > H - M:
            self.footer()
            self.new_page()

    def footer(self):
        n = len(self.pages)
        self.draw.line((M, H - 62, W - M, H - 62), fill=LINE, width=1)
        self.draw.text((W - M - 80, H - 48), str(n), font=small_font, fill=MUTED)

    def text(self, s, font=body_font, fill=INK, gap=9):
        lines = []
        for para in s.split("\n"):
            if not para:
                lines.append("")
                continue
            lines.extend(wrap_to_width(para, font, W - 2 * M))
        line_h = font.size + gap
        self.ensure(max(1, len(lines)) * line_h + 8)
        for line in lines:
            self.draw.text((M, self.y), line, font=font, fill=fill)
            self.y += line_h
        self.y += 8

    def heading(self, s, level=1):
        font = h1_font if level == 1 else h2_font
        self.ensure(font.size + 38)
        if level == 1 and self.y > M + 10:
            self.y += 12
        self.draw.text((M, self.y), s, font=font, fill=BLUE)
        self.y += font.size + 20

    def code(self, s):
        lines = []
        for line in s.strip("\n").split("\n"):
            if code_font.getlength(line) <= W - 2 * M - 36:
                lines.append(line)
            else:
                lines.extend(wrap(line, 78, break_long_words=False))
        line_h = 24
        box_h = len(lines) * line_h + 28
        self.ensure(box_h + 12)
        self.draw.rounded_rectangle((M, self.y, W - M, self.y + box_h),
                                    radius=8, fill=CODE_BG, outline=LINE)
        y = self.y + 14
        for line in lines:
            self.draw.text((M + 18, y), line, font=code_font, fill=(20, 24, 28))
            y += line_h
        self.y += box_h + 18


pdf = PDF()
d = pdf.draw
d.text((M, pdf.y), "Hindley-Milner 型推論の健全性と型安全性", font=title_font, fill=BLUE)
pdf.y += 70
pdf.text("Coq による形式化と機械検証のレポート。前回の型推論健全性と、今回追加した操作意味論に基づく型安全性をまとめる。")
pdf.text("対象ファイル: HMSoundness.v / HMTypeSafety.v", font=small_font, fill=MUTED)

pdf.heading("1. 目的")
pdf.text("このレポートでは、Hindley-Milner 型システムに関する二つの性質を Coq で証明した。第一に、推論が返した型は宣言的型付けでも正しい、という型推論の健全性である。第二に、閉じた型付き項は値であるか一歩実行でき、実行しても型が保存される、という型安全性である。Coq の記述と対照できるよう、文法と型付け規則を明示し、証明の進み方も具体的に述べる。")

pdf.heading("2. 今回の改訂で直したこと")
pdf.text("以前の版は Hindley-Milner を名乗りながら、その中身を持っていなかった。欠陥は二つある。")
pdf.text("第一に、具体化と一般化が退化していた。inst (Forall xs T) T は scheme の本体をそのまま返し、gen G T (Forall xs T) は側条件なしに任意の変数を量化できた。両方が恒等写像なので、アルゴリズム的関係と宣言的関係は構成子ごとに同型となり、健全性の定理は言い換えに過ぎなかった。")
pdf.text("第二に、型安全性の対象言語に多相性が無かった。型は int と関数型だけで型変数が存在せず、ラムダは型注釈を持ち、let も単相であった。証明されていたのは、単純型付きラムダ計算に let と加算を足したものの型安全性である。")

pdf.heading("3. 型推論の健全性: 文法")
pdf.code("""
e      ::=  x | n | \\x. e | e1 e2 | let x = e1 in e2      式
tau    ::=  int | alpha | tau1 -> tau2                    型
sigma  ::=  forall alpha_bar. tau                         型スキーム
Gamma  ::=  .  |  Gamma, x : sigma                        環境
""")
pdf.text("x と alpha は自然数、alpha_bar はその列である。環境は関数ではなく連想リストにした。下の側条件で使う ftv(Gamma) を計算可能にするためである。")
pdf.text("型の自由変数 ftv は構造に沿って定める。scheme では量化された変数を除き、環境では各 scheme の和をとる。")
pdf.code("""
ftv(int)          = {}
ftv(alpha)        = { alpha }
ftv(t1 -> t2)     = ftv(t1) U ftv(t2)
ftv(forall a_. t) = ftv(t) \\ a_
ftv(Gamma)        = U { ftv(sigma) : x:sigma in Gamma }
""")

pdf.heading("4. 具体化と一般化")
pdf.text("代入 s は型変数を型へ写し、型に準同型に作用する。beta が alpha_bar に属さないとき常に s(beta) = beta であることを、s が alpha_bar の上でのみ作用する、という。")
pdf.code("""
      s は alpha_bar の上でのみ作用する
  ----------------------------------------- Inst
      forall alpha_bar. tau  <=  s(tau)

      alpha_bar かつ ftv(Gamma) = 空
  ----------------------------------------- Gen
      gen(Gamma, tau) ∋ forall alpha_bar. tau
""")
pdf.text("Inst が第一の欠陥の修復である。scheme の本体が実際に置換される。ここから、単相 scheme はただ一つの具体化しか持たないことが従う。これは inst_mono_inv であり、証明は only_on_nil と appT_id から出る。")
pdf.text("Gen が第二の欠陥の修復、すなわち Damas-Milner の側条件である。空回りしていないことは、Gamma = { x0 : alpha7 } のとき gen(Gamma, alpha7) が forall alpha7. alpha7 を含まないこと、つまり導出不能であることで確かめた。以前の定義ではこれが導けた。")
pdf.text("アルゴリズムは Gen が許す自由を持たず、最大一般化に確定する。")
pdf.code("""
gen_max(Gamma, tau) = forall (ftv(tau) \\ ftv(Gamma)). tau
""")

pdf.heading("5. 型推論の健全性: 規則")
pdf.text("宣言的体系の規則は次のとおり。")
pdf.code("""
 Gamma(x) = sigma    sigma <= tau
 -------------------------------- T-Var        --------------- T-Int
        Gamma |- x : tau                       Gamma |- n : int

    Gamma, x:tau1 |- e : tau2
 ------------------------------------ T-Lam
 Gamma |- \\x. e : tau1 -> tau2

 Gamma |- e1 : tau1 -> tau2    Gamma |- e2 : tau1
 ------------------------------------------------ T-App
              Gamma |- e1 e2 : tau2

 Gamma |- e1 : tau1
 gen(Gamma, tau1) ∋ sigma
 Gamma, x:sigma |- e2 : tau2
 ------------------------------------------- T-Let
 Gamma |- let x = e1 in e2 : tau2
""")
pdf.text("アルゴリズム的体系は、let 以外は同じ規則である。let では scheme を選ぶ自由が無く、gen_max に確定する。")
pdf.code("""
 Gamma |-I e1 : tau1
 Gamma, x:gen_max(Gamma,tau1) |-I e2 : tau2
 ------------------------------------------- I-Let
 Gamma |-I let x = e1 in e2 : tau2
""")
pdf.text("T-Let は I-Let が持たない前提を一つ余分に持つ。したがって両者はもはや同じ規則ではなく、健全性には証明すべきことがある。")

pdf.heading("6. 型推論の健全性: 証明の進み方")
pdf.text("定理 hm_infer_sound は、Gamma |-I e : tau ならば Gamma |- e : tau である。証明は Gamma |-I e : tau の導出に関する帰納法で、場合は五つ。")
pdf.text("I-Var と I-Int は即座に終わる。対応する宣言的規則の前提が同じで、具体化の前提はそのまま持ち越されるからである。I-Lam と I-App は帰納法の仮定だけで閉じる。")
pdf.text("働きがあるのは I-Let のみである。帰納法の仮定から Gamma |- e1 : tau1 と Gamma, x:gen_max(Gamma,tau1) |- e2 : tau2 が得られる。T-Let を適用するには、その中央の前提 gen(Gamma,tau1) ∋ gen_max(Gamma,tau1) を供給しなければならない。すなわち、アルゴリズムが量化した変数がすべて本当に ftv(Gamma) に無いことである。これが補題 gen_max_ok である。")
pdf.text("gen_max_ok の証明は次のとおり。量化される列は filter で ftv(tau) から取られている。その要素 a をとると、filter_In より述語が a について成り立つので negb (memb a ftv(Gamma)) = true、negb_true_iff より memb a ftv(Gamma) = false、memb_false_notin より a が ftv(Gamma) に属さない。これがちょうど Gen の側条件である。")
pdf.text("実例として、forall alpha0. alpha0 -> alpha0 が二つの具体化 int -> int と (int -> int) -> (int -> int) を持つことを、代入 [alpha0 := int] と [alpha0 := int -> int] を明示して示した。これを使って let id = \\x. x in (id id) 42 が int 型を持つことを導き、定理で宣言的体系へ移している。左の id は (int -> int) -> (int -> int) で、右の id は int -> int で使われる。単相束縛ではこれが不可能であることも、inst_mono_inv から証明した。")

pdf.heading("7. 型安全性: 文法")
pdf.code("""
t      ::=  x | n | t1 + t2 | \\x. t | t1 t2 | let x = t1 in t2   項
v      ::=  n | \\x. t                                            値
tau    ::=  int | alpha | #i | tau1 -> tau2                       型
sigma  ::=  forall^n. tau                                        スキーム
""")
pdf.text("ラムダは型注釈を持たない。言語は型無しで、関係がそれに型を付ける。実際の HM 体系と同じ形である。")
pdf.text("型変数は二種類ある。alpha は自由型変数 TFree、#i は囲む scheme が束縛する i 番目の変数 TBound、すなわち de Bruijn 指標である。scheme forall^n. tau は tau の中の #0 から #(n-1) を束縛する。")
pdf.text("この二分割が、開発を短く保っている仕掛けである。具体化は #i しか置き換えず、置き換えて入る型には alpha しか現れないので、自由変数が量化子に捕獲されることが原理的に起こらない。新鮮性の側条件も型代入補題も、どこにも必要ない。")
pdf.code("""
open t_ int          = int
open t_ alpha        = alpha
open t_ #i           = tau_i        (i >= n なら #i のまま)
open t_ (t1 -> t2)   = open t_ t1 -> open t_ t2

        |t_| = n
 ----------------------------- Inst
 forall^n. tau  <=  open t_ tau
""")
pdf.text("open [] tau = tau が無条件に成り立つので、単相 scheme forall^0. tau はやはり tau ただ一つの具体化を持つ。")

pdf.heading("8. 型安全性: 規則")
pdf.code("""
 Gamma(x) = sigma   sigma <= tau
 ------------------------------- S-Var        --------------- S-Int
        Gamma |- x : tau                      Gamma |- n : int

 Gamma |- t1 : int   Gamma |- t2 : int
 ------------------------------------- S-Add
       Gamma |- t1 + t2 : int

 Gamma, x:forall^0. tau1 |- t : tau2
 ----------------------------------- S-Lam
 Gamma |- \\x. t : tau1 -> tau2

 Gamma |- t1 : tau1 -> tau2   Gamma |- t2 : tau1
 ----------------------------------------------- S-App
             Gamma |- t1 t2 : tau2

 forall t_. |t_| = n ならば Gamma |- t1 : open t_ tau0
 Gamma, x:forall^n. tau0 |- t2 : tau
 ----------------------------------------------------- S-Let
 Gamma |- let x = t1 in t2 : tau
""")
pdf.text("S-Let は一般化を意味論的に読んだものである。ftv(Gamma) から scheme を計算するのではなく、t1 が scheme の全ての具体化で型付くことを要求し、t2 の中の x の各出現が必要な具体化を選べるようにする。この前提は全称量化された仮定だが、Coq はこれを強正値の出現として受理し、期待どおりの帰納法の仮定を生成する。")
pdf.text("操作意味論は値呼び、左から右である。")
pdf.code("""
 --------------------- E-Add        t1 -> t1'
 n + m -> n+m                ------------------------- E-Add1
                             t1 + t2 -> t1' + t2

 t -> t'                     ------------------------------- E-Beta
 --------------- E-Add2      (\\x. t) v -> t[x := v]
 v + t -> v + t'

 t1 -> t1'                   t -> t'
 ------------------- E-App1  --------------- E-App2
 t1 t2 -> t1' t2             v t -> v t'

 ----------------------------- E-Let
 let x = v in t -> t[x := v]

 t1 -> t1'
 ------------------------------------------- E-Let1
 let x = t1 in t2 -> let x = t1' in t2
""")

pdf.heading("9. 型安全性: 証明の進み方")
pdf.text("環境は自然数から scheme への部分関数なので、必要な四つの事実は一行ずつで済む。extend_eq、extend_neq、extend_shadow、extend_permute であり、いずれも Nat.eqb の場合分けで終わる。その上に context_invariance と weakening が乗り、どちらも型付け導出に関する帰納法である。")
pdf.text("代入補題は scheme に対して述べる。Gamma, x:sigma |- t : tau であり、かつ sigma <= tau' なる全ての tau' について |- v : tau' であるなら、Gamma |- t[x := v] : tau である。v への仮定が、多相束縛でこの補題を働かせている。x が使われうる各具体化で v が型付いていなければならない。")
pdf.text("証明は導出ではなく項 t に関する帰納法で進める。各場合が v への仮定を別の型で使い直せるようにするためである。場合は六つで、議論を担うのは三つ。")
pdf.text("変数の場合。t = x なら extend_eq で束縛が sigma と分かり、型付けの前提が sigma <= tau を与え、v への仮定が |- v : tau を供給する。これを weaken_empty で Gamma へ持ち上げる。t = y かつ y と x が異なるなら、extend_neq で束縛を捨て、S-Var で導出を組み直す。")
pdf.text("ラムダの場合。t = \\y. t' では、y = x のとき代入は止まる。この場合は extend_shadow を使った context_invariance で閉じる。内側の x の束縛が外側を隠すからである。y と x が異なるときは extend_permute で二つの束縛を入れ替え、帰納法の仮定を適用する。")
pdf.text("let の場合。本体については同じ隠蔽と交換の場合分けをする。束縛される式については、S-Let の全称量化された前提を各 t_ で具体化し、その具体化での t1 の帰納法の仮定に渡す。")
pdf.text("標準形の補題は、値であることと型付け導出の両方を inversion して得る。int 型の値は整数リテラル、関数型の値はラムダである。他の組み合わせは、S-Int と S-Lam が異なる型構成子を作ることから反駁される。")

pdf.heading("10. Progress と Preservation")
pdf.text("Progress は、|- t : tau ならば t が値であるか、ある t' へ一歩進むことを述べる。証明は型付け導出に関する帰納法で、環境を空として覚えておく。")
pdf.text("S-Var は空虚である。空環境は束縛を与えないので前提が矛盾する。S-Int と S-Lam は値をそのまま与える。S-Add は、両辺が値なら標準形の補題で整数リテラルになり E-Add が発火し、そうでなければ先に進む方を E-Add1 か E-Add2 で伝播させる。S-App も同じ議論で、canonical_arrow が関数をラムダに変えるので E-Beta が使える。")
pdf.text("S-Let では、t1 についての帰納法の仮定それ自体が t_ について全称量化されているので、使う前に具体化しなければならない。長さが合えば何でもよく、証明では repeat int n を渡している。長さが n であることは repeat_length による。これで、t1 が値なら E-Let が発火し、そうでなければ E-Let1 が伝播する。")
pdf.text("Preservation は、|- t : tau かつ t -> t' ならば |- t' : tau を述べる。証明は step の導出に関する帰納法で、各場合において型付け導出を inversion する。合同規則は帰納法の仮定の周りに同じ規則を組み直すだけである。E-Add は S-Int で閉じる。要点は二つ。")
pdf.text("E-Beta では、S-App と S-Lam を順に inversion して Gamma, x:forall^0. tau1 |- t : tau2 と |- v : tau1 を得る。代入補題は forall^0. tau1 の全ての具体化で v が型付くことを求めるが、inst_mono_inv より具体化は tau1 しかないので、手元の仮定で足りる。")
pdf.text("E-Let では、S-Let を inversion すると、v が forall^n. tau0 の全ての具体化で型付くことと、Gamma, x:forall^n. tau0 |- t2 : tau が、そのまま得られる。これは代入補題の二つの仮定そのものであり、多相の場合が追加の作業なしに閉じる。S-Let を意味論的に述べたことの見返りである。")
pdf.text("E-Let1 では束縛される式が進む。新しい S-Let の前提は、古い前提を各 t_ で具体化し、帰納法の仮定を通して得る。")
pdf.text("実例として、id = \\x. x が forall^1. #0 -> #0 の全ての具体化で型付くことを示した。任意の tau について open [tau] (#0 -> #0) = tau -> tau であり、S-Lam に続いて inst_mono つきの S-Var を使えば |- \\x. x : tau -> tau が一般に導ける。この前提が S-Let を養い、let id = \\x. x in (id id) 42 が int 型を持つことを与える。二つの出現はそれぞれ [int -> int] と [int] で具体化される。前の版の単相体系ではこれは型付かない。")

pdf.heading("11. 一般化の二つの見方")
pdf.text("二つのファイルは一般化を意図的に別の角度から扱っている。HMSoundness.v は構文的で、側条件は alpha_bar が ftv(Gamma) と交わらないこと、量化変数は名前付き、環境は連想リスト、ftv(Gamma) を必要とする。HMTypeSafety.v は意味論的で、条件は全ての具体化で型付くこと、量化変数は de Bruijn 指標、環境は関数、ftv(Gamma) を必要としない。")
pdf.text("意味論的な形は、型代入補題と新鮮性の機構なしに安全性の証明を閉じるための選択である。標準的な定式化ではあるが、構文的な Gen 規則そのものではない。両者を繋ぐこと、すなわち構文的な一般化が意味論的な条件を満たすことの証明は、自然な次の一歩であり、ここでは行っていない。")

pdf.heading("12. 範囲と限界")
pdf.text("これは MiniML 実装の検証ではない。証明されたのは上の二つの体系についてであって、このリポジトリの SML コードとの隔たりは大きい。")
pdf.text("未着手のものは、具体的な単一化アルゴリズムの正しさ、occurs check、principal type、構文的な一般化と意味論的な一般化の橋渡し、再帰、リストと組とパターン照合、そして SML 実装との対応証明である。I-Lam は依然として引数型を推測し、I-App は関数が既に矢印型であることを前提にする。これは単一化が成功したときに得られる形である。とりわけ MiniML の中核は let rec であるが、どちらのファイルにも再帰は無いので、再帰的定義について本証明は何も述べていない。")

pdf.heading("13. 証明が覆っていない反例")
pdf.text("MiniML は比較演算子に forall alpha. alpha * alpha -> bool という型を与えているが、関数値は実行時に比較できない。次は型検査を通ってから失敗する。")
pdf.code("""
## let f x = x;
f : for all 'a, ('a -> 'a) = <fun>
## f = f;
Runtime error: these values cannot be compared.
""")
pdf.text("これは現状の MiniML に対する progress の反例である。どちらの Coq ファイルにも比較演算子は無いので、どちらもこれを排除しない。各ファイルが記述している言語の範囲では、定理は成立している。MiniML を直すには、Standard ML の等価型のような仕組みを入れるか、比較を単相に戻すことになる。")

pdf.heading("14. 検証方法")
pdf.text("Rocq Prover 9.1.0 で以下を実行し、どちらも終了コード 0 で成功した。From Coq が From Stdlib に置き換わった旨の deprecation 警告以外に出力は無い。Admitted も admit も Axiom も無く、38 個の証明はすべて Qed で閉じている。")
pdf.code("""
cd coq/hm-soundness
coqc HMSoundness.v
coqc HMTypeSafety.v
""")
pdf.text("さらに主要な定理について隠れた仮定の有無を監査した。hm_infer_sound、progress、preservation のいずれも Closed under the global context と答えるので、追加公理に依存していない。")

pdf.footer()
pdf.pages[0].save(OUT, "PDF", resolution=150.0, save_all=True, append_images=pdf.pages[1:])
print(OUT)
