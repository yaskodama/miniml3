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
pdf.text("このレポートでは、Hindley-Milner 型システムに関する二つの性質を Coq で証明した。第一に、型推論が返した型は宣言的型付けでも正しい、という型推論の健全性である。第二に、閉じた型付き項は値であるか一歩実行でき、実行しても型が保存される、という型安全性である。")

pdf.heading("2. 今回の改訂で直したこと")
pdf.text("以前の版は Hindley-Milner を名乗りながら、その中身を持っていなかった。欠陥は二つある。")
pdf.text("第一に、具体化と一般化が退化していた。inst は量化変数を置換せず本体をそのまま返し、gen は側条件なしに任意の変数を量化できた。その結果、推論関係 hm_infer と宣言的関係 has_type は構成子ごとに完全に同型となり、健全性の定理は各構成子を相方に写すだけで成立して、何も述べていなかった。")
pdf.text("第二に、型安全性の対象言語に多相性が無かった。型は整数型と関数型だけで型変数が存在せず、ラムダは型注釈を持ち、let も単相であった。つまり証明されていたのは、単純型付きラムダ計算に let と加算を足したものの型安全性である。")

pdf.heading("3. 型推論の健全性")
pdf.text("具体化を本物の型代入にした。代入 s が xs の外を動かさないことを only_on で表し、具体化はその代入の適用として定義する。")
pdf.code("""
Definition only_on (xs : list nat) (s : tsub) : Prop :=
  forall a, memb a xs = false -> s a = TVar a.

Inductive inst : scheme -> ty -> Prop :=
| Inst : forall xs T s,
    only_on xs s -> inst (Sch xs T) (appT s T).
""")
pdf.text("一般化には Damas-Milner の側条件を入れた。環境に自由に現れる変数は量化できない。環境の自由変数を計算できるよう、環境は連想リストにしてある。")
pdf.code("""
Inductive gen : env -> ty -> scheme -> Prop :=
| Gen : forall G T xs,
    (forall a, In a xs -> ~ In a (ftv_env G)) ->
    gen G T (Sch xs T).
""")
pdf.text("この側条件は空回りしていない。環境が握っている変数の一般化が拒否されることを、次の否定的な補題で確かめた。以前の定義ではこれが導けてしまっていた。")
pdf.code("""
Lemma gen_rejects_env_variable :
  ~ gen [(0, Sch [] (TVar 7))] (TVar 7) (Sch [7] (TVar 7)).
""")
pdf.text("宣言的体系は一般化を関係のまま持ち、側条件を満たす scheme ならどれでも許す。一方アルゴリズムはその自由を持たず、最大一般化 gen_max に確定する。したがって両者はもはや同じ規則ではなく、健全性の証明は、アルゴリズムが計算したものが宣言的体系の要求を満たすことを示す義務を負う。")
pdf.code("""
Lemma gen_max_ok : forall G T, gen G T (gen_max G T).

Theorem hm_infer_sound :
  forall G e T, hm_infer G e T -> has_type G e T.
""")
pdf.text("検証例として、forall a. a -> a という scheme が int -> int と (int -> int) -> (int -> int) という二つの異なる具体化を持つことを、代入を明示して示した。その上で let id = fun x -> x in (id id) 42 が int 型を持つことを証明している。束縛を単相にするとこのプログラムが型付かないことも、あわせて証明した。")

pdf.heading("4. 型安全性")
pdf.text("型に変数を入れ、環境を型スキームに、let を多相にした。量化変数は de Bruijn 指標 TBound とし、自由変数 TFree とは別の構成子にしてある。具体化は TBound しか触らず、代入される型には TBound が現れないので、変数捕獲が構造的に起こり得ない。新鮮性の側条件も型代入補題も不要になり、検証しきれる長さに収まった。")
pdf.code("""
Inductive ty : Type :=
| TInt : ty
| TFree : nat -> ty
| TBound : nat -> ty
| TArrow : ty -> ty -> ty.

Inductive scheme : Type := Sch : nat -> ty -> scheme.
""")
pdf.text("多相 let は、束縛される式が scheme の全ての具体化で型付くことを要求する。束縛変数の各出現は、そのうち好きなものを選べる。")
pdf.code("""
| TyLet : forall G x e1 e2 n T0 T2,
    (forall ts, length ts = n -> has_type G e1 (open ts T0)) ->
    has_type (extend G x (Sch n T0)) e2 T2 ->
    has_type G (TmLet x e1 e2) T2.
""")
pdf.text("代入補題も scheme に対して述べ直した。変数の位置に置く値は、その変数が束縛された scheme の全ての具体化で型付いていなければならない。ラムダ束縛ではこの仮定は一つの型に潰れ、let 束縛では TyLet の第一前提そのものになる。多相の場合が通るのはこのためである。")
pdf.code("""
Lemma substitution_preserves_typing :
  forall t G x Sg v T,
    has_type (extend G x Sg) t T ->
    (forall T', inst Sg T' -> has_type empty v T') ->
    has_type G (subst x v t) T.
""")

pdf.heading("5. Progress と Preservation")
pdf.text("Progress は、閉じた型付き項が詰まらないことを述べる。Preservation は、一歩の評価が型を壊さないことを述べる。二つを合わせて、標準的な構文的型安全性が得られる。")
pdf.code("""
Theorem progress :
  forall t T,
    has_type empty t T -> value t \\/ exists t', step t t'.

Theorem preservation :
  forall t t' T,
    has_type empty t T -> step t t' -> has_type empty t' T.
""")
pdf.text("多相性が本物であることの証拠として、let id = fun x -> x in (id id) 42 がここでも型付くことを証明した。id を (int -> int) -> (int -> int) と int -> int の二つの型で使っている。前の版の単相体系ではこれは型付かないので、拡張は見かけだけのものではない。")

pdf.heading("6. 一般化の二つの見方")
pdf.text("二つのファイルは一般化を意図的に別の角度から扱っている。HMSoundness.v は構文的な Damas-Milner の側条件を使う。HMTypeSafety.v は意味論的な形、すなわち束縛される式が全ての具体化で型付くことを要求する形を使う。後者は型代入補題と新鮮性の機構なしに安全性の証明を閉じるための選択である。標準的な定式化ではあるが、構文的な Gen 規則そのものではない。")

pdf.heading("7. 範囲と限界")
pdf.text("これは MiniML 実装の検証ではない。証明されたのは上の二つの Coq の体系についてであって、このリポジトリの SML コードとの隔たりは大きい。")
pdf.text("未着手のものは、具体的な単一化アルゴリズムの正しさ、occurs check、principal type、構文的な一般化と意味論的な一般化の橋渡し、再帰、リストと組とパターン照合、そして SML 実装との対応証明である。とりわけ MiniML の中核は let rec であるが、どちらのファイルにも再帰は無いので、再帰的定義について本証明は何も述べていない。")

pdf.heading("8. 証明が覆っていない反例")
pdf.text("MiniML は比較演算子に forall a. a * a -> bool という多相型を与えているが、関数値は実行時に比較できない。次は型検査を通ってから失敗する。")
pdf.code("""
## let f x = x;
f : for all 'a, ('a -> 'a) = <fun>
## f = f;
Runtime error: these values cannot be compared.
""")
pdf.text("これは現状の MiniML に対する progress の反例である。どちらの Coq ファイルにも比較演算子は無いので、どちらもこれを排除しない。各ファイルが記述している言語の範囲では、定理は成立している。MiniML を直すには、Standard ML の等価型 ''a のような仕組みを入れるか、比較を単相に戻すことになる。")

pdf.heading("9. 検証方法")
pdf.text("Rocq Prover 9.1.0 で以下を実行し、どちらも終了コード 0 で成功した。From Coq が From Stdlib に置き換わった旨の deprecation 警告以外に出力は無い。Admitted も admit も Axiom も無く、38 個の証明はすべて Qed で閉じている。")
pdf.code("""
cd coq/hm-soundness
coqc HMSoundness.v
coqc HMTypeSafety.v
""")
pdf.text("さらに主要な定理について隠れた仮定の有無を監査した。いずれも Closed under the global context と答えるので、追加公理に依存していない。")
pdf.code("""
Print Assumptions hm_infer_sound.
Print Assumptions progress.
Print Assumptions preservation.
""")

pdf.footer()
pdf.pages[0].save(OUT, "PDF", resolution=150.0, save_all=True, append_images=pdf.pages[1:])
print(OUT)
