from PIL import Image, ImageDraw, ImageFont
from textwrap import wrap

OUT = "hm_safety_report_ja.pdf"
JP_FONT = "/usr/share/fonts/truetype/droid/DroidSansFallbackFull.ttf"
MONO_FONT = "/usr/share/fonts/truetype/noto/NotoSansMono-Regular.ttf"

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

    def text(self, s, font=body_font, fill=INK, width_chars=42, gap=9):
        lines = []
        for para in s.split("\n"):
            if not para:
                lines.append("")
                continue
            lines.extend(wrap(para, width_chars, break_long_words=False))
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
            if len(line) <= 80:
                lines.append(line)
            else:
                lines.extend(wrap(line, 80, break_long_words=False))
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
pdf.text("Coq による形式化と機械検証のレポート。前回の型推論健全性と、今回追加した操作意味論に基づく型安全性をまとめる。", width_chars=39)
pdf.text("対象ファイル: HMSoundness.v / HMTypeSafety.v", font=small_font, fill=MUTED, width_chars=60)

pdf.heading("1. 目的")
pdf.text("このレポートでは、Hindley-Milner 型推論に関する二つの性質を Coq で証明した。第一に、型推論が返した型は宣言的型付けでも正しい、という型推論の健全性である。第二に、閉じた型付き項は値であるか一歩実行でき、実行しても型が保存される、という型安全性である。")

pdf.heading("2. 型推論の健全性")
pdf.text("HMSoundness.v では、変数、整数、ラムダ抽象、関数適用、let を持つ小さな式言語を定義した。型は整数型、型変数、関数型からなる。")
pdf.code("""
Inductive ty : Type :=
| TInt : ty
| TVar : nat -> ty
| TArrow : ty -> ty -> ty.
""")
pdf.text("宣言的型付け関係を has_type、HM 型推論関係を hm_infer として定義した。多相型スキーム、インスタンス化、一般化は関係として抽象化している。したがって、これは単一化アルゴリズムそのものの証明ではなく、推論規則レベルの soundness である。")
pdf.code("""
Theorem hm_infer_sound :
  forall G e T,
    hm_infer G e T ->
    has_type G e T.
""")
pdf.text("意味は、Γ ⊢infer e : T なら Γ ⊢ e : T である。つまり、推論が作った型は宣言的型体系でも受理される。")
pdf.text("サンプルとして、let id = fun x -> x in id 42 が int 型を持つこと、また + : int -> int -> int を仮定して fun x -> x + 1 が int -> int 型を持つことも Coq で確認した。")

pdf.heading("3. 型安全性")
pdf.text("HMTypeSafety.v では、型推論後に得られる単純型付きの核言語を対象にした。言語は整数、加算、ラムダ抽象、関数適用、let を持つ。実行意味論は call-by-value の一ステップ関係 step として定義した。")
pdf.code("""
Inductive value : tm -> Prop :=
| VInt : forall n, value (TIntLit n)
| VLam : forall x T body, value (TLam x T body).
""")
pdf.text("関数適用と let は、閉じた値を変数に代入することで進む。保存定理の鍵は、代入が型を保存するという補題である。")
pdf.code("""
Lemma substitution_preserves_typing :
  forall G x U t v T,
    has_type (extend G x U) t T ->
    has_type empty v U ->
    has_type G (subst x v t) T.
""")
pdf.text("この補題は、型 U を持つ閉じた値 v を、型 U と仮定された変数 x に代入しても、式全体の型 T は保たれる、という内容である。")

pdf.heading("4. Progress")
pdf.text("Progress は、閉じた型付き項が詰まらないことの片側である。すなわち、その項はすでに値であるか、一歩実行できる。")
pdf.code("""
Theorem progress :
  forall t T,
    has_type empty t T ->
    value t \/ exists t', step t t'.
""")

pdf.heading("5. Preservation")
pdf.text("Preservation は、評価が型を壊さないことを述べる。閉じた項 t が型 T を持ち、t が t' に一歩進むなら、t' も同じ型 T を持つ。")
pdf.code("""
Theorem preservation :
  forall t t' T,
    has_type empty t T ->
    step t t' ->
    has_type empty t' T.
""")
pdf.text("Progress と Preservation を合わせることで、閉じた型付きプログラムは値になるか、型を保ったまま実行を続けられる。これが標準的な構文的型安全性である。")

pdf.heading("6. 範囲と限界")
pdf.text("今回の証明は二層構成である。HMSoundness.v は HM 型推論規則が宣言的型付けに対して健全であることを示す。HMTypeSafety.v は、型推論後の単純型付き核言語が操作意味論に対して安全であることを示す。")
pdf.text("まだ含めていないものは、具体的な単一化アルゴリズムの正しさ、occurs check、principal type、MiniML の SML 実装との対応証明である。")

pdf.heading("7. 検証方法")
pdf.text("Coq 8.16.1 で以下を実行し、どちらも成功した。")
pdf.code("""
cd /home/yass/my-coq-project
coqc HMSoundness.v
coqc HMTypeSafety.v
""")

pdf.footer()
pdf.pages[0].save(OUT, "PDF", resolution=150.0, save_all=True, append_images=pdf.pages[1:])
print(OUT)
