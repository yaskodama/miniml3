# HM Coq Soundness and Type Safety

This project contains Coq proofs for a small Hindley-Milner-style language.

## Files

- `HMSoundness.v`: inference soundness for an HM-style inference relation.
- `HMTypeSafety.v`: operational type safety for the typed core language, including substitution, progress, and preservation.
- `hm_safety_report.tex`: LaTeX report source.
- `make_japanese_pdf.py`: script used to generate the Japanese PDF without Japanese LaTeX packages.

## Verify

```sh
coqc HMSoundness.v
coqc HMTypeSafety.v
```

Checked with the Rocq Prover 9.1.0; both compile with exit status 0.  The only
output is a deprecation warning for `From Coq`, which recent versions spell
`From Stdlib`.  Neither file contains `Admitted`, `admit` or `Axiom`, and the
main theorems answer `Closed under the global context` to `Print Assumptions`,
so none of them rests on an added axiom.

## Build Report

```sh
pdflatex -interaction=nonstopmode hm_safety_report.tex
python3 make_japanese_pdf.py          # needs Pillow
```

`make_japanese_pdf.py` looks for a font that can draw Japanese, trying the
Debian paths first and then the macOS ones.  It wraps on measured width rather
than on a character count, since Japanese glyphs are about twice as wide as
Latin ones and a fixed count runs off the page.

The generated PDFs are kept locally in this workspace; the GitHub connector used here only creates UTF-8 text files.
