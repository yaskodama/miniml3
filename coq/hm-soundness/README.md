# HM Coq Soundness and Type Safety

This project contains Coq proofs for a small Hindley-Milner-style language.

## Files

- `HMSoundness.v`: inference soundness for an HM-style inference relation.
- `HMTypeSafety.v`: operational type safety for the typed core language, including substitution, progress, and preservation.
- `hm_safety_report.tex`: LaTeX report source.
- `hm_safety_report_ja.tex`: the same report in Japanese.

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
pdflatex -interaction=nonstopmode hm_safety_report.tex     # run twice
lualatex -interaction=nonstopmode hm_safety_report_ja.tex  # run twice
```

Run each twice so the cross-references settle.  The Japanese version needs
LuaLaTeX, which luatexja drives; that is what lets it set the inference rules
with mathpartir exactly as the English one does.  It replaces an earlier
script that drew the pages with Pillow and could only render the rules as
monospaced ASCII.

The generated PDFs are not kept in the repository.

