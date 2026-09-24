# arXiv manuscript source

`main.tex` + `refs.bib` are the editable source of the arXiv-style paper
*A nontrivial critical window for RAF emergence in the binary polymer model*
(the corrected Hordijk–Steel transition law, Theorem 2.2 / Corollaries 2.3–2.4).

The compiled PDF is copied to `key_results/RAFs/Hordijk_Steel_Critical_Window_arxiv.pdf`.

## Build

MiKTeX (user scope, not on PATH) is at `%LOCALAPPDATA%\Programs\MiKTeX\miktex\bin\x64`.

```powershell
powershell -ExecutionPolicy Bypass -File build.ps1
```

or by hand, in this folder: `pdflatex main`, `bibtex main`, `pdflatex main`, `pdflatex main`.
Keep `main.bbl` next to `main.tex` when uploading to arXiv (arXiv does not run BibTeX).

## Before submission

Fill in the placeholders at the top of `main.tex`:

- `\PaperAuthor`, `\PaperAffiliation`, `\PaperEmail`
- `\RepoURL` (public location of the Lean sources; cited in Appendix B)

## Relationship to the other files in `../`

- `../paper.tex`, `../supplement.tex`, `../manuscript.json` are the earlier, machine-generated
  flat manuscript (rendered through HTML/Chrome, see `../BUILD.md`). `main.tex` is a rewrite of the
  same mathematics as a proper amsart paper with theorem environments, cross-references, a
  BibTeX bibliography, an expanded introduction/discussion, and a Lean concordance appendix.
- `../theorem_concordance.md` and `../verification_manifest.json` are the authoritative
  Lean-side records that Appendix B summarises. If Lean declaration names change, update
  Tables 1–2 in `main.tex` (they use the `\lean{...}` macro, which accepts raw underscores and
  allows line breaks after `.` and `_`).

## Content notes

- Section 2 states the model exactly as in `proofs/RAF/Concrete/*.lean` (split-position reaction
  identities, food = words of length ≤ 2, clamped catalysis parameter).
- The 36-gateway ceiling (Prop. 4.2) and the 68 = |R_4| bound used in the upper transition bound
  (Prop. 10.2) are both retained deliberately; see the remark after Prop. 4.2.
- No new mathematical claims were introduced relative to `../paper.tex`; only exposition,
  literature context, and structure were added.
