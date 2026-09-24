# From enzyme activity to functional recovery — arXiv source package

Manuscript: *From enzyme activity to functional recovery: kinetic guarantees,
sharp population bounds and measurement requirements*, 16 September 2026,
24 pages, 3 vector figures, 7 tables, 17 references. Author and affiliation
blocks are intentionally empty.

Built PDF: `../Enzyme_Activity_To_Functional_Recovery.pdf` (identical to
`main.pdf` here).

## Files

| File | Role |
|---|---|
| `main.tex` | manuscript source (11pt article, `plain` bibliography style) |
| `references.bib` | 17 entries, each with DOI and a `note` so DOIs print under `plain` |
| `horizon_rows.tex` | generated macro holding the four rows of the horizon table |
| `figures/identified_intervals.pdf` | Figure 1, the three identified sets |
| `figures/margin_frontier.pdf` | Figure 2, the error/normalization frontier |
| `figures/passage_time.pdf` | Figure 3, first passage time against capacity |
| `check_paper.py` | recomputes every printed constant and regenerates all figures |
| `results.json` | generated; exact values and numerical values kept separate |
| `main.bbl` | generated; include it in an arXiv upload alongside `references.bib` |

## Rebuild

From this directory, with the repository Python and MiKTeX on `PATH`
(`%LOCALAPPDATA%\Programs\MiKTeX\miktex\bin\x64`):

```bash
python check_paper.py
pdflatex -interaction=nonstopmode -halt-on-error main.tex
bibtex main
pdflatex -interaction=nonstopmode -halt-on-error main.tex
pdflatex -interaction=nonstopmode -halt-on-error main.tex
```

`check_paper.py` needs `numpy`, `scipy`, `mpmath` and `matplotlib`; the
repository virtual environment at `E:\Erdos Problems\.venv` has them. It runs in
a few seconds, asserts 146 named checks, writes `results.json` and
`horizon_rows.tex`, and rewrites the three figures. It exits nonzero on the
first failed check, naming it.

Verify after building that the log is clean and that `main.aux` exists:

```bash
grep -nE "LaTeX Warning|Overfull|Underfull|undefined|Missing|^! " main.log
```

The current build produces no matches.

## What the checker verifies

Exact rational arithmetic: the rate shape values `k(0)`, `k(28)`, the drift
margins and `T_0`; the two-band floor `20/41` and the three-atom witness family
at every tested `p`; the repaired interval `[33/49, 4/5]` and all three
calibration branches including the mixture identity; the minimax constants
`61/82 ± 21/82` and `361/490 ± 31/490`; the two-thirds threshold `101/150`, the
budget `1/150` and the margin `1/147`; the weight-conversion endpoints and the
boundary `33/32`; the frontier `(33-32R)/(50(1+2R))` as an equality at the
boundary and a strict inequality inside; the whole of Table 2, including the
observation that the compatible realization `K = 56` is the capacity-one cell;
the 128-interval rectangle sums for Table 3 with outward decimal rounding and
the resulting cutoff bracket `(19/20, 951/1000)`; the `49/424 < inf p < 2/17`
enclosure; the `17`-cell and equal-variance examples; the eventual floor
`197/407` with its witness; the asymptotic pieces `beta = 9/140`, coefficient
`8470/9` and constant `545 + (8470/9) log(81/1960)`; the off-band transition
`(d-1)/(d-c)`; the null-vector identities of Example 7.2; and the closed-form
solution of the Example 8.2 counterexample.

High precision (mpmath, 60 digits): the asymptotic constant to `1e-6`, and the
inverted cutoff asymptotic at `T = 15000` and `T = 30000`. The checker also
asserts that the same asymptotic is *not* yet accurate at `T = 1000`, which is
the caveat stated in the text.

Numerical only (labelled as such in the paper and in `results.json`): the
cutoff decimal `.9506018463`, the infimum `.1163957789`, the four horizon rows,
the plotted curves, and the Hoeffding sample sizes `33702` and `41500`.

## Evidence split

Machine-verified (Lean 4.30.0, warnings as errors, axioms limited to
`Classical.choice`, `Quot.sound`, `propext`): Theorem 4.1 in full, including
solution existence, the classification, both realizability equivalences and the
pooled response-surface identity; Corollary 5.1; the budget, conversion and
`33/32` boundary; Theorem 3.2 with the dual certificate and the coefficient
bijection; the normalization and threshold steps behind (40); and the
coefficient-space identification lemmas. Table 7 of the paper maps each
statement to its declaration and module under `proofs/G6PDReserve/`.

Ordinary proof only, stated as such in the paper and in its Table 6: the
frontier of Proposition 5.3, everything in Section 6 (arbitrary horizons,
connected-support cutoff and nonattainment, deadline dependence, eventual
limit, asymptotics, off-band robustness), the row-span criterion of
Proposition 7.1 as stated for finite-support populations, and the monotone
transfer of Proposition 8.1 with its counterexample.

Not established, and not claimed: any matched biological calibration of the
task, the support, the load, the deadline or the readout; and any joint
statement about simultaneous energy service, peroxide control and whole-cell
restart.

## Content added beyond the earlier 10-page workspace manuscript

The workspace draft is
`problem_workspaces/Medical_Sept16Plan_11_G6PD_activity_and_redox_reserve/publication/main.tex`.
This package keeps its results and adds:

- Section 3, the individual observation-to-recovery chain: reciprocal
  coordinates, the exact secant identity, Theorem 3.2, the worked observation
  design of Table 2, and Remark 3.4 on eventual recovery without a uniform
  deadline. The workspace draft omitted this entirely.
- The identification that the design example's compatible realization is the
  capacity-one cell of the population model, which links the two halves.
- Proposition 5.3, the exact error/normalization frontier, with Figure 2.
- Proposition 6.3, upgrading the earlier qualitative `Theta` statement to an
  asymptotic with the explicit constant `545 + (8470/9) log(81/1960)`, plus the
  honest caveat that its remainder only becomes small at horizons of order
  `3e4`.
- Proposition 6.4, sharp off-band robustness, with its transition at
  `(d-1)/(d-c)` and a full nonattainment argument.
- Section 7, the row-span criterion with proof, and the zero-value second-assay
  example with its null vector.
- Section 8, monotone transfer of the capacity threshold, the two-state
  counterexample showing cooperativity in the state is insufficient, and
  scalar envelopes.
- Remarks 2.1 and 2.2, separating the three senses of reserve and recording why
  the individual and pooled uncertainty levels do not compose.
- Table 1 (notation), Table 5 (analysis record), Table 7 (declaration map), the
  connected-support interval added to Figure 1, and support bands plus the
  `V_infinity` asymptote added to Figure 3.
- Corrected reading of the worked example: the 42/40 population is *excluded*
  by the repaired readout class rather than compatible with it.

## Pitfalls hit while building this

- Bash heredocs eat line-final and escape backslashes. A `python - <<'PY'`
  patch turned `\renewcommand{\topfraction}` into a carriage return plus
  `enewcommand{` plus a tab, which produced `Missing \begin{document}`. Patch
  `.tex` files with the editor or a script written to disk, never through a
  heredoc.
- `read_text()` translates a stray carriage return to `\n`, so the mangled
  fragments did not match a `startswith('\renewcommand')` filter. Repair by
  splicing the byte range between two known anchors.
- MiKTeX's "you have not checked for updates" nag makes `pdflatex` exit
  nonzero even on a successful run. Check `Output written on main.pdf` in the
  log rather than the exit code, and do not chain passes with `&&`.
- Long Lean identifiers in running text overflow the line and cannot be
  hyphenated. They are in a two-column table with ragged-right `p{}` columns
  instead; the same `>{\raggedright\arraybackslash}` treatment removes the
  underfull-box warnings from every `tabularx`.
- The declaration table is nearly a full page and was deferred past the
  bibliography. Fixed with raised `\topfraction`/`\floatpagefraction` and a
  `\clearpage` before `\bibliographystyle`.
- `plain.bst` silently drops `doi` fields; the DOIs are printed through `note`.
- `scipy.integrate.quad` hits roundoff near the passage-time divergence. The
  asymptotic checks use the closed form and mpmath, and mpmath `findroot`
  needs `solver='bisect'` with a loose `tol` for cutoffs within `1e-40` of the
  threshold.
