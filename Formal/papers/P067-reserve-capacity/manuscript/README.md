# Reserve capacity and reliable eradication in inherited-state populations — TeX source

arXiv-ready source bundle for the merged manuscript. The compiled PDF is
`../Reserve_Capacity_Reliable_Eradication.pdf` (24 pages).

## Layout

```
main.tex                 preamble, abstract, introduction, \input list
certificate_rows.tex     the exact drift/envelope table used by the appendix
references.bib           bibliography (natbib / plainnat)
sections/
  model.tex              source, allocation law, reserve, delivery, uncertainty box
  main_statement.tex     Theorem 4 (delivered finite mission)
  reserve.tex            Theorem 5 (anchored bound), Corollary 6, Theorem 8 (capacity law)
  asymptotics.tex        Proposition 9 (regime converse), Proposition 10 (high-renewal limit)
  mission_proof.tex      proof of Theorem 4; Corollaries 13 and 14
  design_limits.tex      preparation comparison; open converse; limitations
  evidence.tex           evidence classes, formal scope, availability statement
  appendix.tex           finite certificates and source reconstruction
figures/
  delivered_course.pdf       Fig. 2   (reused from the original package)
  capacity_and_filling.pdf   Fig. 3   (reused)
  capacity_design_map.pdf    Fig. 4   (reused)
  high_renewal.pdf           Fig. 1   (new; see below)
  high_renewal.png           raster preview
  high_renewal_data.json     the plotted values, at 60 decimal digits
```

The author/affiliation block in `main.tex` is intentionally empty and must be
filled before release.

## Build

```bash
pdflatex main && bibtex main && pdflatex main && pdflatex main
```

MiKTeX binaries on this machine: `%LOCALAPPDATA%\Programs\MiKTeX\miktex\bin\x64`.
The build is warning-free: no overfull or underfull boxes, no undefined
references or citations. Check `main.log` for `Output written on main.pdf
(24 pages...)` and confirm `main.aux` is written — a full disk silently drops
`main.aux` and produces a PDF with every cross-reference rendered as `??`.

## Figure 1 must be computed in extended precision

`figures/high_renewal.pdf` plots `r_eff^d * P_K(tau_H <= T)` against renewal.
The probabilities fall below `1e-15`, and they are obtained as
`1 - sum_j p_Kj(T)` from a matrix exponential. In double precision that
subtraction loses every significant figure: a float64 run of the same script
reports the `d = 3` curve *exceeding* its own proved upper bound by 3%. The
producer therefore uses `mpmath` at 60 decimal digits, and asserts that the
bound/probability ratio is `> 1` at every plotted point.

## What is and is not mechanically checked

Lean 4.30.0 (`TherapeuticWindows.publication_certificate`, pinned Mathlib)
covers the finite inequalities entering Theorem 4 only. Corollaries 13 and 14
are exact rational evaluations of an already-proved inequality; Propositions 9
and 10 are conventional proofs. Section 9 of the paper states this boundary
explicitly, and it should not be blurred in any release note.
