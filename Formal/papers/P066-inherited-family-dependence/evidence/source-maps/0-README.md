# Inherited-family dependence can reverse an equal-exposure treatment decision

LaTeX source package for the manuscript. The compiled PDF is
`../Inherited_Family_Dependence_Treatment_Decisions.pdf`.

## Contents

| File | Purpose |
|---|---|
| `main.tex` | Complete manuscript, self-contained (`thebibliography`, no `.bib`) |
| `figures/source.pdf`, `figures/decision.pdf` | The two figures, as included by `main.tex` |
| `figures/*.png` | Raster previews, not used by the build |
| `figures.py` | Regenerates both figures from the preserved certificates |
| `verify_claims.py` | Replays every printed numerical claim |

## Build

Two passes are needed for cross-references. With MiKTeX:

```bash
"$LOCALAPPDATA/Programs/MiKTeX/miktex/bin/x64/pdflatex.exe" -interaction=nonstopmode -halt-on-error main.tex
```

Run it twice, then confirm the log is clean:

```bash
grep -icE "undefined|multiply defined|LaTeX Warning|Overfull|Underfull" main.log
```

This must print `0`, and `main.aux` must exist afterwards — a full disk makes
pdflatex drop the aux file and silently produce a PDF with broken references.
A bundled `tectonic` binary also builds this source unchanged.

## arXiv upload

Upload only `main.tex` and the two files `figures/source.pdf` and
`figures/decision.pdf`, preserving the `figures/` subdirectory. There is no
`.bib`, so no BibTeX pass is required. The Python scripts and PNGs are for
local regeneration and are not needed by the arXiv build. Check the
arXiv-generated PDF before announcing.

The author, affiliation and acknowledgement fields are deliberately empty
(`\author{}` in `main.tex`).

## Regenerating figures and checking claims

Both scripts read the preserved certificates of the campaign workspace

```
E:\Erdos Problems\problem_workspaces\RAF_cancer_inherited_tolerance_evolutionary_rescue
```

which is the default; pass `--workspace PATH` for another checkout.

```bash
"E:/Erdos Problems/.venv/Scripts/python.exe" figures.py
"E:/Erdos Problems/.venv/Scripts/python.exe" verify_claims.py
```

`verify_claims.py` asserts 45 exact rational checks and prints the
floating-point diagnostics separately with an `[N]` tag. It covers:

* the identity of the two augmented mean operators, offspring normalisation,
  and the mutant fixed point `rho = delta/beta`;
* the clearing weight inequality `A0 w <= -.09 w` and its exact residual;
* the poset structure and all 64 quasi-monotonicity inequalities behind
  Lemma 3.2 (the monotone-cone lemma), for both phases;
* the four central flow intervals, the two endpoint gaps, the curvature
  constant `6912`, the derivative slack `.110592` and the resulting uniform
  derivative bounds;
* the dependence errors, their difference, and the schedule-gap identity;
* the minimax regret enclosure and the founder maximum at 32;
* the exact Riccati reduction of the feedback envelope and the scalar floor;
* the two sharpened continuation radii, `eta <= 3e-5` and `H = 152`, together
  with the fact that `eta = 3.2e-5` and `H = 151` do *not* follow from the
  same bounds.

It does **not** re-run the interval integrator. To recompute the four original
flows from scratch use `experiments/validated.py` in the campaign workspace, or
the workspace's `REPRODUCE.md` driver with `--replay-baseline`.

## What changed relative to the earlier eleven-page version

* **Mechanism restored and strengthened.** Section 3 brings back the
  rare-acquisition expansion, the covariance transport equation and the exact
  finite-amplitude response identity, which the earlier draft omitted. The sign
  of the correction, previously conditional on an unproved monotonicity
  assumption, is now proved: Lemma 3.2 establishes invariance of the monotone
  cone by Nagumo's criterion reduced to a finite exact check (64 rational
  inequalities), and Theorem 3.3 concludes via Harris' correlation inequality
  that the independent approximation is systematically optimistic about
  eradication.
* **Curvature proof expanded.** Lemma 4.2 now writes out both variational ODEs,
  the origin of the factor two, the three uniform bounds and the
  secant/mean-value step in full.
* **Direct misspecification cost leads**; the minimax proposition is retained
  but demoted and given its separate premise.
* **Two sharpened continuation radii.** Residual acquisition improves from
  `eta <= 1e-5` to `3e-5`; finite clearing improves from `H = 162` to `H = 152`
  via a one-sided coupling argument, and the exposure cost ratio is stated
  next to the proposition rather than only in discussion.
* **Timescale and acquisition wording corrected** (integrated division hazard,
  no calendar inference, no per-base mutation comparison).
* **Six verified references** in place of two.
* A third figure panel shows the covariance transport for the two schedules.
