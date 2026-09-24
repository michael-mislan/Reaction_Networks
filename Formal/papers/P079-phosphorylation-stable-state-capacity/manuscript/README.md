# Sharp equilibrium and stable-state capacities of multisite phosphorylation

Sources of `../Sharp_Equilibrium_and_Stable_State_Capacities_Multisite_Phosphorylation.pdf`
(34 pages, prepared 2026-09-20). The author block is intentionally blank.

Main result: for the sequential distributive n-site phosphorylation cycle, for every n >= 1,
the maximal number of positive equilibria in one compatibility class is 2n-1 and the maximal
number of locally asymptotically stable equilibria is n (ceiling includes nonhyperbolic
attractors; attainment by rational data, on an open parameter set).

## Files

| File | Purpose |
|---|---|
| `main.tex`, `part1.tex`, `part2.tex`, `part3.tex`, `refs.bib` | LaTeX sources (Sections 1; 2-4; 5-7; 8-11) |
| `figures/benchmark.pdf`, `figures/deficit.pdf` | Figures, produced by `make_figures.py` |
| `phos_sharp.py` | Exact rational toolkit for the equilibrium construction (shared with the earlier 2n-1 sharpness paper) |
| `phos_capacity.py` | Exact toolkit for the loaded slow matrix, limiting prefix, retuning |
| `check_paper.py` | Replays every formula and number in the paper in exact arithmetic; `--full` extends Proposition 9.1 to n <= 7 (about 45 s) |
| `check_paper_report.json` | Output of the last `--full` run |
| `data/worked_example.json`, `data/operational_certificate.json`, `data/refinement.json` | Exact benchmark data copied from the workspace `publication/data` |
| `lean/` | Lean 4 modules (`PhosphorylationStableCapacity/*` at top level, inherited `PhosphorylationSharpness/*`) and the 2026-09-20 verification receipt |

## Build

```bash
python check_paper.py --full
python make_figures.py
pdflatex main && bibtex main && pdflatex main && pdflatex main
```

MiKTeX binaries: `%LOCALAPPDATA%\Programs\MiKTeX\miktex\bin\x64`. For arXiv, upload
`main.tex part*.tex main.bbl figures/*.pdf` (the `.bbl` is kept next to the sources).
Python: the repository `.venv` (3.11); `check_paper.py` needs only the standard library,
`make_figures.py` needs matplotlib and numpy.

Lean: from the repository root,
`.venv/Scripts/python.exe scripts/verify_proof.py proofs/PhosphorylationStableCapacity/DiagonalAlgebra.lean`
(checks all four capacity modules and their Sharpness imports; Lean v4.30.0, warnings as errors).

## Relation to earlier manuscripts

* Supersedes the 14-page workspace manuscript
  `problem_workspaces/RAF_exact_stable-state_capacity_n-site_phosphorylation_system/Phosphorylation_Stable_State_Capacity.pdf`
  and merges the follow-up material (`publication/FOLLOWUP_PROOFS.md`, `FOLLOWUP_REPORT.md`)
  and the supplemental-information plan of 2026-09-20.
* Reuses, with proofs, the equilibrium construction, interlacing/positivity theorem and
  determinant formula of `../Sharp_Steady_State_Bound_Phosphorylation_arxiv`. It proves the
  first sentence of Conjecture 8.3 of that paper (n stable states for every n), with different
  kinetics; the second sentence (standard kinetics, x_j = j+2) remains open.

## Changes relative to the 14-page manuscript

* Introduction with the exact historical gap; explicit definitions of the three capacities.
* Ceiling: index lemma for degenerate attractors written out; transversality via linearity in
  the rate constants.
* Construction: interlacing lemma stated for repeated roots; explicit admissible range of r
  (r >= 3n/2 at coalescence) replaces "r sufficiently large".
* Determinant formula added; it replaces the qualitative elimination argument, gives
  det J = 0 at coalescence for all kinetics, identifies the even-indexed equilibria as the
  sinks without a degree count, and yields the splitting law with an explicit constant.
* Loaded reduction: full derivation of the mass matrix, of the fast block (detailed balance),
  of the slow Jacobian, and a direct proof that K is singular at coalescence.
* Large-r limit: scaled-inverse lemma with a convergence proof (block elimination) and the two
  exact row identities written out; level potential defined.
* New: Table of the feedback deficit; diagonal Lyapunov matrix and compact-current corollary;
  readout monotonicity and separation-recovery corollary; label corollary.
* New exact witnesses: the ordered design terminates immediately for n <= 7 (t = eps = 1),
  Proposition 9.1 and Example 9.2.
* Benchmark: tables, declared units, and the sharpened recovery certificate
  (worst bound 1.2e9 s -> < 32,918,000 s) with an independent replay of the interval bounds.
* Notation: substrate-total function Phi (not H), path matrix H, mass matrix M in bold,
  inventories Lambda_i, eta = r-u, v reserved for J_m/J(1).
