# The 2n-1 steady-state bound is sharp for sequential distributive phosphorylation

Source package for the paper. Final PDF: `main.pdf` (copied to
`../Sharp_Steady_State_Bound_Sequential_Distributive_Phosphorylation.pdf`).
Author and affiliation fields are intentionally blank (`\author{}` in `main.tex`).

## Build

MiKTeX binaries: `%LOCALAPPDATA%\Programs\MiKTeX\miktex\bin\x64`.

```bash
pdflatex -interaction=nonstopmode -halt-on-error main.tex
bibtex main
pdflatex -interaction=nonstopmode -halt-on-error main.tex
pdflatex -interaction=nonstopmode -halt-on-error main.tex
```

`main.bbl` is included, so an arXiv upload needs `main.tex`, `main.bbl`, `figures/residuals.pdf`
(plus `refs.bib` optionally). Assert that `main.log` has no `Warning`/`Overfull`/`undefined` lines.

## Files

| File | Role |
|---|---|
| `main.tex`, `refs.bib`, `main.bbl` | manuscript and bibliography (metadata verified against Crossref/arXiv, 2026-09-19) |
| `phos_sharp.py` | exact rational toolkit: recurrence, conversion, literal vector field, Jacobians, Faddeev-LeVerrier, Routh |
| `check_paper.py` | replays every computational statement of the paper (about 3200 checks, 6 s; `--full` extends the Routh census to n <= 10, about 10 min) |
| `check_paper_report.json` | output of the last run |
| `make_figures.py`, `figures/residuals.pdf` | Figure 1 |
| `lean/` | copy of `proofs/PhosphorylationSharpness/*.lean` and the 2026-09-19 verifier receipt (exit 0; axioms propext, Classical.choice, Quot.sound) |
| `qa/` | contact sheets of the rendered pages |

Python: use the repository interpreter `E:/Erdos Problems/.venv/Scripts/python.exe` (matplotlib is
needed only for `make_figures.py`; `check_paper.py` uses the standard library only).

Lean re-verification, from the repository root (do not run `lake update`):

```bash
.venv/Scripts/python.exe scripts/verify_proof.py proofs/PhosphorylationSharpness/Resolution.lean --declaration PhosphorylationSharpness.sharp_lower_bound --timeout 600
```

## What is new relative to the workspace draft (`problem_workspaces/RAF_sharpness_bound_sequential_phosphorylation/publication/paper.tex`)

1. **Interlacing lemma and sharp positivity theorem** (Lemma 4.2, Theorem 4.3). `N = Pi_odd`,
   `J = -(Pi_even+Pi_odd)/2` have real, negative, strictly interlacing roots, so `N/J` has positive
   residues. Consequences: `D_raw` has positive coefficients for every `r>0`; `B_raw` has positive
   coefficients whenever `r > max u_j` and `4r + sqrt(1+8r) >= sum x_j`, and for `r > max u_j`
   positivity of `B_raw` is equivalent to positivity of its leading coefficient. This replaces the
   crude bound (6615 for the n=3 example) and proves the workspace's open "sharper r" hypothesis:
   for `x_j = j+2` every `r > (4n^2-1)/8` works. The crude bound is kept as Appendix A because it
   is the route used by the Lean proof.
2. **Determinant formula** (Proposition 6.2), valid for all rate constants:
   `det J_S = (-1)^(n+1) prod((b_i+c_i) alpha_i gamma_i) F^n u M(u) H'(u)`.
   Gives nondegeneracy iff `H' != 0` and, for all n, instability of the n-1 odd-indexed constructed
   steady states (Theorem 1.5).
3. **Exact Routh census for n <= 10** (Proposition 8.2): n asymptotically stable states and n-1
   saddles with one unstable direction. Conjecture 8.3: this holds for all n.
4. **S_T window** (Proposition 8.1): exactly five steady states for all `S_T` in `[12-1/500, 12+1/500]`.
5. Parametrisation of all steady states and the 3n-dimensional kinetic freedom (Proposition 2.1);
   readout/flux/loading identities (Proposition 7.1); large-r limits (Remark 7.2).
6. Literature corrections: Wang-Sontag conjectured n+1 (not sharpness); the sharpness conjecture is
   attributed via Feliu-Rendall-Wiuf 2020 and Feliu-Kaihnsa-de Wolff-Yuruk 2023 (open beyond n=4);
   Thomson-Gunawardena is numerical evidence; journal metadata for all references.

Not formalised in Lean: items 1-5 above, arbitrary prescribed ratios, rationality, openness, and the
external Wang-Sontag upper bound. The paper's Section 9 states this scope explicitly.
