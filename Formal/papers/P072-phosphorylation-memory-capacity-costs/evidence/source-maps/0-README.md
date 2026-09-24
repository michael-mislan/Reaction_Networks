# Cycle structure, capacity, and resource costs of phosphorylation memory

Sources for `../Cycle_Structure_Capacity_Resource_Costs_Phosphorylation_Memory.pdf`
(33 pages). This paper merges the 21-page workspace manuscript
(`problem_workspaces/RAF_finite_capacity_phosphorylation_memory_arbitrary_order/publication`)
with the supplement/publication guidance of 2026-09-20. Author and affiliation fields are
intentionally blank.

## Files

| File | Content |
|---|---|
| `main.tex` | preamble, abstract, introduction, scope and parameter tables |
| `part1.tex` | Sections 2-4: equilibrium geometry and `C_n <= 2^n`; square balance; exponential lower bound |
| `part2.tex` | Sections 5-7: finite-molecule theorem; crowding and observation; finite driving and robustness |
| `part3.tex` | Sections 8-9: certified three-site example; discussion |
| `appendix.tex` | A: input from the companion paper; B: proof of the action theorem; C: certificates and Lean scope |
| `refs.bib` | bibliography (all DOIs resolved and checked 2026-09-20) |
| `check_paper.py` | read-only exact replay of every finite claim (`--full` adds the original source's sink certificates) |
| `diagnostics.py` | high-precision floating-point diagnostics quoted in Section 8 (not certificates) |
| `make_figures.py` | the three matplotlib figures (Figure 1 is TikZ inside `part1.tex`) |
| `data/` | exact rational certificates copied from the workspace, plus `diagnostics.json` |
| `lean/` | the three Lean 4 algebra modules (copies of `proofs/PhosphorylationMemory/*.lean`) |

## Build

MiKTeX binaries are under `%LOCALAPPDATA%\Programs\MiKTeX\miktex\bin\x64`.

```bash
pdflatex -interaction=nonstopmode main.tex
bibtex main
pdflatex -interaction=nonstopmode main.tex
pdflatex -interaction=nonstopmode main.tex
```

BibTeX reports two harmless "empty author" warnings for the two companion manuscripts. After a
build, confirm that `main.log` has no `LaTeX Warning`, `Overfull` or `undefined` lines.

## Replay

```bash
python check_paper.py          # about 1 minute, 745 checks
python check_paper.py --full   # about 70 s, 776 checks
python diagnostics.py          # about 15 s, writes data/diagnostics.json
python make_figures.py         # needs check_paper_report.json and data/diagnostics.json
```

Dependencies: Python 3.9+, SymPy; mpmath, NumPy and Matplotlib for diagnostics and figures. The
repository environment `E:\Erdos Problems\.venv` has all of them. The Lean files are verified from
the repository root with `scripts/verify_proof.py proofs/PhosphorylationMemory/<Module>.lean`
(re-verified 2026-09-20, exit code 0).

## What changed relative to the 21-page manuscript

* Theorem 1.3 (balanced ceiling) is now a separate theorem; the proofs of the regularity lemma,
  of the degree/index lemmas and of the symmetric lift are written out.
* The exponential lower bound has complete proofs: the rank lemma, the normal-attraction lemma
  (with the left-invariant subspace argument), and the small-parameter step, where genericity
  is obtained from one-dimensional Sard and the slow eigenvalue from an explicit block argument.
* The sequential attainment appendix was replaced by a summary that cites the companion paper
  (`Phosphorylation_Stable_State_Capacity_arxiv`), which contains the corrected full proof; the
  constant `a` and the identity `g(0,0) = -a` in the action theorem now come from its splitting
  law, and the phase coordinate is `z = 2E - 2`, so the equilibria sit exactly at `delta*xi_j`.
* New: root census of the example (exactly seven positive equilibria, three of index -1),
  sharper obstruction (free substrate above 1.49e11, `E_T/S_T < 6.8e-11`, and an accurate
  statement of its scope: enzyme totals are fixed), multichannel packing, passive and
  bounded-gain observation, the common-clock proposition, a composite error bound 0.011,
  Figure 3 (equilibrium curve), scope table and parameter dictionary.
* Overstatements listed in Section S2 of the guidance were removed.
