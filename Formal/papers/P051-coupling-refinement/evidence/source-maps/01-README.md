# Reliable productive operation of coupled autocatalytic reactors under mechanistic refinement

`main.tex` is the authoritative editable manuscript. Authors and affiliations are intentionally blank.
This is a mathematical research manuscript with a primary-literature introduction, not a review claiming
that all RAF systems satisfy its source-specific operating theorem. No arXiv submission was performed.

## Build the paper

Use a standard pdfLaTeX installation with the packages named in main.tex. No private paths,
shell escape, Python, Lean, or research checkout are needed to compile the manuscript.

```
pdflatex -interaction=nonstopmode -halt-on-error main.tex
bibtex main
pdflatex -interaction=nonstopmode -halt-on-error main.tex
pdflatex -interaction=nonstopmode -halt-on-error main.tex
```

On Windows, `powershell -NoProfile -File build.ps1` runs these passes and fails on any nonzero exit.
The supplied `.bbl` also permits compilation without running BibTeX. The upload archive includes
only `main.tex`, `references.bib`, `main.bbl`, and the three required vector figures.
It follows arXiv's TeX-source guidance: https://info.arxiv.org/help/submit_tex.html.
Supply author metadata, select the license and category, and inspect arXiv's own compiled preview
when submitting. These user-owned publication steps remain separate from preparing the paper.

## Numerical reproduction

Run `reproduce.py` with Python 3.11, NumPy, SciPy and Matplotlib. The delivered plots and CSV files
already exist, so this step is optional for compiling the PDF. In the original repository use:

```
.venv/Scripts/python.exe scripts/smoke_numerics.py
.venv/Scripts/python.exe scripts/process_guard.py run --timeout 180 --owner-label RAF-paper-figures -- "E:/Erdos Problems/.venv/Scripts/python.exe" key_results/RAFs/Reliable_Productive_Operation_arxiv/reproduce.py
```

The script checks finite stoichiometry and rational arithmetic, integrates the literal two-node
seven-species ODE, carries every endpoint (including intermediate) into the next pulse, accumulates
the product and service accounts, and repeats at tighter tolerance. `data/checks.json` reports the
comparison. The script is not a stochastic simulation and does not establish the mission theorem.

## Evidence and scope

Read `PROOF_MAP.md` for exact declarations and evidence distinctions. `provenance/source_audit.json`
records comparison with existing strict receipts. Hash matching establishes receipt freshness only;
the receipt's Lean verification supplies the formal evidence. The original publication target and
all 430 recorded dependency sources matched the saved receipt; the toolchain and lake manifest match.
No Lean files, dependencies, theorem graph or canonical authority records were modified for this paper.

The augmented-inventory balance, nonclosure witness, source estimates used in the conventional
presentation, and service/duration deductions are proved in the manuscript; no new formal root
is claimed for these additions. The full research archive and unrelated chemical-memory results
are excluded from the paper. Supporting source snapshots and original receipts, when needed,
remain in the named original repository workspaces rather than the arXiv upload archive.

## Files

- `main.tex`, `references.bib`, `main.bbl`: editable paper and bibliography.
- `figures/`: vector PDF figures used by LaTeX.
- `reproduce.py`, `data/`: figure generation and numerical data.
- `build.ps1`: portable Windows build wrapper.
- `PROOF_MAP.md`, `provenance/source_audit.json`: scope and source audit.

The final deliverable PDF and source ZIP are also placed in the parent RAF results folder.
