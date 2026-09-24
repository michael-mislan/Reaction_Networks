# Build and verification

Manuscript: *Randomized stopped lineage experiments separate phenotypic
switching, selection and correlated inheritance* (20 pages).

## Compile the PDF

```
python build.py
```

Runs `pdflatex`, `bibtex`, `pdflatex` twice and writes `build_manifest.json`
with the PDF hash and any layout or reference warnings. It looks for MiKTeX at
`%LOCALAPPDATA%\Programs\MiKTeX\miktex\bin\x64`, then on `PATH`; override with
the `PDFLATEX` environment variable. A plain `pdflatex main` / `bibtex main` /
`pdflatex main` / `pdflatex main` from this directory works equally well.

The submission root is self-contained: `main.tex`, `refs.bib`, `main.bbl` and
`figures/*.pdf`. No local style files and no absolute paths are used.

## Regenerate the figures

```
python make_figures.py
```

Writes `figures/{assay,inference,extinction,delay}.{pdf,png}` plus the JSON
records `figure_data_inference.json` and `figure_data_extinction.json`. Every
figure is deterministic: fixed seed, fixed rounded expected counts, no
unrecorded random draw.

## Replay every printed number

```
python check_paper.py            # full, ~25 s, includes the 300-repetition diagnostic
python check_paper.py --quick    # skips the Monte Carlo diagnostic
```

86 checks. It regenerates the worked dataset from seed 20260922, audits the
rational logarithm and relative-entropy bounds against a 200-digit reference,
confirms that every Chernoff set lies inside its Hoeffding radius, reproduces
all four rows of Table 2 and their width reductions, re-derives the prospective
budgets, and replays the delay-channel values, the Erlang obstruction and the
extinction effect sizes. Results are written to `check_paper_output.json`.

Exact rational certificates, floating-point ODE and linear-algebra outputs and
Monte Carlo diagnostics are reported separately and never mixed.

## Source files

| File | Contents |
|---|---|
| `model.py` | synthetic two-state source, stopped observation law, branching ODE, dataset simulator |
| `certkit.py` | exact rational intervals, certified logarithm and `kl` bounds, Chernoff sets, the two target evaluators |
| `prospective_boxes.py` | class-level enclosure and the certified separated-class decision |
| `make_figures.py` | the four vector figures |
| `check_paper.py` | full numerical replay |
| `build.py` | LaTeX build |
| `lean_verify.py` | compiles the declared Lean subset and probes its axioms |
| `lean/` | the Lean sources; see `lean_README.md` |

Python 3.11 with `numpy`, `scipy`, `sympy` (for `mpmath`) and `matplotlib`.
Everything runs single-threaded and finishes in seconds.

## Provenance

The worked dataset, the AU565 provenance table, Figures 1, 3 and 4 and the
structural theorems are carried over unchanged from the earlier version of this
work. New in this manuscript: the cancelled-determinant target
(Proposition 4.1), the Chernoff feature sets and their Pinsker relaxation
(Lemma 4.2, Corollary 4.3), the revised interval theorem and worked interval,
the six-category record (Proposition 4.5), the reduced prospective budget, the
normalized-mixture region (Proposition 4.6), known-mixture calibration and
contamination bounds (Section 5), the implementation section for random
deadlines (Section 2.4), and the destructive-readout and well-level discussion
(Section 7.3).
