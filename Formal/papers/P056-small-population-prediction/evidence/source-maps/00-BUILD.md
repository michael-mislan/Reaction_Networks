# Reliable predictions from small cell populations — arXiv source package

Manuscript: *Reliable predictions from small cell populations: preparation
dependence, measurement and certified count bounds*, 17 September 2026,
26 pages, 4 vector figures, 7 tables, 26 references. Author and affiliation
macros (`\PaperAuthor`, `\PaperAffiliation` at the top of `main.tex`) are
intentionally empty.

Built PDF: `../Medical_Reliable_Small_Population_Count_Prediction.pdf`
(identical to `main.pdf` here).

This article integrates the two workspace manuscripts
`problem_workspaces/Medical_Sept16Plan_1_2` (robust endpoint three, empirical
boundary) and `problem_workspaces/Medical_Sept16Plan_3_4_cell_count_diagnostics`
(preparation ambiguity, calibration, detector, rate box) and adds the
conventional results proposed in the 17 September supplementary review
(640-well rule, continuous dependence family, one-sided demographic conditions,
broad birth cap and pure-birth envelopes, unknown-efficiency identification and
feasible-set rule).

## Files

| File | Role |
|---|---|
| `main.tex` | manuscript source (11pt article, natbib numbers, `plainnat`) |
| `references.bib` | classical and biological references (shared with the companion package) |
| `extra_refs.bib` | references specific to this article, including the companion manuscript entry |
| `calibration_rows.tex` | generated macro `\calibrationrows` holding the five rows of Table 2 |
| `figures/cutoffs.pdf` | Figure 1: two-founder CDFs and the continuous family |
| `figures/calibration.pdf` | Figure 2: W error of the two calibration rules |
| `figures/detection.pdf` | Figure 3: thinning gaps and expectation ranges |
| `figures/envelope.pdf` | Figure 4: sufficient demographic envelope |
| `check_paper.py` | recomputes every printed constant and regenerates all figures |
| `results.json` | generated; exact rationals and numerical values kept separate |
| `main.bbl` | generated; include it in an arXiv upload alongside the two `.bib` files |

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

`check_paper.py` needs `numpy`, `scipy`, `sympy`, `mpmath` and `matplotlib`;
the repository virtual environment at `E:\Erdos Problems\.venv` has them. It
runs in well under a minute, asserts 736 named checks, writes `results.json`
and `calibration_rows.tex`, and rewrites the four figures. It exits nonzero on
the first failed check, naming it. Setting the environment variable
`PAPER_PREVIEW_DIR` to a directory also writes PNG previews of the figures
there.

Verify after building that the log is clean and that `main.aux` exists (a full
disk silently drops the aux file and ships `??` references):

```bash
grep -nE "LaTeX Warning|Overfull|Underfull|undefined|Missing|^! " main.log
```

The current build produces no matches.

## What the checker verifies

Exact rational arithmetic: the two-founder mass functions and distribution
functions derived by convolution of the single-founder laws and compared with
the closed forms `F_I(k) = 1 - (k+5)/(4 2^k)` and `F_W(k) = 1 - (k+1)/2^(k+1)`;
the minimal cutoffs six and seven; the total-variation event `{3,4}` with gap
`5/64`; the `m`-founder variances `5m/4` and `m + m^2/4`; the continuous family
formulas and the threshold `rho = 3/5`; the five integer binomial certificates
(1024/607, 1280/759, 4000/2374 for the low-count rule; 576/149, 640/165 for the
counts-3-or-4 rule) by an exact integer recurrence with a `math.comb`
cross-check, plus the exact `e_W`, `e_I` values and their downward-rounded
displays; the Hoeffding constant `exp(125/16) > 2000`; the randomized baseline
and independence formulas; the thinning gap formulas `d^3(2d-1)/(1+d)^4` and
`u^2(1-u)^2/(4(1+u)^2)` from explicit thinned coefficients (with the thinned
fast coefficients verified against their series); the expectations `729/1600`,
`369/800`; the factorial-moment identities `17/2`, `9`, `17/18`; the truncation
remainders `(L+6)/2^(L+1)` and `(L+2)/2^L`; the detector-control gaps for
`[.499,.501]` and `[.49,.51]`; the sixteen-row scalar certificate
`3134312565151423153/3252877056000000000 > .963` and `.952037`; the odd Taylor
lower bounds; the linear birth–death rational bounds `B_4 > .95034241414`
(births `<= .105`) and `B_5 > .95670013878` (pure birth), together with the
symbolic log-derivative `(5mu - 4lam - mu E)/((1-E)(lam - mu E))` (sympy) and
the failure of cutoff four on the pure-birth route; the inherited-state class
constants `L_3`, `B_3`, `r_4`, `B_4`, `.99 B_4`, the minimality witness
`(5/48) sum (c_0/2)^j > 1/20`, the class bounds `Q_S, d_*, Q_R, b_*`, the
all-positive example distances; the empirical identification arithmetic; the
run-level conformal rank and the `59`-unit exact binomial requirement.

Numerical only (labelled as such in the paper and in `results.json`): the
Hoeffding sample size `281067`, the scalar law at the box corner
(`.96642437695`, `.95545795258`, cross-checked against a numerical solution of
the forward equations), `T_0 = 6.93078`, the plotted curves.

## Evidence split

Lean-checked (compiled in the repository's frozen Lean 4.30.0 / mathlib
environment with `-DwarningAsError=true`; receipts in the two workspaces):

- `proofs/MemoryPrediction/`: `chronological_single_observation_equal`,
  `chronological_minimal_endpoints`, `source_cdf_formula`,
  `nested_endpoint_lower`, `upper_endpoint_loss`, `adaptive_prediction_sharp`,
  `classification_error`, `deleted_count_cannot_identify_latent_cutoff`,
  `observed_four`, `source_scalar_lower`, `finite_scalar_certificate`.
  Receipt `postproof_verification.json` (source SHA-256
  `327708862e4a728f97482c2c75209bba459baa25841d14893270a73c2566caa5`, 125 s).
- `proofs/LowFounderPrediction/`: `robust_endpoint_three_budget`,
  `robust_endpoint_three_mixed_budget`, `sharp_constant`,
  `reference_minimum_endpoint`, `preparation_budget`,
  `conditional_coverage_accounting`. Receipt `postproof_verification.json`
  (source SHA-256
  `befaf1560d78745ac286352e446398ab30080d0a702a0852d53a111a34788770`, 199 s).

Conventional (proved in the paper, arithmetic replayed by `check_paper.py`;
no new Lean export was created for this article): general-`k` CDF formula;
many-founder proposition; continuous family and `rho = 3/5`; 1280/1024-well
binomial certificates; 640/576-well rule; `rho` confidence rule; thinning sign
reversal and bounded repair; unknown-`d` identification and feasible-set rule;
one-sided demographic conditions; pathwise domination; `.105` birth cap and
pure-birth envelopes; endpoint four and the confidence allowance; all
statistical statements about the empirical comparison.

## Pitfalls met while building

- `\input` of bare table rows inside `tabular` followed by `\bottomrule` gives
  `Misplaced \noalign`; generate a macro (`\calibrationrows`) instead.
- `\lean{}` (a `\url`-style command) must not appear in captions.
- Matplotlib mathtext rejects `\le`; use `\leq`.
- Fractions must be converted to `mpmath` via numerator/denominator.
- Bash heredocs in this environment mangle `\\`; write patch scripts to files.
