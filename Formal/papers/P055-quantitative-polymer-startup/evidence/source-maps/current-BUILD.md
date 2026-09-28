# Reliable finite-time output from stochastic autocatalytic reactors — build notes

Output PDF: `..\Reliable_Finite_Time_Output_Stochastic_Autocatalytic_Reactors.pdf` (27 pages), also `main.pdf` here.
Author/affiliation macros (`\PaperAuthor`, `\PaperAffiliation`, `\CompanionAuthor`, `\RepositoryNote`) are at the top of `main.tex` and deliberately blank/placeholder.

This is the merged paper requested in `Reliable_Output_Supplement_and_Merged_Publication_Guidance_2026-09-20.md`. It supersedes, as one canonical dynamic account,

- the 17 September draft `Quantitative_Emergence_Startup_Productive_Reactors_arxiv` (its compiled food-silent theorem is Theorem 3.6 here; its static branching certificates are *not* included and belong with the critical-window work), and
- the 20 September draft `problem_workspaces/RAF_finite_count_startup_random_reactor/paper` (n = 4, V ≥ 5e22).

Neither earlier folder was modified.

## Build

```
powershell -NoProfile -ExecutionPolicy Bypass -File build.ps1
```

Runs `check_paper.py` (exact replay, ~3 s, 222 checks), `make_figures.py`, then pdfLaTeX + BibTeX + 2×pdfLaTeX in a fresh `_build_*` subfolder. The build fails on undefined references/citations, overfull hboxes, or a missing `main.aux`. MiKTeX from `%LOCALAPPDATA%\Programs\MiKTeX\miktex\bin\x64`; Python from the repository `.venv`.

## Files

| File | Role |
|---|---|
| `main.tex`, `refs.bib` | manuscript and bibliography (8 new entries, all checked against Crossref on 2026-09-20) |
| `check_paper.py` → `data/check_paper_output.json`, `check_stdout.txt` | exact-arithmetic replay of every printed number |
| `make_figures.py` → `figures/*.pdf` | two vector figures (the timeline is inline TikZ) |
| `lean/RobustSharpening.lean` | copy of `proofs/StartupCount/RobustSharpening.lean` (new module) |
| `provenance/` | strict Lean receipts (new module, rounding lemma, 17 Sept root), 17 Sept manifest, the 20 Sept certificate script and literal-generator panel |

## What is new relative to both drafts and the guidance supplement

Mathematics (all conventional unless marked):

1. **Exact quadratic minimum** 16/5 in the drift (supplement §5) → `A = 11/5 − …`. Lean: `food_product_deficit_sharp`, `count_log_occupation_sharp`.
2. **Sharper logarithm bound**: `−log(1−x) ≤ x + x²/(2(1−x))` gives second-order loss term `a/(K(K−2))` instead of `2a/(K(K−2))`, and `log(1+1/K) ≥ 1/K − 1/(2K²)`; correction `1500/(h−2)` instead of `3000/(h−2)`.
3. **Potential range** `D = 52` instead of 54 (`log(8.25e18)+8 < 51.56`). Lean: `potential_range_exp`.
4. **Variance weights** `(101/100, 101)` instead of `(17/16, 17)`. Lean: `weighted_square`.
5. Consequently the headline is **all n ≥ 4, V ≥ max{2e22, 1e8 n}, η ≤ 1e-5, failure < 1e-10** (η ≤ 1e-4: < 1e-6). The supplement's rows (V ≥ 3e22, 1e-9; V ≥ 5e22, 2.26e-7) are implied and superseded; `check_paper.py` still replays the 20 Sept numbers (exponent 16.1086, quota 0.1101025). Lean scalar margins and budget: `robust_operating_point_margins`, `robust_operating_point_margins_wide`, `robust_error_budget`.
6. **Robust all-window theorem** (Theorem 3.2): two-sided suprema of the reward and export martingales give every window in (1,199] on one event, cost `52 + 2z` and export tolerance `2·(1/40)`. At V ≥ max{1e24, 1e9 n}: slope 2.182, cost 80, failure < 1e-20 → export > 0.51 V, deadline 79.6, recovery > 1/4700. This replaces the supplement's caution that two fixed windows do not give all windows.
7. **η range**: physical envelopes hold for η ≤ 3/100 (C < 59); fixed-n vanishing failure for η ≤ 5e-4 (margin changes sign between 5.66e-4 and 5.67e-4).
8. **Source/rarity** at the linear scale `V_n ≥ max{2e22, 1e8 n}` with factor `1 − 1e-10`.
9. **Internal detailed balance** proposition (supplement §7), deterministic and stochastic with falling factorials.
10. Scale discussion: where the certificate stops (1.5e22 works at 2e-6 for η=0; 1e22 exponent 4.1), the open establishment implication, and a *heuristic* remark that catalysts of the (00,11) split are net producers of 0011 during establishment, so the uniform loss envelope is pessimistic.

Evidence split is in Appendix A of the paper. The robust mission root is **not** compiled; only the 17 Sept food-silent root and the listed components are.

## Lean verification of the new module

```
.\.venv\Scripts\python.exe scripts/verify_proof.py proofs/StartupCount/RobustSharpening.lean --timeout 600 --declaration StartupCount.robust_error_budget --output problem_workspaces/RAF_finite_count_startup_random_reactor/robust_sharpening.verify.json
```

Receipt: verified=true, Lean 4.30.0, source SHA-256 `ccb237409087dcc4498813102e73f183e0f699dc1defecd5d48307bb66ce16d1`, axioms `propext`, `Classical.choice`, `Quot.sound` only.

## Pitfalls met

- `exp_lower` with a 40-term Taylor value of `e` raised to powers ~1000 makes Fractions explode; the script uses the rational `2718281828/10^9` and caps exponents at 130.
- In Lean, `norm_num at h` evaluates `2.7182818283^24` and breaks the later `exact`; use `exact_mod_cast hpow 24` with an explicit type ascription instead.
- Floats: `[t]` tables/figures split theorem statements; the final layout uses `[!ht]` for Figure 2, Table 4 and Figure 3.
- arXiv abstract limit is 1920 characters; the abstract is ~1940 with TeX markup (below the limit as plain text). Keep it short when editing.
