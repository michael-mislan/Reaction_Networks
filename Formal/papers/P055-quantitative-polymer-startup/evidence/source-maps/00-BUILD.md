# Quantitative emergence and finite-time startup of productive polymer reactors — build notes

Output PDF: `..\Quantitative_Emergence_Finite_Time_Startup_Productive_Polymer_Reactors.pdf` (24 pages), also `main.pdf` here.
Author/affiliation macros (`\PaperAuthor`, `\PaperAffiliation`, `\CompanionAuthor`, `\RepositoryNote`) are at the top of `main.tex` and deliberately blank/placeholder.

## Build

```
powershell -File build.ps1
```

This runs `check_paper.py` (exact replay of every printed number, ~20 s), `make_figures.py`, then pdfLaTeX + BibTeX + 2×pdfLaTeX in a fresh `_build_*` subfolder. The build fails if the log has undefined references/citations or overfull hboxes, or if `main.aux` is missing (the full-disk failure mode). MiKTeX is taken from `%LOCALAPPDATA%\Programs\MiKTeX\miktex\bin\x64`; Python from the repository `.venv`. One benign "ignored error: Infinite glue shrinkage" from the appendix longtable remains; the rendered pages are correct.

## Files

| File | Role |
|---|---|
| `main.tex`, `refs.bib` | manuscript and bibliography |
| `check_paper.py` → `check_paper_output.json`, `data/static_grid.json` | exact-arithmetic replay; static certificate search + exact verification; literal prefix-construction enumeration |
| `make_figures.py` → `figures/*.pdf` | two vector figures (the timeline is inline TikZ) |
| `data/marked_generator_pilot.json`, `data/crossing_compensator_pilot.json` | diagnostic outputs quoted in Section 8 |
| `provenance/` | copies of the diagnostic scripts, the workspace replay script, and the Lean verification manifest |

## Evidence split

**Lean** (all 56 cited declaration names checked to exist; 8 principal files' SHA-256 match `provenance/verification_manifest.json` on 2026-09-17):
Theorem 3.1 (`StartupMarked.startup_quantitative_resolution`, reliability 9989/10000), Theorem 3.2 (`startup_enhanced_failure`, all windows `q(t-s)`, synthesis > 6V/25), Lemmas 4.2–4.8 and Proposition 4.9 at δ = 14, Theorem 3.4(a),(b) (gateways, dimer forest, inverse certificate, 1/2 and 3/10 intervals), normalized source limit/lower bound.

**Conventional (proved in the paper, not formalized):**
- Corollary 3.3: whole-horizon export > 263V/624, recovery > 1/5700, windows longer than 1756/19 give V/10.
- Proposition 5.1: the Lean budget rounds controls to 1e-3 and the floor to 1e-6, but their proved sizes are about 1e-33 and below 1e-2990. So the true failure is < 9.1e-5 at δ = 14, and with δ = 20 the original mission has reliability > 1 − 1.7e-7.
- Final liminf conversion (5.1).
- Proposition 5.2: weak food catalysis, via random time-change coupling.
- **Theorem 3.4(c):** a three-type prefix multitype Galton–Watson embedding. It gives > 99% survival at a = 1/4 and width < 1e-9 at a = 1/2. The workspace handoff listed this as an open Lean bridge. The conventional proof is complete, because the live-prefix process is a genuine multitype GW (fresh, distinct coordinates per child; quotient collisions only at 000 and 111). An exact enumeration to depth 2 confirms the bookkeeping.

**Open (stated as open in the paper):** useful weak-food robustness (drift re-derivation), smaller count scale (below ~3e5 copies the log bracket fails), converse/selection at the new scale, collective witnesses, low openness a < 0.17, and formalization of the three-type bound and general δ.

## Corrections relative to the 11-page workspace draft

- Public title without internal project numbers; volume typeset as `10^{13}n` throughout.
- Recovery described as a guaranteed floor, not an efficiency.
- The 1600-trial screening uses 0.9989; 1614 trials are needed at 0.99.
- Evidence tags are explicit on every theorem.
- Added a derivation of the constants 1558/9, 3073, 6146, 3072000 and 196608000 from the envelopes, and an explanation of what sets 10^24 (bracket cutoff 307304 copies × the requirement's relative stock threshold) and 10^13 n (export-counter exponent 79.75).
