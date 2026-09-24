# Build and provenance

Paper: *Exact common-activity compatibility of autocatalytic cores: finite cycle
acceleration, monotone elimination, and fixed-parameter tractability in the longest
path* (20 September 2026, 28 pages). Metadata macros at the top of `main.tex`:
`\PaperAuthor`, `\PaperAffiliation`, `\PaperDate` (blank on purpose) and
`\PaperRepository` (put the public URL of the Lean/source repository here; if empty the
text says "the accompanying source repository").

Final PDF: `key_results/RAFs/Exact_Common_Activity_Compatibility_Cycle_Acceleration_FPT.pdf`.

## Files

| File | Role |
|---|---|
| `main.tex` | Manuscript (TikZ figures 1 and 3 inline) |
| `refs.bib`, `main.bbl` | Bibliography (superset; only cited entries print) |
| `make_figures.py` | Generates `figures/cycle.pdf` (Figure 2) from exact formulas |
| `check_paper.py` | Replays every printed number and identity exactly; ends in `"status": "PASS"` |
| `sanity_elimination.py` | Tabulated floating-point prototype of Algorithm 3 (monotone elimination) compared with Kleene iteration on 300 random instances; a logic check, not a certificate |
| `lean_sources.zip`, `lean_README.md` | All 77 Lean modules of `proofs/ThermoCoreCompatibility`, toolchain pin, Lake manifest, 15 strict receipts, and a guide |

## Commands (MiKTeX, user scope)

```bash
export PATH="$LOCALAPPDATA/Programs/MiKTeX/miktex/bin/x64:$PATH"
python make_figures.py
python check_paper.py
python sanity_elimination.py
pdflatex -interaction=nonstopmode main.tex
bibtex main
pdflatex -interaction=nonstopmode main.tex
pdflatex -interaction=nonstopmode main.tex
```

Check `main.log` for `^!`, `Warning`, `Overfull`, `undefined` (last build clean).
Patch scripts must be written to a file: bash heredocs eat backslashes.

## Second sprint (FPT), what changed

* **Theorem 1.2 (new): fixed-parameter tractability in h.** Algorithm 3 eliminates
  vertices bottom-up along a DFS forest. Monotone two-variable implications are closed
  under exact elimination through the next-map `nu_w(a) = min(U_w ∩ [a,∞))`
  (Lemma 7.1, compiled: `MonotoneElimination.lean`). Generated maps join ancestors,
  envelopes have near-linear size by Davenport–Schinzel (Szemerédi's `n log* n`), sizes add
  along the forest (`S(j) <= K (K+1)^d |subtree|`), numbers have descriptions bounded in h.
  `f(h)` is an iterated exponential (walks of length `2^(h+1)`); not optimized.
* **Theorem 1.1 (strengthened).** Algorithm 1 is now label-correcting with cycle
  detection: no simple-path enumeration, at most `h+1` rounds of `2hn` arc scans per phase
  (Lemma 3.1). Cost `(J+1) n (h+2)^{O(h)} poly(B)`, `J` = jumps `<= sigma (h+2)^{O(h)}`;
  `J <= 4|E|` on forests, `O(n)` cycles on windmills.
* **Margin as infinitesimal (Theorem 5.1).** Tests are decided for all small `t>0`; only
  tests actually performed are decomposed; trace invariance replaces the global template
  enumeration. The a-priori threshold `t_0` survives as Corollary 5.3 (form of the Lean root).
* **Proposition 1.3 (barrier).** A directed path is compatible iff
  `F_m∘…∘F_1(x_0) > lambda`; polynomial time in n would decide that sign (2^m B bits).
* New Lean (both compile strictly, receipts in the workspace `verification/`):
  `GeneralCompatibility/MonotoneElimination.lean` (9 s) and
  `GeneralCompatibility/Consequences.lean` (189 s): `round_down_margin`,
  `min_residual_le_capacity`, `ratio_factor_le`, `lower_mono_ratio`, `upper_mono_ratio`,
  `robust_band_empty`, `order_d_band`.
* All "Anonymous" citations removed; companion manuscripts are cited by title.
* New references checked against Crossref: Allender et al. 2009, Szemerédi 1974;
  Sharir–Agarwal 1995 (book).

## Honest limits to keep in mind when editing

* Theorem 1.2's arithmetic paragraph is an existence-level argument via general QE with
  `2^{O(h)}` variables; no explicit `f` is claimed. The piece-count lemma depends on the
  Davenport–Schinzel bound for partially defined functions (`lambda_{s+2}`).
* Remark 8.2's exponent `(2h+2)^(h+1)` for generic nested elimination is a routine estimate.
* Collins' explicit 1975 CAD time formula is deliberately not quoted.
* Neither complete algorithm is implemented; `sanity_elimination.py` is floating point.
