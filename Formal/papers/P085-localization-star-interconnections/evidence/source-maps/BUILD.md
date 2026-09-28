# Build notes: *Localization of D-instability in star interconnections and a sharp bound on synchronized groups*

Final PDF: `../Localization_of_D-Instability_Star_Interconnections.pdf` (workspace root), copied to
`key_results/RAFs/Localization_of_D-Instability_Star_Interconnections.pdf`.

## Scope decision (owner instruction, 2026-09-28)

The paper contains only the final critical path: spectral localization (Thm 2.3), lifting
(Thm 2.4), the criterion (Cor 2.5), the marginal-gap example (Prop 2.6) and sharpness of both the
number of groups (Thm 2.7, Example 7.4) and their size (Prop 2.8, added after the referee pass). The follow-up consequences requested by the PI guidance (counting and the
pseudo-polynomial decision procedure A1/A2, the time-scale certificate A3, cyclic cascades A4,
worked examples A7, coordinate k = 2 A6) are recorded in the workspace notes and, where
formalized, in `proofs/DStabilityLocalization/{Cascade,Counting,Consequences}.lean`, but are not
in the paper (the owner's standing rule: no optional extras, even when guidance suggests them).
For the same reason the paper has two figures instead of the four in the guidance.

## Files

| File | Purpose |
|---|---|
| `main.tex` | The paper. `\PaperAuthor`, `\PaperAffiliation` are deliberately blank (repository convention). `\lean{...}` is url-style: never inside math or captions. |
| `refs.bib`, `main.bbl` | Bibliography (style `plainurl`); 50 entries, all verified (`../notes/LITERATURE_VERIFICATION_2026-09-28.md`); reused entries copied verbatim from the verified coNP-hardness paper. `refs_new.bib` is the verification agent's raw output (not loaded). |
| `figures/*.pdf` | Written by `make_figures.py` (matplotlib, validated palette). |
| `check_paper.py` | Exact replay (sympy) of every printed computation plus the Lean receipt and source hashes. Must print `31/31 checks passed`. |
| `make_anc.py` | Rebuilds `anc/` (Lean closure of the root, 14 modules + `All.lean`, toolchain pin, path-free receipt summary, replay script, the two companion manuscripts). Stops if any source differs from its receipt hash. |
| `build.py` | pdflatex → bibtex → pdflatex ×2 (MiKTeX). Fails on errors, undefined references, overfull boxes, BibTeX warnings, a full disk, or off-page text; then copies the PDF to the workspace root and `key_results/RAFs/` (`--no-copy` skips). |
| `qa/` | Referee report and point-by-point response. |

## Rebuild

```
<repo>/.venv/Scripts/python.exe make_figures.py
<repo>/.venv/Scripts/python.exe check_paper.py
<repo>/.venv/Scripts/python.exe make_anc.py
<repo>/.venv/Scripts/python.exe build.py
```

Lean (from the repository root):

```
.venv/Scripts/python.exe scripts/verify_proof.py proofs/DStabilityLocalization/All.lean --timeout 3000 --declaration DStabilityLocalization.localization_and_sharpness --declaration DStabilityLocalization.sharpness_full --declaration DStabilityLocalization.lumping_needed --declaration DStabilityLocalization.cyc2_example --output problem_workspaces/D_stability_localization_TLOC/evidence/lean_receipt_root_v2.json
```

## Pitfalls met

- `\lean{}` inside a `\caption` is fatal ("\url used in a moving argument"): use `\texttt`.
- Free disk space on E: was ~6 GB; `build.py` checks the log for disk errors.
- Font expansion is disabled (`microtype` with `expansion=false`); `build.py` scans content
  streams for off-page text.
