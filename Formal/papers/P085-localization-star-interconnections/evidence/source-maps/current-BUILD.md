# Build notes: *Localization of D-instability in star interconnections and a sharp bound on synchronized groups*

This folder holds the arXiv-ready source of the paper (final version, 28 September 2026). The PDF
is copied to `../Localization_of_D-Instability_Star_Interconnections.pdf`. **This folder is the
source to edit.**

The earlier draft is `problem_workspaces/D_stability_localization_TLOC/paper/`, with its PDF at the
workspace root. It is left untouched. The campaign record, the supplementary information
(`SUPPLEMENTARY_INFORMATION.md`) and the follow-up results that are not in the paper live in that
workspace.

## What changed relative to the draft

The draft had been through one referee round (`qa/REFEREE_REPORT.md`, `qa/REFEREE_RESPONSE.md`).
The final version applies the PI plan (`SUPPLEMENTARY_INFORMATION.md` §11–12 in the workspace) and
fixes everything a fresh independent referee pass found (`qa/REFEREE_REPORT_FINAL.md`,
`qa/REFEREE_RESPONSE_FINAL.md`, itemized). The referee found no mathematical error.

- **Stronger sharpness of group size.** Proposition 2.8 now holds for every number m ≥ 2 of
  pieces (loads c³/m, c > 2, (m−1)c³ < 8m): only the fully lumped group destabilizes, so the size
  of a synchronized group cannot be bounded. New Lean module `proofs/DStabilityLocalization/GroupSize.lean`
  (`group_size_sharpness`).
- **One formal root for the paper.** New root file `proofs/DStabilityLocalization/Paper.lean`
  imports `Main`, `GroupSize` and `Counting`; its strict receipt
  (`problem_workspaces/D_stability_localization_TLOC/evidence/lean_receipt_paper.json`) exports all
  seven cited declarations with the axioms `propext`, `Classical.choice`, `Quot.sound` only.
  No existing module was changed, so the draft's receipts stay valid.
- **Lean fidelity.** Lemma 3.3 restated exactly as formalized (existential thresholds, explicit
  constants in the proof); Lemma 4.1(d) says "differentiable".
- **Scope statements** (abstract, results (A) and (B), Remark 2.9(i)): localization gives the same
  eigenvalue, in general at other core time constants (for non-real z, a common dilation κ ≥ 1);
  lifting gives an unstable eigenvalue, in general a different one.
- **Positioning and literature.** Classical ingredients named as such (end of Related work);
  Hartfiel/Cain attribution corrected against Kushel's survey; singular-perturbation and
  Simpson-Porco–Monshizadeh sentences made precise; the companion [12] paraphrase completed
  (n ≥ 2; exact only for D-semistability in general).
- **Discussion.** The formally verified bound ∏_c (N_c+1)² on distinct boundary systems; a precise
  consequence of the companion's hardness; two marginal boundary systems that always transfer
  back, and Open problem 2 restated for the remaining gap.
- **Notation.** h(κ) → ψ(κ), ℓ⁰ → ℓ̂, c₀ → γ / c_*, k = j + 2 in Section 9, Figure 2 axis label.
- **Ancillary files.** Closure of `Paper.lean` (17 Lean files), `lakefile.lean` for a fresh
  checkout, path-free receipt summary with declaration names and elaborated types, replay script
  (40 checks), the two companion manuscripts.
- **Not adopted from the SI plan:** pointers to a supplementary-information PDF. The SI mixes
  conventional and numerical results with internal notes and review responses; it is better
  released separately as supplemental reports, and the paper stays on its fully formalized
  critical path. The time-scale certificate (SI §6.1) and the pseudo-polynomial decision
  procedure (SI §4.2) are therefore not mentioned.

## Files

| File | Purpose |
|---|---|
| `main.tex` | The paper. `\PaperAuthor` and `\PaperAffiliation` are deliberately blank (repository convention). `\lean{...}` is a url-style command: write underscores unescaped, never use it inside math mode or a caption. |
| `refs.bib`, `main.bbl` | Bibliography (style `plainurl`). arXiv uses `main.bbl`. All 31 cited DOIs re-resolved on 2026-09-28 (`qa/audit_references.py`, `qa/reference_audit.json`). |
| `figures/*.pdf` | Written by `make_figures.py` (matplotlib). |
| `check_paper.py` | Exact replay (SymPy) of every printed computation, of general-m Proposition 2.8, of the counting bound and the marginal-case observations on small examples, and of the SHA-256 of every Lean source against the receipt. Must print `40/40 checks passed`. A copy is shipped as `anc/check_paper.py`. |
| `make_anc.py` | Rebuilds `anc/` from the repository and the workspace receipt `evidence/lean_receipt_paper.json`. Stops if any source differs from its receipt hash. |
| `build.py` | pdflatex → bibtex → pdflatex ×2 (MiKTeX). Fails on errors, undefined references, overfull boxes, BibTeX warnings, a full disk, or off-page text; then copies the PDF one level up (`--no-copy` skips). |
| `make_manifest.py` | Writes `ARTIFACT_MANIFEST.json`: hashes, formal roots, axioms, replay result. |
| `make_submission.py` | Writes `arxiv_submission.tar.gz`, refuses absolute local paths, and test-compiles an extracted copy without BibTeX (as arXiv does). |
| `ARXIV_SUBMISSION.md` | Metadata for the arXiv form and the remaining steps before submission. |
| `qa/` | Referee reports and responses (first round from the draft, final round here), the reference audit, page renders. |

## Commands (from the repository root)

```
.venv/Scripts/python.exe scripts/verify_proof.py proofs/DStabilityLocalization/Paper.lean --timeout 3000 --declaration DStabilityLocalization.localization_and_sharpness --declaration DStabilityLocalization.sharpness_full --declaration DStabilityLocalization.lumping_needed --declaration DStabilityLocalization.cyc2_example --declaration DStabilityLocalization.group_size_sharpness --declaration DStabilityLocalization.card_bdSystems_le --declaration DStabilityLocalization.bdSystem_eq_of_loads --output problem_workspaces/D_stability_localization_TLOC/evidence/lean_receipt_paper.json
cd key_results/RAFs/D_Stability_Star_Localization_arxiv
../../../.venv/Scripts/python.exe make_anc.py
../../../.venv/Scripts/python.exe check_paper.py
../../../.venv/Scripts/python.exe make_figures.py
../../../.venv/Scripts/python.exe build.py
../../../.venv/Scripts/python.exe make_manifest.py
../../../.venv/Scripts/python.exe make_submission.py
```

If a Lean file changes, re-verify `Paper.lean` and refresh the receipt first; `make_anc.py` refuses stale
hashes.

## Pitfalls

- Never write LaTeX through Git-Bash heredocs (`\\` collapses). Use the file tools or Python.
- `\lean{}` inside a `\caption` is fatal ("\url used in a moving argument"): use `\texttt`.
- microtype is loaded with `expansion=false`; `build.py` and `make_submission.py` scan the PDF
  content streams for off-page text (a clean log does not prove every word reached the page).
- `placeins` + `\FloatBarrier` keep Table 3 before the references.
- The shipped `anc/lean/lakefile.lean` declares local modules through `roots := #[`proofs]` and
  `globs := #[.submodules `proofs]`. It has not been run in a fresh checkout (repository rule:
  `lake build` only in `mathlib4_project/`); see `ARXIV_SUBMISSION.md`.
