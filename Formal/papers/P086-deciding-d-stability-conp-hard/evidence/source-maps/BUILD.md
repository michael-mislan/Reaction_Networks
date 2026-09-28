# Build notes: *Deciding D-stability is coNP-hard*

This folder holds the arXiv-ready source of the paper (final version, 28 September 2026). The PDF
is copied to `../Deciding_D-Stability_is_coNP-Hard.pdf`. This folder is the source to edit.

The first draft is `problem_workspaces/D_stability_interconnection_localization/paper/`, with its
PDF at the workspace root. It is left untouched. The campaign record, the supplementary
information (`SUPPLEMENTARY_INFORMATION_D_STABILITY_HARDNESS.md`) and the follow-up results that are
not in the paper live in that workspace.

## What changed relative to the draft

The draft had already been through a referee round (`qa/REFEREE_REPORT.md`, `qa/REFEREE_RESPONSE.md`).
The final version applies the PI guidance (SI section 10.1) and fixes what a fresh referee pass
found (`qa/REFEREE_REPORT_FINAL.md`, `qa/REFEREE_RESPONSE_FINAL.md`).

- **Self-containment** (Introduction): the proof uses no result of the companion paper.
- **Complexity packaging** (Section 7): the informal running-time step is framed as standard
  practice, with verified citations to mechanized complexity theory: Forster, Kunze and Wuttke
  (CPP 2020); Gäher and Kunze (ITP 2021); Balbach (AFP 2023). It also names Mathlib's
  `Turing.TM2ComputableInPolyTime`.
- **Related work** (Section 8):
  - Nemirovskii's last-row-and-column interval result, via the Horáček–Hladík–Černý survey;
  - Blondel–Tsitsiklis 1997 as the PARTITION precedent;
  - a new item on matrix polytopes (Gurvits–Olshevsky), including the simplex reformulation of
    D-stability.
- **Open problem 3:** it quotes the Lean-verified time-scale bound `destabilizing_port_fast`,
  labelled as not used in the proofs. It follows that the reduction says nothing about bounded
  heterogeneity.
- **Abstract:** "weak sense (binary encoding)" is now stated, the novelty claim is hedged ("to our
  knowledge"), and the informal part is "running time and trivial instances". The MSC secondary
  code is 93D20.
- **Final referee round:** a new pass found no mathematical error. Its one major item, the
  ancillary lakefile, is fixed. So are 19 minor wording, notation and typesetting items: formal
  scope now includes Remark 3.6; the module count is 52; notation clashes are resolved; the
  related-work items are more precise; the threshold `3q² ≥ c`; ragged-right table captions; no
  font-shape warnings.
- **Ancillary files** (`anc/`) replace the reference to an unpublished repository:
  - the Lean closure of both roots, 57 files, hash-checked against the receipts;
  - path-free receipt summaries;
  - `lakefile.lean` and the manifest;
  - a self-contained replay (42 checks). Compared with the draft's 37 checks, it adds exact
    checks of Remark 3.4 and of the determinant crossing, source-hash checks of all 57 Lean files,
    and byte-for-byte regeneration of both certificate files.
- **Bibliography:** single `refs.bib` (43 entries, 38 cited). Every cited DOI was re-resolved
  (`qa/audit_references.py`, `qa/REFERENCES_VERIFICATION_FINAL.txt`).

- **Round 3** (`qa/REVISION_ROUND3.md`): the eigenvector block is renamed `(v,u)` → `(x,u)` in §2.3.
  Open problem 3 now derives the ratio bound `> 3q²` explicitly and concludes that every scaling
  with ratio `≤ R` is Hurwitz.

## Files

| File | Purpose |
|---|---|
| `main.tex` | The paper. `\PaperAuthor` and `\PaperAffiliation` are deliberately blank (repository convention). `\lean{...}` is a url-style command, so write underscores unescaped, and never use it inside math mode. |
| `refs.bib`, `main.bbl` | Bibliography (style `plainurl`). arXiv uses `main.bbl`. |
| `figures/*.pdf` | Written by `make_figures.py`. |
| `build.py` | pdflatex → bibtex → pdflatex ×2 with MiKTeX. It fails on errors, undefined references, overfull boxes, BibTeX warnings or a full disk, then copies the PDF one level up (`--no-copy` skips the copy). |
| `make_anc.py` | Rebuilds `anc/lean/` and `anc/receipts/` from the repository and the workspace receipts. It stops if any source differs from its receipt hash. |
| `anc/` | arXiv ancillary files; see `anc/README.md`. `anc/replay/check_paper.py` is edited in place. |
| `make_manifest.py` | Writes `ARTIFACT_MANIFEST.json`: hashes, formal root, axioms and the replay result. |
| `make_submission.py` | Writes `arxiv_submission.tar.gz` and test-compiles an extracted copy without BibTeX. |
| `ARXIV_SUBMISSION.md` | Metadata for the arXiv form (plain-text abstract, categories, MSC, comments) and the remaining steps before submission. |
| `qa/` | Page renders, referee reports and responses, reference verification, novelty search. |

## Commands (from the repository root)

```bash
.venv/Scripts/python.exe scripts/verify_proof.py proofs/DStabilityHardness/Paper.lean --timeout 2400
.venv/Scripts/python.exe scripts/verify_proof.py proofs/DStabilityHardness/All.lean --timeout 2400
.venv/Scripts/python.exe key_results/RAFs/Deciding_D-Stability_coNP-Hard_arxiv/make_anc.py
.venv/Scripts/python.exe scripts/process_guard.py run --timeout 1800 --owner-label DSTAB-REPLAY -- "E:/Erdos Problems/.venv/Scripts/python.exe" "E:/Erdos Problems/key_results/RAFs/Deciding_D-Stability_coNP-Hard_arxiv/anc/replay/check_paper.py"
.venv/Scripts/python.exe key_results/RAFs/Deciding_D-Stability_coNP-Hard_arxiv/make_figures.py
.venv/Scripts/python.exe key_results/RAFs/Deciding_D-Stability_coNP-Hard_arxiv/build.py
.venv/Scripts/python.exe key_results/RAFs/Deciding_D-Stability_coNP-Hard_arxiv/make_manifest.py
.venv/Scripts/python.exe key_results/RAFs/Deciding_D-Stability_coNP-Hard_arxiv/make_submission.py
```

`make_anc.py` reads the workspace receipts `evidence/lean_receipt_{paper,all}.json`. If a Lean
file changes, re-verify it and refresh those receipts first; `make_anc.py` refuses stale hashes.

## Pitfalls

- Never write LaTeX through Git-Bash heredocs, because `\\` collapses. Use the file tools or
  Python scripts saved as files.
- `\Box` is taken by `amssymb`, so the certificate box is `\cB`.
- Keep the plain-text abstract under 1,920 characters (currently 1,853; see `ARXIV_SUBMISSION.md`).
- microtype is loaded with `expansion=false`. With font expansion, pdfTeX once placed a caption line
  15220pt off the page with a clean log; `build.py` and `make_submission.py` now scan the PDF for
  such offsets, and `qa/scan_offpage_text.py` does the same with PyMuPDF.
- The shipped `anc/lean/lakefile.lean` must list local modules through `roots := #[`proofs]` and
  `globs := #[.submodules `proofs]`. Lake resolves an import only under a root prefix or a matching
  glob. It has not been run in a fresh checkout (repository rule: `lake build` only in
  `mathlib4_project/`).
