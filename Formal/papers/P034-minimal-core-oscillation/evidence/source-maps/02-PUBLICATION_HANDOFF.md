# Publication handoff - 14 September 2026

## Delivered paper

`type_ii_instability_paper.pdf` is the five-page publication-style paper in this project folder root. Its editable source is `type_ii_instability_paper.tex`. The source template and exact table builder are in `notes/paper_template.tex` and `notes/build_paper.py`.

The paper contains only the necessary counterexample argument: the literal seven-species network; minimality of its three-fork forward source; strictly positive exact parameters; stationary balance; differentiation of the full physical dynamics; and the exact eigenpair with eigenvalue 1+8i. It states the conventional smooth-ODE local-instability consequence separately from the formal spectral headline. No discovery experiments, superseded stability lemmas, optional operating examples, or Hopf/periodic-orbit claims are included.

## Follow-up disposition

The supplied guide permits the source-connected counterexample route and retires helpers that no longer lie on that route. The existing 35 active items are complete; the 13 superseded items are not missing proof obligations. The entry checkpoint was CURRENT / TERMINAL_NO_OPEN_CUT. There is no remaining critical-path follow-up to the selected finite-return-path universal-Hurwitz question.

The six-species classification, nonlinear continuation, degradation-only bifurcation, and other optional successors remain separate research questions. The previously recorded automatic publication interface mismatch is a bookkeeping limitation, not a missing premise of the closed source-connected theorem, and is not represented as successful automatic formal docking.

## Checks performed

- Canonical repository Python check and numerical smoke suite passed.
- Reran `audit_completion.py`: the strict terminal receipt, theorem interface, all 93 dependency sources and artifacts, frozen toolchain, manifest, and completion ledger passed.
- Re-read the source membership, literal dynamics, derivative and eigenpair declarations. No Lean source or dependency was changed; no redundant Lean recompilation was needed.
- Built the paper's integer tables directly from `Witness.lean`. Exact checks of all 28 positive entries, seven stationarity coordinates and fourteen pencil coordinates passed. Results: `results/paper_exact_audit.json`.
- Independently checked the structural assertion on all 126 nonempty proper induced species subsets; this is a transcription/review aid, not substitute formal evidence. The paper gives a direct path argument.
- Compiled LaTeX twice, resolving all references. The final LaTeX log has no overfull/underfull boxes or LaTeX warnings. Rendered and visually inspected all five pages, including the long integer tables, formulas, source paths and reference.
- Verified the primary classification reference against its publisher page.

No generated evidence was staged or committed. The PDF and editable paper source are the deliverables; prior campaign evidence remains intact.
