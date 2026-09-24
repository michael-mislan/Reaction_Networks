# Publication handoff

The mandatory follow-ups in the attached handoff are complete at the explicitly stated formal/conventional scope. Original guide: **40/40 PASS**, preserved. Separate publication checklist: **24/24 PASS, 0 FAIL, 0 BLOCKED**. This is a local deliverable assessment; it is not a canonical AGC publication.

The final paper is `Reliable_Covalent_Export.pdf` in this workspace root, with editable `Reliable_Covalent_Export.tex`. Its 15 pages present the final critical proof path, exact reaction and mark table, joint operating theorem, matched disabled comparison, finite-duration consequences, sizing, physical example and evidence boundary. It contains no discovery-only lemmas, optional parameter enlargement, ODE simulations or failed-route narrative.

## Completed mathematical follow-ups

- Direct finite-duration operating and supply certificate at time 500+H, with m=floor(H), final fraction H-m, and supply allowances proportional to this actual duration.
- A sufficient integer copy-scale rule from the duration and confidence logarithms, and a sharper full-error evaluator returning individually interval-checked sufficient values.
- Cumulative output, expected guaranteed output, arbitrary-alignment intervals, service/output and recovery ratios, and conservation-forced food replenishment.
- Actual matched disabled counted-law comparison for every integer H>=1. It retains both driven reactions and removes only templated ligation labels 6 and 7.
- Explicit dimensional translation and reservoir-work interpretation, without claiming experimental calibration or an autonomous fuel reservoir.

## Formal evidence

`verification/BindingCompetitionPublication.verify.json` verifies `RandomViability.Binding.competition_publication_probability`: exit zero, no warnings, empty stdout/stderr, 130.563 seconds, Lean 4.30.0 and 86 authenticated dependencies. It authenticates the current five new modules under `proofs/RandomViability/`: BindingCompetitionTimed, BindingCompetitionConsequences, BindingCompetitionTimedComparison, BindingCompetitionSizing and BindingCompetitionPublication.

Both original compiled endpoint source hashes are preserved. `publication/audit_publication.py` checks current source and compiled artifact hashes against the saved strict closure and frozen manifest. Its outputs are `publication/evidence_manifest.json` and `publication/EVIDENCE.md`. A dependency count is verification scope, not a count of solved conjectures. Earlier unsuccessful standalone receipts remain diagnostic history; they are not represented as successful.

Lean verifies the finite marked-kernel laws, actual source estimates, projections, counter saturation, probability bounds, grid geometry and scalar inequalities. Nonexplosion and identification with one infinite-state reaction-clock process, the uncapped physical-path expectation, and the channel-history interpretation of moiety accounting are proved conventionally in the paper. Thus this is not a claim that an infinite-state CTMC construction and every physical interpretation have been encoded in Lean. The manuscript states this boundary in its abstract, theorem discussion and formal appendix.

## Tests and lessons

The canonical numerical environment checks passed. Five small guarded tests cover unit duration, H=100, a fractional duration, tighter confidence and a huge duration with an insufficient initial scale. Logarithmic calculations retain every error term; outward interval comparisons validate the rounded worked-example claims. At V=10^8 and H=100 the enabled supplied-success lower bound is at least 0.9238 and the matched disabled-success upper bound is below 10^-21699. No trajectories were simulated. The plots are ordinary evaluations of proved bounds, separately labelled as numerical.

The key proof distinction is that a shorter observation horizon requires its own supply-tail proof: merely restricting the original event does not shrink its allowances. The finite-duration modules establish exactly that missing implication. Arbitrary alignment then follows from deterministic counting of complete unit windows, without another probabilistic union. The evaluator provides sufficient scales, not an optimization theorem. Full numerical diagnostics and physical values are retained in `publication/worked_example.json`, `numerical_checks.json` and `figure_data.json`.

Compiler failures and their resolutions are recorded in Sprint 10 of `sprints/2026-09-14.md`; none changed the mathematical assumptions. Optional wider-cleavage and exponent-improvement investigations are deliberately outside this requested publication scope, not unfinished prerequisites.

## Reproduction and presentation

`publication/README.md` gives canonical Python, strict Lean, numerical-check, figure and LaTeX commands. `publication/PDF_QA.md` records inspection of all 15 final rendered pages and the final PDF hash. Two vector figures explain the source and compare the certified bounds. References distinguish primary literature from the local predecessor manuscript. The frozen Lean dependencies were not updated.

AGC was useful for receipt freshness and same-cut reconciliation. The saved final checkpoint is `verification/publication_final_gate.yaml`. Its CURRENT classification does not itself close a theorem; its older canonical open-cut suggestions are not used as evidence against or for the authenticated exports. No protected authority graph was promoted and no generated-evidence commit was made. Those integration actions remain with the canonical authority integrator.
