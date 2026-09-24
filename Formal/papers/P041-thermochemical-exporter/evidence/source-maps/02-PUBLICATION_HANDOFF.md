# C0 publication handoff

## Delivered result

The paper **Thermochemically Consistent Realization of a Stochastic Autocatalytic Exporter** is saved as `Thermochemically_Consistent_Exporter.pdf` in this workspace root, alongside its editable LaTeX source. The original C0 guide remains 48/48 complete. The separate publication checklist in `publication/TASKS.md` records the 24 PI follow-ups and their evidence.

The publication keeps the accepted boundary: exact balanced chemical completion, common thermochemistry, labeled count rates and output/service marks, and inherited finite marked-kernel guarantees. The nonexplosive unrestricted-process interpretation is proved conventionally in the paper's Appendix A. The paper does not claim a fully Lean-formalized infinite-state CTMC theorem or an autonomous finite-bath implementation.

## What was proved and learned

1. **Internal cycles have an exact two-vector basis.** The passive cycle is `(-1,1,1,1,1,0)` and the additional internal drive cycle is `(1,0,0,0,0,1)`. The full source kills the passive vector and sends the drive vector to `eP-eF`. Thus the completed chemical subnetwork has one independent fuel/waste driving direction. The affinity of `a cp+b cd` is `b log(8e10)`. This is now formally checked rather than inferred only from rank calculations.
2. **Thermochemistry matches neighboring count rates.** All six forward/reverse ratios were checked symbolically and compiled in Lean at supported neighboring states. The `2X` direction retains the falling factorial, without an extra factor of one half. This connects the potential assignment to the actual source convention.
3. **The stronger inherited operating estimates transfer unchanged.** The designated deletion removes only the reversible `C2 <-> Z` pair; both driven directions, preparation, services and output requirements remain. Retained material balance and thermochemistry and the disabled source identity are compiled. The numerical upper comparison is below `10^-21699` at `V=1e8,H=100`.
4. **Food-only initiation forces logarithmic confidence sizing.** The first template can arise only from basal or reverse driven creation, with coefficient `alpha = 1/500000000 + delta/8000000000`. Independent reference immigration-death food processes, killed by their integrated seed hazard, give the exact survival identity. Jensen gives failure at least `exp(-500 alpha V)`. Uniformly, 99% success requires integer `V >= 4593686`; this is necessary, not sufficient. The reference processes are independent before killing; the actual food counts conditioned on survival are not assumed independent. Supporting algebra and the convex tangent compile.
5. **Three printed success claims are outward-interval certified.** At `H=100`, the bounds are at least `0.923849`, `0.994201`, `0.999558` for `V=1e8,2e8,3e8`. The unchanged predecessor evaluator is imported and fingerprinted. These are evaluated theorem bounds, not Monte Carlo success frequencies or Lean-checked decimal arithmetic.
6. **Physical interpretation is explicit.** At 1 mM and a 60-second time unit, the volumes are approximately 0.166, 0.332 and 0.498 pL. Startup lasts 8 h 20 min and the full example 10 h. The first row guarantees 5000 template equivalents per window, allows `1.2e11` molecules of each food over the full run, and allows `7.5e9` gross driven events. The specified reservoir difference is about 62.235 kJ/mol at 298.15 K. Product is a mixture of template-containing exported species, not a purified free-X guarantee. Apparatus and separation costs are unpriced.
7. **Finite stock accounting is now a precise conditional theorem.** The activity ratio and logarithmic force corridors compile, as does `R >= B/rho` under the gross-count premise. The next operational obligation is robustness to changed forward/reverse ratio in the extended bath source. Paired speed variation does not establish that implication.
8. **Resident maintenance is accounted separately.** The companion keeps external H removal and effective growth. The paper states explicit bounded-coordinate premises for resident service intensities. Current sufficient resident allowances scale as `O(NMT)=O(NM/gamma)` for `T=8/gamma`, while growth-precursor allowance scales as `O(NM)`. This is not a necessary maintenance-cost lower law.

## Experiments, failures and decisions

The extension used one small exact/interval pilot, not a long reactor simulation. SymPy verified the two ranks, cycle images and all six rational neighboring-rate identities. The donor evaluator checked three volumes and the matched disabled bound. The successful numerical checks directly informed the short structural proofs. No bulk certificate replay or parameter sweep was launched.

Initial Lean attempts failed on unnecessary simplifier arguments/tactics and unused hypotheses under strict linting. The mathematical statements did not need weakening. Removing redundant proof commands and marking unused positivity inputs resolved the diagnostics. All supporting modules then compiled in the same frozen environment. The final publication receipt reports `verified=true`, exit 0, empty diagnostics and the standard axioms `propext`, `Classical.choice`, `Quot.sound` for the six audited interfaces.

The first figure renderer rejected a connection style with parallel angles; a simple curved connector fixed it. Page inspection found an omitted typesetting backslash and a floating appendix table among references; both were corrected. A missing optional LaTeX spacing package was removed in favor of an explicit page break. No dependency updates or package installations were performed. These were rendering/tooling corrections, not proof-route failures.

## AGC assessment

AGC was helpful as a scope and freshness gate. It preserved the accepted maintained C0 boundary and identified the need to bind the new strict receipt to the existing frontier. Its exact proof-neutral `authority reconcile-frontier` action was executed, followed by a CURRENT checkpoint. It did not generate a new mathematical mechanism and did not itself establish any theorem. No protected theorem graph was advanced and no generated evidence was staged or committed.

## Reproducibility and final critical path

See `publication/EVIDENCE.md` for actual theorem/declaration mapping and formal/conventional/numerical distinctions. `publication/file_hashes.json` records exact delivered hashes. `publication/certify.py`, `figures.py`, `references.bib`, `build.ps1`, `certificates.json`, and `PDF_QA.md` support reproduction. `verification/Publication.verify.json` is the new strict audit; `verification/Resolution.verify.json` remains the original realization evidence. Daily Sprint 2 and the hypothesis graph preserve the research record outside the paper.

The paper excludes the optional productive-state witness and discovery-only unsuccessful routes. It includes the resident and finite-stock consequences because the PI expressly requested them. Its critical new chain is exact source correspondence -> inherited joint marked law -> unchanged quantitative operation/deletion guarantee, with cycles and initiation as short consequences of that same source.

## Remaining questions, not publication blockers

- C1: establish recovery/entry after a newly specified perturbation or transfer preparation.
- C3: specify serial-transfer dynamics and prove propagation of its required distributions and resource conditions; microscopic growth/division remains a separate source-realization issue where required.
- Changing bath: extend the count source, prove generator bounds uniformly over the activity corridor, stop on first corridor/operating failure, and prove the joint gross-count control for that extended law without circularly borrowing its maintained-model probability.
- Useful isolated product: specify conversion/recovery yields and separation costs.
- Stronger formal scope: formalize the conventional infinite-state process and reference-clock arguments if a later project specifically requires it.

None of these is represented as closed by the current compiled result. No further PI decision was needed to complete the requested bounded publication phase.
