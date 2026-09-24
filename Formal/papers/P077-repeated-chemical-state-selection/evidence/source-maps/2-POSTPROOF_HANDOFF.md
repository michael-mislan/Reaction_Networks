# Post-proof extension and publication handoff

Original guide: **50/50 complete**. Post-proof follow-ups: **20/20 PASS**.
The finite-horizon roots remain green. The optimal exponential population rate
was investigated but **has not been proved or determined**.

## Delivered paper

`Repeated_Chemical_State_Selection.pdf` is the final 12-page research manuscript,
saved at the workspace subfolder root as requested. Its reproducible LaTeX
source has the same basename. `paper_figures.py` produces the three vector
figures in `paper_assets/`. All twelve final rendered pages were visually
inspected; the build has no undefined references or overfull boxes. The proof
presentation includes only the completed critical path and the imported chemical
source definitions needed to state it. It excludes discovery-only refinements.

## New proved results

- `HorizonScaling`: exact geometric sum and inverse horizon equivalence;
  chemical envelope `(142+4T/21)M exp(-N/(4D))`; explicit logarithmic chemical
  sizing; necessary inverse count horizon.
- `SourceHorizonDesign.logarithmic_source_horizon`: for even M and prescribed
  positive K within the explicit logarithmic sufficient bound, finite source
  parameters exist at confidence `1-delta`. Roots, founders, clocks and quotas
  are bound. The ordinary Theta(log M) deduction uses this result and the
  compiled necessary bound; the paper gives the integer-rounding argument.
- `CompactWitness` and `PublicationResolution.publication_tenCycle_instance`:
  K=10, M=10^13, N=65536000000000000000000, gamma=10^-11, confidence >=.994.
  The exact rational replay gives >=.9940328056031995, but the exported
  confidence is .994. The returned source and transfer law are unchanged.
- `publication_terminal_interpretation`: on the SAME certified history event,
  high-state fraction >.998935 and low-state count >=1598083. This avoids
  presenting two unrelated conditional guarantees as one joint result.
- `EnrichmentDesign`: generic inverse target rule, outward exponential and
  fraction certificates, integer minority bound, and 4/5/8/11-cycle gain
  requirements for 90/95/99/99.9 percent high fractions. Gain requirements still
  require separate mission budgets.

The publication root strictly compiled with exit 0, no diagnostics, and the
standard axioms Classical.choice, Quot.sound and propext only. Its current
receipt exports five interfaces and records 202 dependency modules. The final
audit checks source and artifact hashes, not merely a saved `verified` flag.

Relative to the previous refined witness, population falls 100-fold and NM
falls 400-fold. Relative to the initial count-floor witness, those factors are
10^7 and 4*10^7. The complete worked design includes finite clock-dependent
quota formulas, duration, terminal refill, and material bills. No numerical
optimization campaign or enormous state enumeration was launched.

## Optimal-rate attempt and precise remaining implication

The small constant-rate comparison converges to dilution base
`4^(1-zL/zH) = 2.515536575...`, rather than `exp(g) = 2.124998894...`.
This does NOT establish the source optimum: the first number is a reduced-model
diagnostic, while the second is only the necessary event ceiling.

The new discrete scalar minority-growth exponential barrier with eta=.32
compiled strictly in `MinorityGrowthBarrier.lean`. It is retained separately
and is not imported into the publication root. A source-level endpoint bound,
its conditional mission composition, and a matching survival converse remain
unproved. A sharp stationary-root rate additionally requires uniform chemical
tracking with the finite-gamma correction and a long-horizon limit argument.
The investigation, exact drift margin, proposed mechanism, and evidence are
in `RATE_INVESTIGATION.md`, `postproof_pilot.py/json`, and
`verification/minority_barrier.json`. The final paper explicitly leaves the
optimal constant open. No sharper rate is inferred from this partial result.

## AGC and reproducibility

AGC was used at entry, structural changes, formal failures, and before the
completion decision. The final checkpoint is CURRENT, with an unbound authored
route and no new mathematical suggestions. It still cannot supply a canonical
frontier closure for this workspace; no AGC ClosedRoot is claimed. Its freshness
checks were helpful, but strict Lean evidence and direct source inspection
settled the mathematical status. Generated evidence has not been staged or
committed. The chronological ledger remains `campaign/logs/2026-09-19.md`.

From `E:\Erdos Problems`:

```powershell
.\.venv\Scripts\python.exe scripts/check_python.py --quiet
.\.venv\Scripts\python.exe scripts/verify_proof.py proofs/SerialTransferSelection/PublicationResolution.lean --timeout 900 --declaration SerialTransferSelection.publication_tenCycle_instance --declaration SerialTransferSelection.publication_terminal_interpretation --declaration SerialTransferSelection.logarithmic_source_horizon --declaration SerialTransferSelection.chemical_sizing --declaration SerialTransferSelection.target_gain_table --output problem_workspaces/RAF_state_selection_many_serial_transfers/verification/publication.json
.\.venv\Scripts\python.exe problem_workspaces/RAF_state_selection_many_serial_transfers/postproof_pilot.py
.\.venv\Scripts\python.exe problem_workspaces/RAF_state_selection_many_serial_transfers/paper_figures.py
.\.venv\Scripts\python.exe problem_workspaces/RAF_state_selection_many_serial_transfers/postproof_audit.py
```

From the problem workspace, run `pdflatex -interaction=nonstopmode
-halt-on-error Repeated_Chemical_State_Selection.tex` twice. Use Poppler to
render and inspect the new PDF after manuscript edits. No dependency update
is needed. The canonical numerical environment passed `smoke_numerics.py`.

The completed follow-up assignment and paper do not imply a solution of the
still-open optimal-rate extension. The next mathematical task, if continued,
is source-level minority-growth probability and its converse, not further
normalization tweaking or bulk numerical replay.
