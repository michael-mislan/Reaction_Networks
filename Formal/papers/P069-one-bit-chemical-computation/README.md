# Certified one-bit chemical computation: finite-fuel correction, productive readout, and inheritance

[Read the paper](../../../Applications/Chemical-Computation/P069-one-bit-chemical-computation.pdf) · [Claim map](claims.json) · [Build instructions](../../BUILD.md) · [All papers](../../../README.md)

A finite chemical reaction model jointly corrects a binary input, produces the corresponding output and returns complementary daughters to usable encodings under explicit resource, rate and operating assumptions.

**Reproduction:** Build from `manuscript/` with pdflatex, bibtex, then two further pdflatex passes. The archived `build.ps1` assumes the original environment and scratch drive; use the direct LaTeX commands here. `python check_paper.py` requires NumPy, SciPy and SymPy; `python make_figures.py` also requires Matplotlib and reads the included `data/` files. Earlier source-level producers and saved results are in `support/experiments/`: run `python replay.py`, `python operation_certificate.py` or `python fuel_absorption.py` there when an explicit computational replay is desired. SSA illustrations additionally require Numba. Script paths are local to the copied files. Migration reuses saved computation and strict compilation evidence without rerunning either campaign.

**Formalization:** The current 25-page manuscript is a conventional and exact-computational probability result with selected formally checked components. Lean covers literal source rates and invariants, complementary partition identities, conditional iteration, generic uniformization bounds, repair-clock and arithmetic margins, correction-walk identities, operation-kernel monotonicity and selection tails. Saved strict receipts bind the complete unchanged import closures under Lean 4.30.0; only three declarations have saved elaborated axiom interfaces. The 3,240-state recurrence execution, source-to-semigroup interpretation, CTMC couplings and full probability guarantees are not end-to-end formalized. High-order reactions and strong kinetic separation are model assumptions. Neither a calibrated physical chemical computer nor sustained adaptation is established. Older supporting notes remain historical; they do not replace the expanded current manuscript.

[Historical verification review](../../papers/P069-one-bit-chemical-computation/evidence/historical-verification.json) records source/environment matching and the exact saved declaration-probe coverage.

The full abstract, hypotheses and numbered results are in the manuscript.

**Formal sources:** 18 selected modules, including shared dependencies. 37 declaration records are linked in the claim map. The preserved manuscript tables provide the detailed correspondence and identify conventional arguments and numerical illustrations.

Selected entry points:

- [ConcreteWitness.lean](../../proofs/TinyProgrammableChemicalFactory/ConcreteWitness.lean)
- [CorrectionWalk.lean](../../proofs/TinyProgrammableChemicalFactory/CorrectionWalk.lean)
- [IntegerBounds.lean](../../proofs/TinyProgrammableChemicalFactory/IntegerBounds.lean)
- [Invariants.lean](../../proofs/TinyProgrammableChemicalFactory/Invariants.lean)
- [Iteration.lean](../../proofs/TinyProgrammableChemicalFactory/Iteration.lean)

## Verification

The [verification notes](../../VERIFICATION.md) explain the saved compilation and axiom-audit records. See the [build guide](../../BUILD.md) to reproduce a selected paper.
