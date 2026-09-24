# Randomized stopped lineage experiments separate phenotypic switching, selection and correlated inheritance

[Read the paper](../../../Applications/Cell-Memory/P075-randomized-stopped-lineage-identification.pdf) · [Claim map](claims.json) · [Build instructions](../../BUILD.md) · [All papers](../../../README.md)

Randomized observation deadlines stopped at the first demographic event identify switching and offspring mechanisms under explicit calibration assumptions; the paper separates structural identification from finite-sample inference and correlated-inheritance effects.

**Reproduction:** Build from `manuscript/` with python build.py or the standard pdflatex/bibtex/pdflatex/pdflatex sequence. Run numerical scripts from that directory because some output filenames are relative to the working directory. check_paper.py --quick omits the Monte Carlo diagnostic; NumPy, SciPy, SymPy/mpmath and Matplotlib supply its dependencies. The included saved data and four vector figures allow building without a replay. Do not use the archived lean_verify.py defaults here: they infer the old repository depth. Use the verification commands in `Formal/BUILD.md` for any explicitly desired Lean check.

**Formalization:** The current 20-page manuscript has a declared finite-algebra subset: pair and mixture identities, matrix/resolvent and delayed-channel cancellation, offspring marginal and quadratic identities, and the new cancelled-target/calibration algebra. Six modules and 23 declarations are preserved. The five-module Postproof closure has fully source- and environment-matched strict history. CancelledTarget has source-hashed historical success and six standard-axiom reports, but its custom receipt omits the Mathlib manifest hash; that limitation remains explicit. Stochastic paths, resolvent convergence, concentration and coverage, interval inclusion and KL soundness, cooperative comparison, and numerical claims remain conventional or computational. This is model-conditional identification and design, not a clinically validated assay.

[Historical verification review](../../papers/P075-randomized-stopped-lineage-identification/evidence/historical-verification.json). The five-module Postproof closure matches a source- and Mathlib-manifest-bound strict receipt. The separate CancelledTarget module matches a successful historical compilation and six standard-axiom reports under Lean 4.30.0, but that legacy receipt does not record the Mathlib manifest hash. Its environment match is therefore partial, not fully authenticated.

The full abstract, hypotheses and numbered results are in the manuscript.

**Formal sources:** 6 selected modules, including shared dependencies. 23 declaration records are linked in the claim map. The preserved manuscript tables provide the detailed correspondence and identify conventional arguments and numerical illustrations.

Selected entry points:

- [CancelledTarget.lean](../../proofs/PhenotypeIdentification/CancelledTarget.lean)
- [DelayedChannel.lean](../../proofs/PhenotypeIdentification/DelayedChannel.lean)
- [OffspringOrder.lean](../../proofs/PhenotypeIdentification/OffspringOrder.lean)
- [Resolution.lean](../../proofs/PhenotypeIdentification/Resolution.lean)
- [Resolvent.lean](../../proofs/PhenotypeIdentification/Resolvent.lean)

## Verification

The [verification notes](../../VERIFICATION.md) explain the saved compilation and axiom-audit records. See the [build guide](../../BUILD.md) to reproduce a selected paper.
