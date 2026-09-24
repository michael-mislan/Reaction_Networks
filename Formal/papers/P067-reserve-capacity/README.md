# Reserve capacity and reliable eradication in inherited-state populations

[Read the paper](../../../Applications/Cell-Memory/P067-reserve-capacity.pdf) · [Claim map](claims.json) · [Build instructions](../../BUILD.md) · [All papers](../../../README.md)

A finite-mission guarantee combines extinction bounds for an inherited-state target population with a bound on reserve loss throughout treatment, under specified source and delivery assumptions.

**Reproduction:** Compile `manuscript/main.tex` with pdflatex, bibtex, and two further pdflatex passes. The exact audit is `python manuscript/scripts/verify_arithmetic.py` from this dossier. The included `support/experiments/` and `support/results/` preserve the source reconstruction and prior figure producers/data. For the high-renewal figure use `python reproduction/make_high_renewal_figure.py` with NumPy, Matplotlib and mpmath; it retains 60-digit precision and writes to this dossier. The original `manuscript/scripts/make_high_renewal_figure.py` is archival and contains an Erdos output path; do not run that original copy.

**Formalization:** TherapeuticWindows.publication_certificate verifies finite drift bounds, the relative-error envelope, an anchored reserve product and the assembled numerical margins of Theorem 4. The older Root certificate and supporting benchmark algebra are preserved separately. Process construction, stopping theory, order coupling, capacity/asymptotic arguments and the main probability interpretation remain conventional proofs. The later incomplete-filling and smaller-capacity corollaries are exact evaluations, and both sharpness propositions are conventional; they are not part of the compiled publication declaration. No figure, clinical calibration or full stochastic theorem is claimed kernel-verified.

[Historical verification review](../../papers/P067-reserve-capacity/evidence/historical-verification.json) records source/environment matching and the exact saved declaration-probe coverage.

The full abstract, hypotheses and numbered results are in the manuscript.

**Formal sources:** 9 selected modules, including shared dependencies. 26 declaration records are linked in the claim map. The preserved manuscript tables provide the detailed correspondence and identify conventional arguments and numerical illustrations.

Selected entry points:

- [Source.lean](../../proofs/TherapeuticWindows/Source.lean)
- [Clock.lean](../../proofs/TherapeuticWindows/Clock.lean)
- [Reserve.lean](../../proofs/TherapeuticWindows/Reserve.lean)
- [Robustness.lean](../../proofs/TherapeuticWindows/Robustness.lean)
- [Delivery.lean](../../proofs/TherapeuticWindows/Delivery.lean)

## Verification

The [verification notes](../../VERIFICATION.md) explain the saved compilation and axiom-audit records. See the [build guide](../../BUILD.md) to reproduce a selected paper.
