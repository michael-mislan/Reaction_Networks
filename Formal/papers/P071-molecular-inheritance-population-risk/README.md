# Conservative molecular inheritance and population risk: extinction and variance ordering, approximation limits, and regrowth

[Read the paper](../../../Applications/Cell-Memory/P071-molecular-inheritance-population-risk.pdf) · [Claim map](claims.json) · [Build instructions](../../BUILD.md) · [All papers](../../../README.md)

For a declared chromatin-state branching model, conservative complementary allocation and independent draws can have identical means but different extinction and variance; the paper identifies ordering assumptions, preparation effects and observation limits.

**Reproduction:** Build from `manuscript/` with pdflatex main.tex, bibtex main and two further pdflatex passes. The scripts and data are self-contained relative to this package. The original BUILD.md lists the optional ordered numerical replay; use a suitable Python environment with NumPy, SciPy, SymPy and Matplotlib, rather than its historical absolute Erdos interpreter path. `scripts/make_figures.py` renders included saved data. Diagnostics and reversal searches are optional numerical investigations, not prerequisites for the manuscript. Long computations should use an explicit bounded process.

**Formalization:** The current 22-page paper strengthens the earlier workspace manuscript. Fourteen PhenotypeMemory modules plus one shared dependency are preserved against the strict continuation root receipt. Selected formal components cover finite source and partition algebra, supersolutions, downward iteration, weighted contraction, order/covariance/response lemmas and coarse threshold arithmetic; only continuation_finite_certificate has a saved elaborated axiom interface. The full chronological construction, probability couplings, PGF comparison, variance ordering, strictness, large-memory limit, state-dependent-division obstruction, strong Markov bridge, validated integrator soundness and tight boxes remain conventional or exact computation. In particular, the newer regrowth gaps above 0.098 and 0.084 must not be relabelled as the older coarse Lean arithmetic. Constant division and monotone hazard are substantive assumptions. The examples are not clinically calibrated.

[Historical verification review](../../papers/P071-molecular-inheritance-population-risk/evidence/historical-verification.json) records source/environment matching and the exact saved declaration-probe coverage.

The full abstract, hypotheses and numbered results are in the manuscript.

**Formal sources:** 15 selected modules, including shared dependencies. 44 declaration records are linked in the claim map. The preserved manuscript tables provide the detailed correspondence and identify conventional arguments and numerical illustrations.

Selected entry points:

- [Main.lean](../../proofs/PhenotypeMemory/Main.lean)
- [Source.lean](../../proofs/PhenotypeMemory/Source.lean)
- [Partition.lean](../../proofs/PhenotypeMemory/Partition.lean)
- [PopulationBounds.lean](../../proofs/PhenotypeMemory/PopulationBounds.lean)
- [ReductionCertificate.lean](../../proofs/PhenotypeMemory/ReductionCertificate.lean)

## Verification

The [verification notes](../../VERIFICATION.md) explain the saved compilation and axiom-audit records. See the [build guide](../../BUILD.md) to reproduce a selected paper.
