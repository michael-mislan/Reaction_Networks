# Zero-divisor methods for absolute concentration robustness: completeness, positive geometry, and quantitative certificates

[Read the paper](../../../Theory/Algorithms/P082-zero-divisor-acr.pdf) · [Claim map](claims.json) · [Build instructions](../../BUILD.md) · [All papers](../../../README.md)

Zero-divisor counterexamples and block-order candidate completeness for absolute concentration robustness, with quantitative residual/load identities and separately identified geometric and dynamical arguments.

**Reproduction:** Build from manuscript/ with pdflatex main.tex, bibtex main and two further pdflatex passes; figures and main.bbl are included. Optional check_paper.py needs SymPy and uses literal exact inputs; make_figures.py needs Matplotlib, NumPy and SciPy and writes local figures. Use the top-level manuscript scripts; anc/ contains original ancillary duplicates. Bound any numerical replay explicitly. Historical source-machine commands are archival; public Lean reproduction uses the unchanged module paths and pinned shared environment in BUILD.md.

**Formalization:** The current 24-page paper distinguishes its compiled algebra from conventional geometry and dynamics. The strict CampaignRoot and PaperRoot receipts cover the two bimolecular counterexamples to necessity/sufficiency of a unique candidate, the admitted mixed-order counterexample, block-order completeness for rational mass-action input with real witnesses, release-ring and ACR transfer, and residual/reactor/EnvZ/release algebra. RegularityCertificates is separately source- and environment-matched. Completeness assumes block compatibility, ideal membership and leading-monomial coverage, plus nonvacuous ACR and coordinate candidacy; it is a mathematical candidate-set theorem, not a verified root-isolation program or ACR decision procedure. Regular-point coverage, nonlinear stability, invariant-region reasoning, parts of positive-pool reconstruction and dynamical interpretation remain conventional. Exact finite computations are not kernel proofs. Three saved elaborated standard-axiom interfaces cover campaign_root, paper_root and envZ_regular_minor; other listed declarations inherit source-bound module compilation without individual saved probes.

[Historical verification review](../../papers/P082-zero-divisor-acr/evidence/historical-verification.json) records source/environment matching and the exact saved declaration-probe coverage.

The full abstract, hypotheses and numbered results are in the manuscript.

**Formal sources:** 41 selected modules, including shared dependencies. 66 declaration records are linked in the claim map. The preserved manuscript tables provide the detailed correspondence and identify conventional arguments and numerical illustrations.

Selected entry points:

- [CampaignRoot.lean](../../proofs/ACRZeroDivisors/CampaignRoot.lean)
- [PaperRoot.lean](../../proofs/ACRZeroDivisors/PaperRoot.lean)
- [NecessityIdeal.lean](../../proofs/ACRZeroDivisors/NecessityIdeal.lean)
- [SufficiencyCounterexample.lean](../../proofs/ACRZeroDivisors/SufficiencyCounterexample.lean)
- [OrderMain.lean](../../proofs/ACRZeroDivisors/OrderMain.lean)

## Verification

The [verification notes](../../VERIFICATION.md) explain the saved compilation and axiom-audit records. See the [build guide](../../BUILD.md) to reproduce a selected paper.
