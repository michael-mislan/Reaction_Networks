# How to design an assay that answers the biological question: from specimen and signal to a justified biological conclusion

[Read the paper](../../../Applications/Assays/P063-assay-design.pdf) · [Claim map](claims.json) · [Build instructions](../../BUILD.md) · [All papers](../../../README.md)

An accurately measured signal can leave the biological question unresolved when sampling, population heterogeneity, stored material, or the measurement itself obscures the quantity of interest.

**Formalization:** A perspective synthesizing eight companion case studies, with conventional derivations and worked model examples. The 16 named declaration records are companion references, not newly proved results of this manuscript. All 13 selected companion module hashes and their full local import closure match the included sources. Companion dossiers retain their own historical and fresh evidence; no fresh compilation or paper-wide axiom audit is claimed for this synthesis. Biological validity, clinical use and empirical coverage are not established by these model examples.

Companion papers:

- [P058](../../papers/P058-enzyme-functional-recovery/README.md)
- [P054](../../papers/P054-sandwich-assay-dilution/README.md)
- [P060](../../papers/P060-finite-target-exclusion/README.md)
- [P053](../../papers/P053-negative-recovery-assays/README.md)
- [P056](../../papers/P056-small-population-prediction/README.md)
- [P057](../../papers/P057-amplification-decisions/README.md)
- [P062](../../papers/P062-fresh-microbial-conversion/README.md)
- [P061](../../papers/P061-native-function-readouts/README.md)

To rebuild this manuscript, run `pdflatex main`, `bibtex main`, then `pdflatex main` twice from its `manuscript/` directory. Figures are included. The preserved `build.ps1` is archival and assumes the original research layout; use the direct LaTeX commands in this checkout.

The full abstract, hypotheses and numbered results are in the manuscript.

**Formal sources:** 166 selected modules, including shared dependencies. 16 declaration records are linked in the claim map. The preserved manuscript tables provide the detailed correspondence and identify conventional arguments and numerical illustrations.

Selected entry points:

- [PopulationRoot.lean](../../proofs/G6PDReserve/PopulationRoot.lean)
- [Publication.lean](../../proofs/SandwichImmunoassay/Publication.lean)
- [PolicyComparison.lean](../../proofs/SpecimenReliability/PolicyComparison.lean)
- [ExtendedCoverage.lean](../../proofs/FunctionalViability/ExtendedCoverage.lean)
- [YuleAmbiguity.lean](../../proofs/MemoryPrediction/YuleAmbiguity.lean)

## Verification

The [verification notes](../../VERIFICATION.md) explain the saved compilation and axiom-audit records. See the [build guide](../../BUILD.md) to reproduce a selected paper.
