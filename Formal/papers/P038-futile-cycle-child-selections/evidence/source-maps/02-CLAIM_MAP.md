# Declaration-to-claim map

All paths below are repository-relative. The strict resolution receipt is the
final intended authority for the transitive proof closure; older failed attempt
receipts remain diagnostic history. No numerical result is an input assumption
of the Lean theorems. The aggregate root compiled strictly in 60.203 seconds;
the verifier-authenticated declaration export passed in 25.938 seconds. The four
exported declarations are `FutileCycle.resolution`, `FutileCycle.positive_core_all_n`,
`FutileCycle.negative_core_all_n`, and `FutileCycle.allN_child_det`. Each has exactly
the standard axiom set `Classical.choice`, `Quot.sound`, `propext`.

| Claim | Declaration | Proof file | Current evidence |
|---|---|---|---|
| Literal finite source and injective reactant-supported child | `ConversionSystem`, `Child`, `futile` | `proofs/FutileCycle/Source.lean` | Compiled |
| Every elementary-conversion child has determinant 0 or ±1 | `child_det_bound` | `proofs/FutileCycle/AllNDeterminant.lean` | Compiled, exported |
| All-n futile-cycle determinant specialization | `allN_child_det` | same | Compiled, exported |
| Actual negative-witness RHP eigenpair | `negative_unstable` | `proofs/FutileCycle/NegativeSpectrum.lean` | Compiled |
| All proper negative-witness restrictions nonunstable | `negative_principal_no_rhp` | `proofs/FutileCycle/NegativeMinimality.lean` | Compiled |
| Literal minimal negative core, determinant +1, every n≥3 | `negative_core_all_n` | `proofs/FutileCycle/NegativeCore.lean` | Compiled |
| Arbitrary-n positive source assignment and dimension 2n+1 | `positiveChild`, `positive_dimension` | `proofs/FutileCycle/PositiveSource.lean` | Compiled |
| Literal source equals sign-conjugate flower | `positive_source_flower` | `proofs/FutileCycle/PositiveStructure.lean` | Compiled |
| Uniform flower determinant | `flowerMatrix_det` | `proofs/FutileCycle/FlowerMatrix.lean` | Compiled |
| Uniform RHP eigenpair | `flower_eigenpair` | `proofs/FutileCycle/FlowerSpectrum.lean` | Compiled |
| Every proper flower restriction excludes RHP roots under all positive scalings | `flower_scaled_no_rhp` | `proofs/FutileCycle/FlowerScaledMinimality.lean` | Compiled |
| Literal positive determinant, instability and minimality | `positive_det`, `positive_unstable`, `positive_minimal` | `proofs/FutileCycle/PositiveCore.lean` | Compiled |
| Literal positive proper restrictions under every positive scaling | `positive_proper_scaling` | same | Compiled |
| All-positive assertion refuted | `not_all_positive` | `proofs/FutileCycle/Resolution.lean` | Compiled |
| Unbounded literal sizes of positive cores | `no_literal_positive_bound` | same | Compiled |
| Literal all-n positive family, including scaling extension | `positive_core_all_n` | same | Compiled |
| Combined exact source resolution | `resolution` | same | Compiled |

## Evidence boundaries

The guide's characteristic-polynomial identities, rank 3n discussion, tree
criterion, and source-paper reconciliation are retained as conventional evidence
unless a declaration above explicitly covers them. The compiled spectral proofs
use explicit eigenvectors, reciprocal-root identities and contraction/Lyapunov
arguments. They do not import the characteristic-polynomial formulas as axioms.

The n=2 census, witness restriction audits, exact LDL diagnostic, family formula
checks and FC-10 flower pilot are local executed evidence. The n=3 full census
was supplied by the guide and was not rerun. The finite negative-mask theorem
is kernel-evaluated by `decide`; it does not trust the Python generator or
`native_decide` for soundness or coverage.

No theorem here asserts a mass-action Hopf bifurcation, realizability of every
column scaling by kinetics, persistence, uniqueness of steady states, or a
classification modulo graph subdivision/contraction. The size refutation uses
the literal number of selected species with principal restriction as minimality.
