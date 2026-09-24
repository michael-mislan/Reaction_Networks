# FER entropy source map

| Claim | Status | Source / local interface |
|---|---|---|
| Unrestricted Frankl half-frequency theorem | Open | Root target |
| RAF/Frankl exact equivalence | Compiled inherited foundation | `proofs/RAF/Frankl/PairGadget.lean` |
| Binary entropy API | Compiled dependency | mathlib `Mathlib.Analysis.SpecialFunctions.BinaryEntropy` |
| Boppana inequality | Strictly compiled locally | `proofs/RAF/FranklEntropy/Frontier/Boppana.lean`; Ho arXiv:2601.19327 |
| Sharp two-variable Boppana inequality | Strictly compiled locally | `proofs/UCFrankl/DiagonalReduction.lean`, `UCFrankl.weakBoppana_sharp` |
| Sawin constant `(3-sqrt 5)/2` | Strictly compiled locally, unconditional | `proofs/UCFrankl/DiagonalReduction.lean`, `UCFrankl.franklWithConstant_psi` |
| Yu approximately 0.38234 frontier | Numerical optimization; exact local certificate pending | Yu coupling optimization |
| Liu approximately 0.38271 frontier | Conditional-numerical | Optimizer-structure hypotheses must remain explicit |
| Exact provenance identity | Strictly compiled locally | `proofs/RAF/FranklEntropy/Union/ProvenanceIdentity.lean` |
| Four-row union-neighborhood fan with distinct labels | Exactly impossible; strict compiled witness- and family-level theorems | `proofs/RAF/FranklEntropy/Structural/FourFanCollision.lean`, `RAF.FranklEntropy.fourFan_union_collision`, `fourFan_collision_of_realized_neighborhoods`, and `fourFan_escape_of_distinct_realized` |
| Full four-fan quantitative escape | Strictly compiled locally: at least two distinct escape events among twelve; uniform escape probability at least `1/6` | `proofs/RAF/FranklEntropy/Structural/FourFanTwoEscape.lean`, `proofs/RAF/FranklEntropy/Structural/FourFanEscapeMass.lean`; `fourFan_two_distinct_escape_events`, `two_le_fourFanEscapeCount`, `fourFan_uniform_escapeProbability_ge_one_sixth` |
| Full four-fan modal fiber | Strictly compiled locally: every local output value has multiplicity at most `9/16` | `proofs/RAF/FranklEntropy/Structural/FourFanModalFiber.lean`; `fourFanModalFiberCount_le_nine` |
| Corrected entropy/provenance inequality | Strictly compiled locally | `proofs/RAF/FranklEntropy/Hybrid/CorrectedInequality.lean`; `entropy_union_gain_ge_rigiditySlack`, `entropy_union_strict_growth_of_rigiditySlack` |
| Four-fan entropy-gain obstruction | Strictly compiled locally: source-only zero-gain model and stronger distinct-row four-output model | `proofs/RAF/FranklEntropy/Hybrid/FourFanNoGainObstruction.lean`; `degenerateFourFan_output_sourceOnly`, `entropy_fst_sub_entropy_left_eq_zero`, `fourOutputFan_allOutputsAmongLabels`, `four_label_entropy_le_log_four` |
| Narrow exact structural oracle | Strictly compiled locally | `proofs/RAF/FranklEntropy/Structural/Oracle.lean`; imports the collision and quantitative escape interfaces |

## Compatibility facts

- Pinned project: Lean 4.30.0, mathlib revision `c5ea00351c28e24afc9f0f84379aa41082b1188f`.
- External Boppana formalization: Lean 4.24.0, mathlib revision `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`.
- The external file contains no `sorry` or explicit axioms, but uses unlimited heartbeats and must be rebuilt under the pinned warning-as-error verifier before it is admissible here.
- The full UCFrankl chain was audited at Demonstrandum commit `c03d9915394e6e4906f1447680ed62eda0a023b7`, ported under `proofs/UCFrankl/`, repaired only for strict linter compatibility, and independently rebuilt by `scripts/verify_proof.py`; see `FER/EXTERNAL_UCFRANKL_PROVENANCE.md` and `FER/UCFranklPsi.verify.json`.
