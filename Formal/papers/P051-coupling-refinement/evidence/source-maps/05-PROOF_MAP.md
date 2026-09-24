# Final critical proof map

Paths below are relative to the repository root. All declarations are checked by `proofs/RAF1519/Publication.lean`; no table entry relies on a failed receipt. The strict combined receipt is `../evidence/Publication.verify.json`.

| Paper obligation | Exact source / declaration | What is actually established |
|---|---|---|
| Seven-species source | `Refinement/Source.lean`, `CountSource.lean`, `CountNetwork.lean`, under `proofs/RAF1519/` | Literal 23 local labels, falling factorials, material identities and finite-count correction |
| Deterministic repeated operation | `proofs/RAF1519/Refinement/Repeated.lean`: `RAF1519.Refinement.R15_D` | Actual pulses, carried D, global flow, Ready return, product, food and service on all finite prefixes; beta=.01 and 0<theta<=.01 |
| Arbitrary tolerance concentration | `Refinement/NoiseBudget.lean`: `molecular_coordinate_budget` | Actual censored coordinate law, epsilon>0, epsilon<=1, V>=40/epsilon |
| Revised actual corridors | `TolerancePath.lean`, `RelaxedCorridors.lean` | First-exit removal and all-time material/D bounds at epsilon=1/[10000(1+Delta)] |
| Revised productive output | `QuantitativeStock.lean`, `RelaxedStock.lean` | Compensated stock fence and literal phase adjoint, not a differentiable-count assumption |
| Physical integer event | `RelaxedOperating.lean`: `RAF1519.Refinement.Relaxed.integerCycleSuccess_of_operating` | Weaker sufficient product margins imply the original ceil/floor event and actual endpoint Ready |
| One-cycle probability | `RelaxedProbability.lean`: `RAF1519.Refinement.Relaxed.pulseFlow_integer_failure` | Literal pulse and flow law, full union bound, 29n prefactor |
| Improved mission | `RelaxedMission.lean`: `RAF1519.Refinement.Relaxed.R15_S` | All logged successes under unrestricted full-history law, denominator 2e12(1+Delta)^3 |
| Concrete law | Original `ReturnedHistory.lean`: `returnedPhysicalHistory`; new `RelaxedMission.lean`: `returned_mission` | Constructed normalized law for arbitrary policies on prior returned states and counters |
| Smaller connected instance | `RelaxedInstance.lean`: `RAF1519.Refinement.Relaxed.connected_hundred_cycle_mission` | V=224000000000000, n=2, degree=1, 100 cycles, probability strictly greater than .99 |
| Sizing and yield | `MissionAccounting.lean`: `RAF1519.Refinement.Relaxed.mission_size`, `successful_cycle_yield` | Logarithmic sufficient scale and division-free natural-count food/product bounds |
| Two attracting communities | `proofs/RAF1519/Reservoir/Attractors.lean`: `RAF1519.Reservoir.R19` | Positive equilibria, equal prescribed proportions, strict abundance/uptake separation, full-community local attraction |
| Scalar root existence | `Reservoir/Scalar.lean`, `RootBoxes.lean` and imported root certificates | Exact residual reduction, opposite rational endpoint signs, IVT and enclosure |
| Full-state attraction | `CoreEnergy.lean`, `CommunityCoercivity.lean`, `CommunityAttraction.lean` | Rational secant decay, additional consumer variance modes, actual invariant local solution |
| Readout | `FunctionalReadout.lean`: `RAF1519.Reservoir.transient_composition_readout`, `abundance_readout_error` | Literal transient identity and abundance-error bound, with explicit derivative/dispersion assumptions |
| Finite windows | `WindowReadout.lean`: `RAF1519.Reservoir.finite_window_readout`, `reservoir_window_readout` | Actual source trajectory integrals; continuity and integrability are derived |
| Resident bridge | `FeedbackLoad.lean`: `RAF1519.Reservoir.resident_feedback_identity` | Resident projection equals `ProductiveMemory.extractDrift` at load RS and zero finite-size correction |
| Stationary cap and curve | `FunctionalReadout.lean`: `stationary_supply_cap`; `FeedbackLoad.lean`: `stationary_load_curve` | RS<=.025 for nonnegative equilibria; necessary curve for prescribed composition |
| Observable recovery | `ObservableRecovery.lean`: `RAF1519.Reservoir.source_observable_recovery`, `observable_deadline` | Source-specific invariant-sublevel construction and explicit uptake envelope/deadline. The radius and bounding box remain parameters with stated local conditions |

The high-z resident exclusion comparison at load .031 is `ProductiveMemory.no_high_stationary_above_boundary` in `proofs/ProductiveMemory/ExtractionBoundary.lean`; its condition is z>=2. Only the deterministic drift identity is imported into the new bridge. No #16 copying or probability conclusion is asserted for the reservoir community.

Numerical figures are not formal certificates. The uptake measurement classification follows by interval monotonicity and the triangle inequality from the certified root intervals; its exact rational data are provided. Optional sharper maxima of the necessary load curve, expectation theorems, global basins, and new inheritance protocols are not part of the paper or required proof path.
