# Publication claim and evidence map

All proof paths below are relative to `E:\Erdos Problems`. Lean names in the
RepeatedFunction files are in namespace `RandomViability`.

| Paper claim | Critical evidence | Scope |
| --- | --- | --- |
| Literal source, marks, initialized process, mission | `proofs/RepeatedFunction/Mission.lean`, `MissionMeasurable.lean`; definitions imported by `C6Resolution.lean` | Existing formal definitions; no model replacement |
| Interval potential, mass integral, two exports | `IntervalPotential.lean`, `IntervalPath.lean`, `IntervalMass.lean`: `physical_interval_mass_from_noise`; `IntervalExport.lean`: `physical_interval_export_lower`, `interval_export_margin` | Existing compiled interval chain |
| Endpoint stock, supply, actual probability | `MissionPath.lean`, `MissionProbability.lean`: `physical_two_window_ae`, `physical_two_window_failure_tail` | Same initialized trajectory and actual law |
| Uniform witness and exact source averaging | `SourceLower.lean`: `concrete_two_window_success_lower`, `fully_averaged_two_window_lower` | Direct uniform bound needs V >= 2n/d; convenient root envelope is stronger |
| Finite converse | `FiniteConverse.lean`: `averaged_mission_finite_upper`; `EnsembleBounds.lean` | Original formal coefficient 15480 |
| Root theorem | `C6Resolution.lean`: `c6_two_window_resolution` | Original strict receipt; 425 local dependencies, standard axioms only |
| Productive census | `ProductiveCensus.lean`: `productive_labels_four`, `productive_labels_card_le`, `productive_union_iff` | New strict bundle checks 224 at cap four, injection for all n, exact productive predicate |
| 224 source probability coefficient | Section 5.3 | Written union-bound proof, using equal incidence marginals; not a claimed new terminal probability export |
| Signed synthesis | `NetSynthesis.lean`: `actual_net_synthesis_identity`, `food_only_mission_net_synthesis`; `MissionAccounts.lean` | Original compiled pathwise account, actual-law almost-sure interpretation |
| Material fraction | Section 5.4; `StartupNecessary.lean`: `mission_material_recovery` | Written application to normalized account; scalar inequality checked |
| Source and residual limits | `proofs/PowerLawSmallRAF/SourceCriticalSecondMoment.lean`: `sourceExactCriticalFirstMoment_scaled_tendsto`; `proofs/RepeatedFunction/MissionAsymptotics.lean`: `mission_residual_relative_tendsto_zero`, `two_window_noise_tendsto_zero` | Inherited exact capped-source limits |
| Full gamma and gamma/224 limits; 2^-n rarity | Theorem 4.2 and Section 6.1 | Conventional limiting argument; no assumed exact success coefficient |
| Screening, reliability, transfer implications | Sections 6.1–6.3 | Conventional consequences with complete assumptions in text |
| Positive limiting structural RAF probability | `proofs/PowerLawSmallRAF/Main.lean`: `source_RAF_probability_tendsto`, `sourceCriticalSurvival_pos` | Same capped source; not an IID substitution |
| Disabled baseline and unique local mechanism | `proofs/RandomViability/PhysicalOutputProbability.lean`, `LocalMultiplicity.lean`; mission inclusion | Inherited law/row bounds plus written transfer |
| First-birth rate and finite survival | `StartupNecessary.lean`: `food_pair_birth_bound`, `startup_intensity_bound`, `startup_survival_lower`, `startup_necessary_scale` | New checked algebra and finite-kernel induction |
| Stopped first-birth actual-law ceiling | Theorem 7.1 | Complete conventional finite-state uniformization proof, including safe absorption at exit and Poisson mixing |
| Refined sufficient volume | Equation (39), inherited direct conditional theorem | Written rearrangement; does not alter converse assumptions |
| Small-cap converse obstruction | Equation (40) | Exact row-independence calculation, high-precision evaluation |
| Chosen-source example | Section 8.2, `scripts/experiments.py`, raw data | Numerical illustration, not probability-theorem evidence |

## Direct predecessor manuscripts

The bibliography's local manuscripts are bundled in this repository:

- `problem_workspaces/RAF_can_diffuse_RAFs_achieve_productive_operation/paper/main.tex`, version 14 September 2026.
- `problem_workspaces/RAF_Emergence_Dynamic_Viable_Autocatalysis_Random_Networks/paper/main.tex`, version 10 September 2026.

These contain the inherited source/kinetic estimates. The current paper cites
them rather than presenting inherited discoveries as new. The machine-readable
map records source and receipt fingerprints, checked declaration interfaces,
and precise evidence categories. The manuscript does not claim arbitrary-state
restart, infinite-time persistence, equal motif weights, or a named external
conjecture beyond the literal finite-horizon theorem.
