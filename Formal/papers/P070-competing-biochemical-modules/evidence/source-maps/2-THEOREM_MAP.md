# Theorem-to-module map

All paths below are relative to proofs/DynamicSharedResource. Main.lean and all
listed dynamic modules have passed strict compilation; verification/Main.json
contains the authenticated root interface and all local dependency hashes.
This map explains those results and is not itself a verification receipt.

| Guide obligation | Module and declaration | What it supplies |
|---|---|---|
| Literal source and observable dictionary | Model.lean: field, nominal, Physical, HG, HT | Exact eight-state source, rates, services, physical domain |
| Transient accounts | Model.lean: bufferG_hasDerivAt, bufferT_hasDerivAt, resource_hasDerivAt, peroxide_velocity | Identities after substitution of the literal field |
| Actual nonlinear expansion | Algebra.lean: nominal_expansion | Five mass-action products plus the exact rational source remainder |
| Fixed rational data | Data.lean: inverse_basis, basis_inverse | All entries of the coordinate inverse identities |
| General estimates | Bounds.lean: faceDecay_of_bounds; Remainder.lean: products_bound, source_remainder_bound | Uniform state-space inequalities, including center residual |
| Exact numerical obligations | Checks.lean: jac_center, inverse_jac, left_basis, inverse_reaction, field_center, inverse_field, numerical_face_margin, nb_formula | Kernel-checked fixed rational arithmetic |
| PRODUCTIVE-TRAP inward inequality | SourceCertificate.lean: nominal_face_decay | FaceDecay for the literal transformed source |
| PRODUCTIVE-TRAP physicality and services | PhysicalService.lean: outer_physical, inner_service | Physical outer box and both inner-box quotas |
| Explicit preparation | PhysicalService.lean: Prepared, prepared_contains_ball, preparation_fails, prepared_in_outer | Positive ordinary coordinate width, deficient center, outer inclusion |
| PREPARATION-CAPTURE | BoxFlow.lean: moving_cube, cube_capture | Finite-face barrier and 2000-second shrinking-box capture |
| LITERAL-FLOW existence | GlobalFlow.lean: cube_global_extension, exists_captured_solution | Global bounded extension, with the actual field recovered by invariance |
| Source regularity and derivative conversion | Regularity.lean: nominal_contDiffAt, affine_contDiff, mulVec_hasDerivAt | Smooth source away from pole and exact coordinate derivative mapping |
| Source-instantiated existence/capture | Resolution.lean: source_solution_exists | Actual forward solution from every Prepared state |
| Universal trajectory guarantee | EveryTrajectory.lean: every_source_trajectory, dynamic_shared_resource_root | Physicality and eventual service without assuming either in the trajectory hypotheses |
| Forward uniqueness | Uniqueness.lean: source_solution_unique | Equality for all nonnegative times from the same initial state |
| Cumulative service | ServiceWindows.lean: cumulative_service, exists_sustained_service | Every later service window on the same solution |
| Integrated accounts | Accounts.lean: resource_account, buffer_accounts, peroxide_account | NADPH/buffer/externally supported repair accounting on arbitrary forward intervals |
| ROOT-DYNAMIC-SHARED-RESOURCE | Main.lean: dynamic_compatibility | Positive preparation width, deficient state, global existence, uniqueness, physicality, finite capture, sustained service, cumulative service, exact resource account |

Inherited formal inputs are C4Assemblies.Comparison's finite strict barrier and
CoreCouplingCAC.GlobalExistence's bounded Lipschitz global solution theorem.
They do not assume this source's capture or service result. Mathlib supplies
calculus, Lipschitz extension, ODE uniqueness, and interval integration.

The operating-point connection in OPERATING_POINT.md uses the inherited
CommonEnvironmentProtection/Main.lean equilibrium result and a conventional
Poincare–Miranda argument. The dynamic proof avoids assuming its rational center
is stationary. OBSTRUCTIONS.md gives conventional proofs of zero-slack failure
and the matched-rate repair obstruction; those are not advertised as newly
kernel-checked obstruction theorems. Numerical evidence is identified separately
in HANDOFF_REPORT.md and SCORECARD.md.
