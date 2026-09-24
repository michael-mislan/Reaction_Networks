# Verified interfaces used by C4

All paths below are repository-relative; namespace ProductiveRecovery unless stated.

| Module | Declaration | Relevant assumptions/conclusion |
|---|---|---|
| proofs/ProductiveRecovery/Source.lean | field, flux, flux_coefficients | Six literal paired fluxes at maintained F/P activities |
| proofs/ProductiveRecovery/SourceCorrespondence.lean | field_stoichiometry | C0 reaction increments plus unit food feed and six washouts |
| proofs/ProductiveRecovery/StrongGrowth.lean | strong_guarded_growth | Nonneg, 19<=r<=21, 0<=d<=1/25, A/B>=9/10, Y<=1/20 imply Y(field)>=(2/3)Y |
| proofs/ProductiveRecovery/PhaseComparison.lean | phase_comparison | Same parameter box and A/B<=11/10 give four phase lower inequalities |
| proofs/ProductiveRecovery/StrongScalar.lean | strong_scheduled_recovery | Scalar differentiable curve plus guarded drift, retained floor and exponential deadline |
| proofs/ProductiveRecovery/PostproofResolution.lean | conditioned_productive_operation | Actual isolated source flow, conditioning at 12, routine return at 3/4 and free-X output |
| proofs/ProductiveRecovery/SourceFlow.lean | global_nonnegative_solution | Polynomial cutoff/positive-part construction; scalar material barriers are isolated-source specific |

The current strong modules match the guide; the old C1 HANDOFF describes the
earlier Y=1/2500 result and must not override these source signatures.
The strong growth result is used directly in the compiled C4 adapter, with
no presumed assembled return or presumed growth hypothesis.

New receipt Source.verify.json: verified true, exit zero, empty stdout/stderr,
Lean 4.30.0, warningAsError; only propext, Classical.choice, Quot.sound.
It includes Transport.lean as a freshly compiled dependency. The C4 proofs
already give exact A/B/Y transport identities, conservative total diffusion,
the favorable sign at a minimum and the source-specific guarded growth there.
That early source-only receipt did not itself prove finite-time order preservation
or global assembled flow. Both were subsequently closed in Examples.verify.json;
the strengthened publication root is now verified in Publication.verify.json.
