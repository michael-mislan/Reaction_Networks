# Theorem index

This index records the terminal proof surface. Fully qualified names begin with
`OptimalAffinityRealizability.` unless stated otherwise.

## Root and raw-source interface

- `rawSquareSource_capacityEquality` — literal `SquareSource` adapter proving equality
  of response-layer and strict-local capacities on the accessible irreducible class.
- `optimalAffinityKineticRealizabilityResolution` — named root theorem packaging the
  local-capacity resolution, the integer-power global resolution, and the interacting-
  core boundary resolution.

## Local kinetic realizability and capacity

- `exists_firstOrderSourceRealization` — reconstructs positive one-way flows and rates.
- `exists_regularStrictLocalSourceCertificate` and
  `regularStrictLocalSourceRealization` — actual positive local branch with strict local
  flux maximum.
- `responseLayerCapacity_eq_strictLocalCapacity_of_accessibleIrreducible` — local
  capacity equality on the explicit accessible irreducible response class.
- `interiorLogProfileKKT_iff_routingStationary` and
  `interiorLogProfileMinimizer_implies_routingStationary` — matrix-scaling KKT bridge.
- Boundary-gauge lemmas in `BoundaryGauge.lean` — nonblowing representatives along
  accessible response rays.

## Exact global realizability

- `twoByTwoFixture_stationary_elimination` and `twoByTwoFixture_uniqueGlobal` — exact
  two-reaction global witness and factorized gap proof.
- `powerFamily_uniqueGlobal` — unique global realization for every integer exponent
  `d >= 2` in the new power family.
- `powerFamilyGlobalValueSet_eq_localValueSet` and
  `powerFamilyGlobalCapacity_eq_localCapacity` — exact global/local equality for that
  family.
- `uniqueGlobalRealizable_iff_correctedGlobalProfile` — corrected invariant: global
  realizability is equivalent to the explicit global stationary-fiber gap certificate,
  not to response data alone.

## Interacting-core boundary

- `squareSource_reactionwiseMagnitudeAutomatic` — the square-source thermodynamic
  magnitude condition is automatic in the stated single-source setting.
- `interacting_direction_does_not_imply_magnitude` and
  `interacting_linearComplex_does_not_imply_speciesActivity` — exact countertheorems
  separating direction, magnitude, toric, and species-activity layers.
- `directionOnly_articulation_refuted` and
  `linearComplexOnly_articulation_refuted` — precise articulation counterboundaries.
- `LayeredInteractingCoreRealization`, `TypedKineticBoundaryRelation`,
  `BoundaryRelationsJoinable`, and `JoinedBoundaryProjection` — typed six-layer
  compatibility interface.

## Receipts and experiment registries

- Terminal receipt: `verification/TerminalRoot.verify.json`.
- Per-module strict receipts: `verification/*.verify.json`.
- Hypothesis cycles: `HYPOTHESIS_CYCLE_LEDGER.jsonl`.
- Counterexamples and ablations: `COUNTEREXAMPLE_REGISTRY.json`.
- Fixed guide score: `CHECKLIST.json`.
- Exact numerical outputs: `*_preflight_result.json`, `global_root_audit_result.json`,
  and `same_response_pair_search_result.json`.
