# Corrected Optimal-Affinity theorem index

## Strictly verified Lean interfaces

- `OptimalAffinityCorrected.responseProfileBound_applies_at_optimum`: the constrained response-profile infimum lower-bounds every represented positive-mode optimum.
- `OptimalAffinityCorrected.correctedTheoryClosure`: terminal adapter combining the general response bound, recycling family, zero-diagonal obstruction, and productive-fraction correction.
- `OptimalAffinityCorrected.recyclingMultiplicityDestroysUniformGap`: for `m>1` and `1<r<2`, the family value lies strictly between `1+1/m` and `2`.
- `OptimalAffinityCorrected.zeroDiagonalDoesNotRestoreGrossBound`: the source-valid zero-diagonal circuit has a global optimum with exponential affinity `9/5<2`.
- `OptimalAffinityCorrected.productiveFractionReplacesGrossGain`: in the leakage motif the effective gain `1+theta(B-1)` lies in `[1,B)` for `B>1` and `0<=theta<1`.

Strict receipt: `verification/Main.verify.json`. Proof source SHA-256: `e51ef928df1b2841c4c1d0de31e709262be0d9d419434c2adfd94bf23dfd12f4`.

## Exact analytic certificates outside the fully generalized Lean surface

- The `m`-family global maximum follows from the factorization of `H_1'(y)` and the comparison `H_J(y)<H_1(y)` for `J>1`.
- The zero-diagonal circuit global maximum follows from the exact nonnegative identity recorded in `circuit_fixture.json` and `FALSIFIER_REGISTRY.json`.

These analytic certificates are source-level exact arguments; Lean verifies their specialized algebraic consequences and the terminal structural adapter, not a fully generic mass-action realizability theorem.
