import proofs.CompositionalMemory.SemenovLowEndpoint
import proofs.CompositionalMemory.SemenovHighEndpoint
import proofs.CompositionalMemory.SemenovEndpointGeometry
import proofs.CompositionalMemory.SemenovRecoveryPieces
import proofs.CompositionalMemory.SemenovRecoveryRegion

namespace CompositionalMemory.Semenov.SemenovEndpointBounds
open Matrix SemenovRecoveryPieces

theorem low_refill_comparison (v : Fin 8 → ℝ) :
    matrixEnergy (rationalMatrix SemenovLowInitialMetric.pl) ((1/2 : ℝ) • v) ≤
      (SemenovLowEndpoint.ratio : ℝ)*matrixEnergy (rationalMatrix SemenovLowMetric15.pr) v := by
  apply refill_energy_comparison
  intro x
  have hh := rational_congruence_nonneg SemenovLowEndpoint.M SemenovLowEndpoint.A
    SemenovLowEndpoint.finite_checks.1 SemenovLowEndpoint.finite_checks.2.1
    SemenovLowEndpoint.finite_checks.2.2.1 SemenovLowEndpoint.finite_checks.2.2.2.2.1
    SemenovLowEndpoint.finite_checks.2.2.2.1 x
  change 0 ≤ matrixEnergy (fun i j =>
    ((SemenovLowEndpoint.ratio*SemenovLowMetric15.pr i j-SemenovLowInitialMetric.pl i j/4 : ℚ) : ℝ)) x at hh
  push_cast at hh
  exact hh

theorem low_initial_nonneg (v : Fin 8 → ℝ) :
    0 ≤ matrixEnergy (rationalMatrix SemenovLowInitialMetric.pl) v :=
  (lowPiece00.left_metric_bounds v).1

theorem low_initial_symmetric :
    ∀ i j,rationalMatrix SemenovLowInitialMetric.pl i j=rationalMatrix SemenovLowInitialMetric.pl j i := by
  have hh := lowPiece00.coefficient_symmetry (-1)
  change ∀ i j,coefficientMatrix lowPiece00.pc (-1) i j=
    coefficientMatrix lowPiece00.pc (-1) j i at hh
  rw [lowPiece00.left_matrix] at hh
  exact hh

theorem low_initial_upper (v : Fin 8 → ℝ) :
    matrixEnergy (rationalMatrix SemenovLowInitialMetric.pl) v ≤ (1601 : ℝ)*vectorSquares v := by
  apply (le_abs_self _).trans
  apply matrix_energy_norm_bound _ low_initial_symmetric
  intro i
  have hh := SemenovLowEndpoint.finite_checks.2.2.2.2.2.1 i
  change (∑ j,|(SemenovLowInitialMetric.pl i j : ℝ)|) ≤ (1601 : ℝ)
  norm_num only [div_one] at hh
  exact_mod_cast hh

theorem low_terminal_radius (v : Fin 8 → ℝ)
    (hv : matrixEnergy (rationalMatrix SemenovLowMetric15.pr) v ≤ (SemenovLowMetric15.eta : ℝ)) :
    vectorSquares v ≤ (SemenovLowMetric15.radius : ℝ)^2 := by
  apply lowPiece15.right_radius_bound v
  convert hv using 1
  norm_num [recoveryEta,SemenovLowMetric15.eta]

theorem high_refill_comparison (v : Fin 8 → ℝ) :
    matrixEnergy (rationalMatrix SemenovHighInitialMetric.pl) ((1/2 : ℝ) • v) ≤
      (SemenovHighEndpoint.ratio : ℝ)*matrixEnergy (rationalMatrix SemenovHighMetric21.pr) v := by
  apply refill_energy_comparison
  intro x
  have hh := rational_congruence_nonneg SemenovHighEndpoint.M SemenovHighEndpoint.A
    SemenovHighEndpoint.finite_checks.1 SemenovHighEndpoint.finite_checks.2.1
    SemenovHighEndpoint.finite_checks.2.2.1 SemenovHighEndpoint.finite_checks.2.2.2.2.1
    SemenovHighEndpoint.finite_checks.2.2.2.1 x
  change 0 ≤ matrixEnergy (fun i j =>
    ((SemenovHighEndpoint.ratio*SemenovHighMetric21.pr i j-SemenovHighInitialMetric.pl i j/4 : ℚ) : ℝ)) x at hh
  push_cast at hh
  exact hh

theorem high_initial_nonneg (v : Fin 8 → ℝ) :
    0 ≤ matrixEnergy (rationalMatrix SemenovHighInitialMetric.pl) v :=
  (highPiece00.left_metric_bounds v).1

theorem high_initial_symmetric :
    ∀ i j,rationalMatrix SemenovHighInitialMetric.pl i j=rationalMatrix SemenovHighInitialMetric.pl j i := by
  have hh := highPiece00.coefficient_symmetry (-1)
  change ∀ i j,coefficientMatrix highPiece00.pc (-1) i j=
    coefficientMatrix highPiece00.pc (-1) j i at hh
  rw [highPiece00.left_matrix] at hh
  exact hh

theorem high_initial_upper (v : Fin 8 → ℝ) :
    matrixEnergy (rationalMatrix SemenovHighInitialMetric.pl) v ≤ (3818 : ℝ)*vectorSquares v := by
  apply (le_abs_self _).trans
  apply matrix_energy_norm_bound _ high_initial_symmetric
  intro i
  have hh := SemenovHighEndpoint.finite_checks.2.2.2.2.2.1 i
  change (∑ j,|(SemenovHighInitialMetric.pl i j : ℝ)|) ≤ (3818 : ℝ)
  norm_num only [div_one] at hh
  exact_mod_cast hh

theorem high_terminal_radius (v : Fin 8 → ℝ)
    (hv : matrixEnergy (rationalMatrix SemenovHighMetric21.pr) v ≤ (SemenovHighMetric21.eta : ℝ)) :
    vectorSquares v ≤ (SemenovHighMetric21.radius : ℝ)^2 := by
  apply highPiece21.right_radius_bound v
  exact hv

end CompositionalMemory.Semenov.SemenovEndpointBounds
