import proofs.RandomViability.BindingOperatingSuccess
import proofs.RandomViability.BindingDisabledProbability

namespace RandomViability.Binding
noncomputable section
open scoped BigOperators

theorem inverse_bias_nonneg (K : ℝ) (hK : K∈Set.Icc 8 12) : 0≤1/K := by
  have h : 0<K := by linarith [hK.1]
  positivity

theorem inverse_bias_upper (K : ℝ) (hK : K∈Set.Icc 8 12) : 1/K≤1/8 := by
  have h : 0<K := by linarith [hK.1]
  apply (div_le_div_iff₀ h (by norm_num : (0:ℝ)<8)).mpr
  linarith [hK.1]

theorem countMass_units (N : Counts) : countMass N=2*(uCount N+wCount N) := by
  unfold countMass uCount wCount
  simp only [total_mass_from_units,← Finset.sum_add_distrib,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem resource_physical_mass (N : Counts) (h : resourceGood N 100000000) : countMass N≤440000000 := by
  rw [countMass_units]
  have hu := h.2.1
  have hw := h.2.2.2
  norm_num at hu hw
  linarith

theorem success_output_and_mass (X : OutputState) (h : operatingSuccess X) :
    (X.2.val:ℝ)/100000000=1/10 ∧ countMass (boxCounts (trackedCounts X.1))≤440000000 := by
  constructor
  · rw [h.2.2]
    norm_num
  · exact resource_physical_mass _ h.1

/-- Main finite-copy theorem on a nontrivial thermodynamic/release-rate box.
The successful event exports0.1V covalent mass during(500,1000] from food-only
initial counts(V,V,0,0,0,0), V=1e8. The disabled upper event conservatively
includes every resource exit and imposes no entry or residence requirement. -/
theorem finite_copy_binding_guarantee (K r : ℝ) (hK : K∈Set.Icc 8 12) (hr : r∈Set.Icc 18 22) :
    (9/10:ℝ)≤operatingExpectation (1/K) r (inverse_bias_nonneg K hK) (inverse_bias_upper K hK) hr.1 hr.2
      (FiniteCopy.FiniteKernel.eventIndicator {X | operatingSuccess X}) ∧
    disabledExpectation (1/K) r (inverse_bias_nonneg K hK) (inverse_bias_upper K hK) hr.1 hr.2
      (FiniteCopy.FiniteKernel.eventIndicator {X | X.2.val=10000000 ∨ ¬resourceGood (boxCounts X.1) 100000000})<1/5000 :=
  ⟨operating_success_lower_bound _ _ _ _ hr.1 hr.2,disabled_success_upper_bound _ _ _ _ hr.1 hr.2⟩

end
end RandomViability.Binding
