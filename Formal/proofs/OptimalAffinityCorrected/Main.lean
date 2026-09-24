import proofs.OptimalAffinityCorrected.ResponseProfile
import proofs.OptimalAffinityCorrected.RecyclingFamily
import proofs.OptimalAffinityCorrected.ZeroDiagonalCircuit

namespace OptimalAffinityCorrected

noncomputable section

theorem zeroDiagonalDoesNotRestoreGrossBound :
    CircuitSourceValid ∧
    (∀ i, circuitT i i = 0) ∧
    CircuitSteady 1 1 1 ∧
    (∀ x y z : ℝ, 0 < x → 0 < y → 0 < z → CircuitSteady x y z →
      circuitJ1 x y ≤ circuitJ1 1 1) ∧
    (9 / 5 : ℝ) < 2 := by
  exact ⟨circuit_isSourceValid, circuit_responseMatrix_zeroDiagonal,
    circuit_one_state_steady, circuit_uniqueGlobalMaximum.2.1,
    circuit_affinityViolation.2⟩

theorem recyclingMultiplicityDestroysUniformGap (m r : ℝ)
    (hm : 1 < m) (hr1 : 1 < r) (hr2 : r < 2) :
    (m + 1) / m < recyclingFamilyExpAffinity m r ∧
      recyclingFamilyExpAffinity m r < 2 := by
  exact ⟨recyclingFamily_above_profile_infimum m r hm hr1,
    recyclingFamily_violates_gross_two m r hm hr2⟩

theorem productiveFractionReplacesGrossGain (gross productiveFraction : ℝ)
    (hgross : 1 < gross) (hf0 : 0 ≤ productiveFraction)
    (hf1 : productiveFraction < 1) :
    1 ≤ leakageAdjustedGain gross productiveFraction ∧
      leakageAdjustedGain gross productiveFraction < gross :=
  leakageAdjustedGain_lt_gross gross productiveFraction hgross hf0 hf1

def CorrectedTheoryClosure : Prop :=
  (∀ (n : ℕ) (T : Fin n → Fin n → ℝ) (g : Fin n → ℕ)
      (f : Fin n → ℝ) (expAffinity : ℝ),
      ForwardResponse T f →
      expAffinity = responseObjective T g f →
      responseProfileBound T g ≤ expAffinity) ∧
  (∀ m r : ℝ, 1 < m → 1 < r → r < 2 →
      (m + 1) / m < recyclingFamilyExpAffinity m r ∧
      recyclingFamilyExpAffinity m r < 2) ∧
  (CircuitSourceValid ∧ (∀ i, circuitT i i = 0) ∧
      CircuitSteady 1 1 1 ∧ (9 / 5 : ℝ) < 2) ∧
  (∀ gross productiveFraction : ℝ,
      1 < gross → 0 ≤ productiveFraction → productiveFraction < 1 →
      1 ≤ leakageAdjustedGain gross productiveFraction ∧
      leakageAdjustedGain gross productiveFraction < gross)

theorem correctedTheoryClosure : CorrectedTheoryClosure := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n T g f expAffinity hf hopt
    exact responseProfileBound_applies_at_optimum T g f expAffinity hf hopt
  · intro m r hm hr1 hr2
    exact recyclingMultiplicityDestroysUniformGap m r hm hr1 hr2
  · exact ⟨circuit_isSourceValid, circuit_responseMatrix_zeroDiagonal,
      circuit_one_state_steady, circuit_affinityViolation.2⟩
  · intro gross productiveFraction hgross hf0 hf1
    exact productiveFractionReplacesGrossGain gross productiveFraction hgross hf0 hf1

end
end OptimalAffinityCorrected
