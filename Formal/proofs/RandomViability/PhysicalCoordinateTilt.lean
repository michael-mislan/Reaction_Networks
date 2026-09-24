import proofs.RandomViability.PhysicalFirstExit
import proofs.RandomViability.PhysicalCoordinateDrift

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 100000

def coordinateTiltCompensator {n : ℕ} (c : SourceMoleculeFibreConfig n) (V : NNReal)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (q : Molecule n) (θ : ℝ) (N : Molecule n → ℕ) : ℝ :=
  θ*physicalCoordinateDrift c V basal cat N q+θ^2*(96000/V)

theorem physical_coordinate_tilt_generator {n : ℕ} (hn : 2 ≤ n)
    (c : SourceMoleculeFibreConfig n) (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ) (hM : (countMass N : ℝ) ≤ 11*V)
    (hbasal : ∀ r,(basal r : ℝ) ≤ 1) (hcat : ∀ r z,(cat r z : ℝ) ≤ 16)
    (q : Molecule n) (θ : ℝ) (hθ : |θ| *(2/V) ≤ 1) :
    (∑ ch,unboundedPhysicalRate c V 1 basal cat N ch*
      (Real.exp (θ*coordinateConcentrationJump V q N ch)-1)) ≤
      coordinateTiltCompensator c V basal cat q θ N := by
  have ht := rate_exponential_tilt_bound (unboundedPhysicalRate c V 1 basal cat N)
    (coordinateConcentrationJump V q N) (unboundedPhysicalRate_nonneg c V 1 basal cat N) θ
    (fun ch => by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left (coordinate_concentration_jump_bound V hV q N ch)
        (abs_nonneg θ)).trans hθ)
  have hv := physical_coordinate_quadratic_rate hn c V hV basal cat N hM hbasal hcat q
  exact ht.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hv (sq_nonneg θ)))

/-- Reuse the generic censored-clock multiplier, with persistent mass stopping. -/
def coordinateCensoredMultiplier {n : ℕ} (c : SourceMoleculeFibreConfig n) (V : NNReal)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (q : Molecule n) (θ T : ℝ) :=
  censoredStoppedMultiplier (fun N ch => Real.exp (θ*coordinateConcentrationJump V q N ch))
    (coordinateTiltCompensator c V basal cat q θ) (fun k h => T-prefixElapsed k h)
    (censoredNonfoodStop V T (massExitStop V))

variable {n : ℕ} [MeasurableSpace (PhysicalCountChannel n)]
  [MeasurableSingletonClass (PhysicalCountChannel n)]

theorem coordinateCensoredMultiplier_measurable (c : SourceMoleculeFibreConfig n) (V : NNReal)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (q : Molecule n) (θ T : ℝ) (k : ℕ) :
    Measurable (fun p : (Finset.Iic k → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) ×
      JumpState (Molecule n → ℕ) (PhysicalCountChannel n) =>
      coordinateCensoredMultiplier c V basal cat q θ T k p.1 p.2) :=
  censoredStoppedMultiplier_measurable _ _ _
    (fun j => measurable_const.sub (prefixElapsed_measurable j)) _
    (censoredNonfoodStop_measurable V T (massExitStop V) (massExitStop_measurable V)) k

theorem physical_censored_coordinate_mean (hn : 2 ≤ n)
    (c : SourceMoleculeFibreConfig n) (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (hbasal : ∀ r,(basal r : ℝ) ≤ 1) (hcat : ∀ r z,(cat r z : ℝ) ≤ 16)
    (q : Molecule n) (θ T : ℝ) (hθ : |θ| *(2/V) ≤ 1)
    (k : ℕ) (h : Finset.Iic k → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) :
    (∫⁻ y,coordinateCensoredMultiplier c V basal cat q θ T k h y
      ∂jumpHistoryKernel unboundedPhysicalNext (unboundedPhysicalRate c V 1 basal cat)
        (unboundedPhysicalRate_nonneg c V 1 basal cat)
        (unbounded_total_pos hn c V 1 hV (by norm_num) basal cat) k h) ≤ 1 := by
  by_cases hs : censoredNonfoodStop V T (massExitStop V) k h
  · simp only [coordinateCensoredMultiplier,censoredStoppedMultiplier,if_pos hs]
    simp
  · have hsplit := not_or.mp hs
    have hM := not_not.mp (not_or.mp hsplit.2).1
    have hrem : 0 ≤ T-prefixElapsed k h := sub_nonneg.mpr (le_of_not_ge (not_or.mp hsplit.2).2)
    simp only [coordinateCensoredMultiplier,censoredStoppedMultiplier,if_neg hs]
    exact jumpState_censored_tilt_le_one unboundedPhysicalNext (unboundedPhysicalRate c V 1 basal cat)
      (unboundedPhysicalRate_nonneg c V 1 basal cat)
      (unbounded_total_pos hn c V 1 hV (by norm_num) basal cat)
      (h ⟨k,Finset.mem_Iic.mpr le_rfl⟩).1
      (coordinateConcentrationJump V q (h ⟨k,Finset.mem_Iic.mpr le_rfl⟩).1) θ
      (coordinateTiltCompensator c V basal cat q θ (h ⟨k,Finset.mem_Iic.mpr le_rfl⟩).1)
      (T-prefixElapsed k h) hrem
      (physical_coordinate_tilt_generator hn c V hV basal cat _ hM hbasal hcat q θ hθ)

/-- Both tilt signs are allowed; no derivative approximation of the clock is used. -/
theorem physical_censored_coordinate_product (hn : 2 ≤ n)
    (c : SourceMoleculeFibreConfig n) (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ)
    (hbasal : ∀ r,(basal r : ℝ) ≤ 1) (hcat : ∀ r z,(cat r z : ℝ) ≤ 16)
    (q : Molecule n) (θ T : ℝ) (hθ : |θ| *(2/V) ≤ 1) (K : ℕ) :
    (∫⁻ z,trajectoryProduct (coordinateCensoredMultiplier c V basal cat q θ T) K z
      ∂physicalTrajectoryLaw hn c V 1 hV (by norm_num) basal cat N) ≤ 1 := by
  simpa only [one_pow] using predictable_product_integral_le
    (physicalTrajectoryLaw hn c V 1 hV (by norm_num) basal cat N)
    (jumpHistoryKernel unboundedPhysicalNext (unboundedPhysicalRate c V 1 basal cat)
      (unboundedPhysicalRate_nonneg c V 1 basal cat)
      (unbounded_total_pos hn c V 1 hV (by norm_num) basal cat))
    (fun k => physicalTrajectoryLaw_transition hn c V 1 hV (by norm_num) basal cat N k)
    (coordinateCensoredMultiplier c V basal cat q θ T)
    (coordinateCensoredMultiplier_measurable c V basal cat q θ T) 1
    (physical_censored_coordinate_mean hn c V hV basal cat hbasal hcat q θ T hθ) K

end
end RandomViability

