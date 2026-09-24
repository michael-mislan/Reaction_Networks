import proofs.RandomViability.CollectiveClockTilt
import proofs.RandomViability.CollectiveNormalizedVariance
import proofs.RandomViability.PhysicalTrajectory
import proofs.RandomViability.ChronologicalReward
import proofs.RandomViability.PredictableProductBounds
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 80000

def nonfoodTiltCompensator {n : ℕ} (c : SourceMoleculeFibreConfig n) (V : NNReal)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (θ : ℝ) (N : Molecule n → ℕ) : ℝ :=
  θ*(∑ ch,unboundedPhysicalRate c V 1 basal cat N ch*nonfoodConcentrationJump V N ch)+
    θ^2*((384000+11*(n : ℝ))/V)

theorem physical_nonfood_tilt_generator {n : ℕ} (hn : 4 ≤ n)
    (c : SourceMoleculeFibreConfig n) (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ) (hM : (countMass N : ℝ) ≤ 11*V)
    (hbasal : ∀ r, (basal r : ℝ) ≤ 1) (hcat : ∀ r z, (cat r z : ℝ) ≤ 16)
    (θ : ℝ) (hθ : |θ| *((n : ℝ)/V) ≤ 1) :
    (∑ ch,unboundedPhysicalRate c V 1 basal cat N ch*
      (Real.exp (θ*nonfoodConcentrationJump V N ch)-1)) ≤
      nonfoodTiltCompensator c V basal cat θ N := by
  have ht := rate_exponential_tilt_bound (unboundedPhysicalRate c V 1 basal cat N)
    (nonfoodConcentrationJump V N) (unboundedPhysicalRate_nonneg c V 1 basal cat N) θ
    (fun ch => by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left (physical_nonfood_normalized_jump hn V hV N ch)
        (abs_nonneg θ)).trans hθ)
  have hv := physical_nonfood_normalized_variance (by omega : 2 ≤ n)
    c V hV basal cat N hM hbasal hcat
  exact ht.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hv (sq_nonneg θ)))

variable {n : ℕ} [MeasurableSpace (PhysicalCountChannel n)]
  [MeasurableSingletonClass (PhysicalCountChannel n)]

theorem physical_nonfood_tilt_mean (hn : 4 ≤ n)
    (c : SourceMoleculeFibreConfig n) (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ) (hM : (countMass N : ℝ) ≤ 11*V)
    (hbasal : ∀ r, (basal r : ℝ) ≤ 1) (hcat : ∀ r z, (cat r z : ℝ) ≤ 16)
    (θ : ℝ) (hθ : |θ| *((n : ℝ)/V) ≤ 1) :
    (∫⁻ y, jumpMultiplier (fun ch => Real.exp (θ*nonfoodConcentrationJump V N ch))
      (nonfoodTiltCompensator c V basal cat θ N) y
      ∂jumpStateKernel unboundedPhysicalNext (unboundedPhysicalRate c V 1 basal cat)
        (unboundedPhysicalRate_nonneg c V 1 basal cat)
        (unbounded_total_pos (by omega : 2 ≤ n) c V 1 hV (by norm_num) basal cat) N) ≤ 1 := by
  apply jumpState_exponential_tilt_le_one
  exact physical_nonfood_tilt_generator hn c V hV basal cat N hM hbasal hcat θ hθ

def nonfoodHistoryMultiplier (c : SourceMoleculeFibreConfig n) (V : NNReal)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal) (θ : ℝ)
    (stop : (k : ℕ) → (Finset.Iic k → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) → Prop)
    (k : ℕ) (h : Finset.Iic k → JumpState (Molecule n → ℕ) (PhysicalCountChannel n))
    (y : JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) : ℝ≥0∞ :=
  stoppedStateMultiplier (fun N ch => Real.exp (θ*nonfoodConcentrationJump V N ch))
    (nonfoodTiltCompensator c V basal cat θ)
    (fun j h => stop j h ∨ ¬(countMass (h ⟨j,Finset.mem_Iic.mpr le_rfl⟩).1 : ℝ) ≤ 11*V) k h y

theorem nonfoodHistoryMultiplier_measurable (c : SourceMoleculeFibreConfig n) (V : NNReal)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal) (θ : ℝ)
    (stop : (k : ℕ) → (Finset.Iic k → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) → Prop)
    (hstop : ∀ k,MeasurableSet {h | stop k h}) (k : ℕ) :
    Measurable (fun p : (Finset.Iic k → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) ×
      JumpState (Molecule n → ℕ) (PhysicalCountChannel n) =>
        nonfoodHistoryMultiplier c V basal cat θ stop k p.1 p.2) := by
  apply stoppedStateMultiplier_measurable
    (fun N ch => Real.exp (θ*nonfoodConcentrationJump V N ch))
    (nonfoodTiltCompensator c V basal cat θ)
    (fun j h => stop j h ∨ ¬(countMass (h ⟨j,Finset.mem_Iic.mpr le_rfl⟩).1 : ℝ) ≤ 11*V)
  intro j
  have hN : Measurable (fun h : Finset.Iic j → JumpState (Molecule n → ℕ) (PhysicalCountChannel n) =>
      (h ⟨j,Finset.mem_Iic.mpr le_rfl⟩).1) := (measurable_pi_apply _).fst
  exact (hstop j).union ((measurableSet_le
    ((measurable_of_countable (fun N : Molecule n → ℕ => (countMass N : ℝ))).comp hN)
    measurable_const).compl)
/-- Actual trajectory-law product inequality, with arbitrary measurable stopping
and automatic deactivation outside the mass corridor. -/
theorem physical_nonfood_stopped_product (hn : 4 ≤ n)
    (c : SourceMoleculeFibreConfig n) (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ)
    (hbasal : ∀ r, (basal r : ℝ) ≤ 1) (hcat : ∀ r z, (cat r z : ℝ) ≤ 16)
    (θ : ℝ) (hθ : |θ| *((n : ℝ)/V) ≤ 1)
    (stop : (k : ℕ) → (Finset.Iic k → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) → Prop)
    (hstop : ∀ k,MeasurableSet {h | stop k h}) (K : ℕ) :
    (∫⁻ z,trajectoryProduct (nonfoodHistoryMultiplier c V basal cat θ stop) K z
      ∂physicalTrajectoryLaw (by omega : 2 ≤ n) c V 1 hV (by norm_num) basal cat N) ≤ 1 := by
  have hh := predictable_product_integral_le
    (physicalTrajectoryLaw (by omega : 2 ≤ n) c V 1 hV (by norm_num) basal cat N)
    (jumpHistoryKernel unboundedPhysicalNext (unboundedPhysicalRate c V 1 basal cat)
      (unboundedPhysicalRate_nonneg c V 1 basal cat)
      (unbounded_total_pos (by omega : 2 ≤ n) c V 1 hV (by norm_num) basal cat))
    (fun k => physicalTrajectoryLaw_transition (by omega : 2 ≤ n) c V 1 hV (by norm_num) basal cat N k)
    (nonfoodHistoryMultiplier c V basal cat θ stop)
    (nonfoodHistoryMultiplier_measurable c V basal cat θ stop hstop) 1
  have hmean : ∀ k h, (∫⁻ y, nonfoodHistoryMultiplier c V basal cat θ stop k h y
      ∂jumpHistoryKernel unboundedPhysicalNext (unboundedPhysicalRate c V 1 basal cat)
        (unboundedPhysicalRate_nonneg c V 1 basal cat)
        (unbounded_total_pos (by omega : 2 ≤ n) c V 1 hV (by norm_num) basal cat) k h) ≤ 1 := by
    intro k h
    by_cases hs : stop k h ∨ ¬(countMass (h ⟨k,Finset.mem_Iic.mpr le_rfl⟩).1 : ℝ) ≤ 11*V
    · simp only [nonfoodHistoryMultiplier,stoppedStateMultiplier,if_pos hs]
      simp
    · simp only [nonfoodHistoryMultiplier,stoppedStateMultiplier,if_neg hs]
      exact physical_nonfood_tilt_mean hn c V hV basal cat _
        (not_not.mp (not_or.mp hs).2) hbasal hcat θ hθ
  simpa only [one_pow] using hh hmean K

theorem physical_nonfood_stopped_product_tail (hn : 4 ≤ n)
    (c : SourceMoleculeFibreConfig n) (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ)
    (hbasal : ∀ r, (basal r : ℝ) ≤ 1) (hcat : ∀ r z, (cat r z : ℝ) ≤ 16)
    (θ : ℝ) (hθ : |θ| *((n : ℝ)/V) ≤ 1)
    (stop : (k : ℕ) → (Finset.Iic k → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) → Prop)
    (hstop : ∀ k,MeasurableSet {h | stop k h}) (K : ℕ) (L : ℝ) :
    physicalTrajectoryLaw (by omega : 2 ≤ n) c V 1 hV (by norm_num) basal cat N
      {z | ENNReal.ofReal (Real.exp L) ≤
        trajectoryProduct (nonfoodHistoryMultiplier c V basal cat θ stop) K z} ≤
      ENNReal.ofReal (Real.exp (-L)) := by
  let μ := physicalTrajectoryLaw (by omega : 2 ≤ n) c V 1 hV (by norm_num) basal cat N
  let m := nonfoodHistoryMultiplier c V basal cat θ stop
  have hm := nonfoodHistoryMultiplier_measurable c V basal cat θ stop hstop
  have hp : Measurable (trajectoryProduct m K) :=
    (prefixProduct_measurable m hm K).comp (Preorder.measurable_frestrictLe
      (X := fun _ : ℕ => JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) K)
  have ht := (mul_meas_ge_le_lintegral (μ := μ) hp (ENNReal.ofReal (Real.exp L))).trans
    (physical_nonfood_stopped_product hn c V hV basal cat N hbasal hcat θ hθ stop hstop K)
  have he : ENNReal.ofReal (Real.exp (-L))*ENNReal.ofReal (Real.exp L) = 1 := by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,← Real.exp_add,neg_add_cancel,
      Real.exp_zero,ENNReal.ofReal_one]
  calc
    _ = ENNReal.ofReal (Real.exp (-L)) * (ENNReal.ofReal (Real.exp L)*
        μ {z | ENNReal.ofReal (Real.exp L) ≤ trajectoryProduct m K z}) := by
      rw [← mul_assoc,he,one_mul]
    _ ≤ ENNReal.ofReal (Real.exp (-L))*1 := mul_le_mul_right ht _
    _ = _ := mul_one _

end
end RandomViability
