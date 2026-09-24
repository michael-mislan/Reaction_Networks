import proofs.RandomViability.PredictableProducts
import proofs.RandomViability.PhysicalKernelLaplace
import proofs.RandomViability.PhysicalTrajectory
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 30000

variable {n : ℕ} [MeasurableSpace (PhysicalCountChannel n)]
  [MeasurableSingletonClass (PhysicalCountChannel n)]

theorem stopped_physical_product_integral (hn : 2 ≤ n)
    (c : SourceMoleculeFibreConfig n) (V D : NNReal)
    (hV : 0 < (V : ℝ)) (hD : 0 < (D : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ)
    (stop : (k : ℕ) → (Finset.Iic k → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) → Prop)
    (hstop : ∀ k, MeasurableSet {h | stop k h}) (K : ℕ) :
    ∫⁻ z, trajectoryProduct
      (fun k h y => if stop k h then 1 else
        jumpMultiplier (fun ch => (2 : ℝ)^foodInputMass ch) (14*(D : ℝ)*V) y) K z
      ∂physicalTrajectoryLaw hn c V D hV hD basal cat N = 1 := by
  apply predictable_product_integral (physicalTrajectoryLaw hn c V D hV hD basal cat N)
    (jumpHistoryKernel unboundedPhysicalNext (unboundedPhysicalRate c V D basal cat)
      (unboundedPhysicalRate_nonneg c V D basal cat) (unbounded_total_pos hn c V D hV hD basal cat))
    (fun k => physicalTrajectoryLaw_transition hn c V D hV hD basal cat N k)
  · intro k
    exact Measurable.ite ((hstop k).preimage measurable_fst) measurable_const
      ((jumpMultiplier_measurable _ _).comp measurable_snd)
  · intro k h
    by_cases hs : stop k h
    · simp only [if_pos hs]
      simp
    · simp only [if_neg hs]
      exact physical_food_multiplier_integral hn c V D hV hD basal cat
        (h ⟨k, Finset.mem_Iic.mpr le_rfl⟩).1

theorem stopped_physical_product_tail (hn : 2 ≤ n)
    (c : SourceMoleculeFibreConfig n) (V D : NNReal)
    (hV : 0 < (V : ℝ)) (hD : 0 < (D : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ)
    (stop : (k : ℕ) → (Finset.Iic k → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) → Prop)
    (hstop : ∀ k, MeasurableSet {h | stop k h}) (K : ℕ) (ε : ℝ≥0∞) :
    ε * physicalTrajectoryLaw hn c V D hV hD basal cat N
      {z | ε ≤ trajectoryProduct (fun k h y => if stop k h then 1 else
        jumpMultiplier (fun ch => (2 : ℝ)^foodInputMass ch) (14*(D : ℝ)*V) y) K z} ≤ 1 := by
  let m := fun k h (y : JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) => if stop k h then (1 : ℝ≥0∞) else
    jumpMultiplier (fun ch => (2 : ℝ)^foodInputMass ch) (14*(D : ℝ)*V) y
  have hm : ∀ k, Measurable (fun p :
      (Finset.Iic k → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) ×
        JumpState (Molecule n → ℕ) (PhysicalCountChannel n) => m k p.1 p.2) := by
    intro k
    exact Measurable.ite ((hstop k).preimage measurable_fst) measurable_const
      ((jumpMultiplier_measurable _ _).comp measurable_snd)
  have hp : Measurable (trajectoryProduct m K) :=
    (prefixProduct_measurable m hm K).comp (Preorder.measurable_frestrictLe
      (X := fun _ : ℕ => JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) K)
  have h := mul_meas_ge_le_lintegral (μ := physicalTrajectoryLaw hn c V D hV hD basal cat N) hp ε
  have he : (∫⁻ z, trajectoryProduct m K z ∂physicalTrajectoryLaw hn c V D hV hD basal cat N) = 1 :=
    stopped_physical_product_integral hn c V D hV hD basal cat N stop hstop K
  rw [he] at h
  exact h

end
end RandomViability
