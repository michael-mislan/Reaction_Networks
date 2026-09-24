import proofs.RandomViability.PredictableProductBounds
import proofs.RandomViability.PhysicalMassTrajectory
import proofs.RandomViability.JumpStateLaplace
import proofs.RandomViability.FoodCrossingAlgebra

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 30000

def massRegion {n : ℕ} (B : ℕ) (N : Molecule n → ℕ) : Prop := countMass N ≤ B

def massKilledMultiplier {n : ℕ} (B k : ℕ)
    (h : Finset.Iic k → JumpState (Molecule n → ℕ) (PhysicalCountChannel n))
    (y : JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) : ℝ≥0∞ :=
  if massRegion B (h ⟨k, Finset.mem_Iic.mpr le_rfl⟩).1 then jumpMultiplier (fun _ => 1) 1 y else 0

theorem unit_jumpMultiplier_eq {α β : Type*} (y : JumpState α β) :
    jumpMultiplier (fun _ => 1) 1 y = ENNReal.ofReal (Real.exp (-y.2.2)) := by
  have hw : y.2.1.elim (fun _ => (1 : ℝ)) (fun _ => 1) = 1 := by cases y.2.1 <;> rfl
  unfold jumpMultiplier
  rw [hw]
  simp

theorem massKilledProduct_eq {n : ℕ} (B K : ℕ)
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n))
    (hs : ∀ i < K, massRegion B (z i).1) :
    trajectoryProduct (massKilledMultiplier B) K z =
      ENNReal.ofReal (Real.exp (-waitingSum (fun i => (z (i+1)).2.2) K)) := by
  have he : trajectoryProduct (massKilledMultiplier B) K z =
      ∏ i : Fin K, ENNReal.ofReal (Real.exp (-(z ((i : ℕ)+1)).2.2)) := by
    unfold trajectoryProduct
    apply Finset.prod_congr rfl
    intro i _
    have hi : massRegion B ((Preorder.frestrictLe (i : ℕ) z)
      ⟨(i : ℕ), Finset.mem_Iic.mpr le_rfl⟩).1 := hs i i.isLt
    dsimp only [massKilledMultiplier]
    rw [if_pos hi, unit_jumpMultiplier_eq]
  rw [he, Fin.prod_univ_eq_prod_range (fun i => ENNReal.ofReal (Real.exp (-(z (i+1)).2.2))) K]
  have hf := food_product_formula (fun _ => 0) (fun i => (z (i+1)).2.2) 1 K
  simpa only [incomingSum, Finset.sum_const_zero, pow_zero, one_mul, neg_one_mul] using hf

theorem massKilledProduct_lower {n : ℕ} (B K : ℕ) (T : ℝ)
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n))
    (hs : ∀ i < K, massRegion B (z i).1) (ht : waitingSum (fun i => (z (i+1)).2.2) K ≤ T) :
    ENNReal.ofReal (Real.exp (-T)) ≤ trajectoryProduct (massKilledMultiplier B) K z := by
  rw [massKilledProduct_eq B K z hs]
  exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (neg_le_neg ht))

variable {n : ℕ} [MeasurableSpace (PhysicalCountChannel n)]
  [MeasurableSingletonClass (PhysicalCountChannel n)]

theorem massKilledMultiplier_measurable (B k : ℕ) :
    Measurable (fun p : (Finset.Iic k → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) ×
      JumpState (Molecule n → ℕ) (PhysicalCountChannel n) => massKilledMultiplier B k p.1 p.2) := by
  have hs : MeasurableSet {N : Molecule n → ℕ | massRegion B N} :=
    measurableSet_le (measurable_of_countable countMass) measurable_const
  exact Measurable.ite (hs.preimage (((measurable_pi_apply
    (⟨k, Finset.mem_Iic.mpr le_rfl⟩ : Finset.Iic k)).comp measurable_fst).fst))
    ((jumpMultiplier_measurable _ _).comp measurable_snd) measurable_const

theorem physical_killed_product_bound (hn : 2 ≤ n)
    (c : SourceMoleculeFibreConfig n) (V D : NNReal)
    (hV : 0 < (V : ℝ)) (hD : 0 < (D : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ) (B : ℕ) :
    ∃ q : NNReal, 1 ≤ (q : ℝ) ∧ ∀ K,
      (∫⁻ z, trajectoryProduct (massKilledMultiplier B) K z ∂physicalTrajectoryLaw hn c V D hV hD basal cat N) ≤
        (ENNReal.ofReal ((q : ℝ)/(q+1)))^K := by
  obtain ⟨q, hq, hb⟩ := unbounded_rate_locally_bounded c V D basal cat B
  refine ⟨q, hq, ?_⟩
  intro K
  apply predictable_product_integral_le (physicalTrajectoryLaw hn c V D hV hD basal cat N)
    (jumpHistoryKernel unboundedPhysicalNext (unboundedPhysicalRate c V D basal cat)
      (unboundedPhysicalRate_nonneg c V D basal cat) (unbounded_total_pos hn c V D hV hD basal cat))
    (fun k => physicalTrajectoryLaw_transition hn c V D hV hD basal cat N k)
    (massKilledMultiplier B) (massKilledMultiplier_measurable B)
  intro k h
  by_cases hs : massRegion B (h ⟨k, Finset.mem_Iic.mpr le_rfl⟩).1
  · simp only [massKilledMultiplier, if_pos hs]
    exact (jumpState_wait_contraction unboundedPhysicalNext (unboundedPhysicalRate c V D basal cat)
      (unboundedPhysicalRate_nonneg c V D basal cat) (unbounded_total_pos hn c V D hV hD basal cat)
      (h ⟨k, Finset.mem_Iic.mpr le_rfl⟩).1 q (hb _ hs)).1
  · simp only [massKilledMultiplier, if_neg hs, lintegral_zero]
    exact bot_le

end
end RandomViability
