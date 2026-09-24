import proofs.RandomViability.PredictableProductBounds
import proofs.RandomViability.JumpStateLaplace
import proofs.RandomViability.FoodCrossingAlgebra
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Analysis.SpecificLimits.Basic

namespace CompositionalMemory
open RandomViability MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

noncomputable def regionKilledMultiplier {α β : Type*} (S : α → Prop) (k : ℕ)
    (h : Finset.Iic k → JumpState α β) (y : JumpState α β) : ℝ≥0∞ := by
  classical
  exact if S (h ⟨k,Finset.mem_Iic.mpr le_rfl⟩).1 then jumpMultiplier (fun _ => 1) 1 y else 0

theorem unit_multiplier_wait {α β : Type*} (y : JumpState α β) :
    jumpMultiplier (fun _ => 1) 1 y = ENNReal.ofReal (Real.exp (-y.2.2)) := by
  have hw : y.2.1.elim (fun _ => (1 : ℝ)) (fun _ => 1)=1 := by cases y.2.1 <;> rfl
  unfold jumpMultiplier
  rw [hw]
  simp

theorem region_killed_product_eq {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (S : α → Prop) (K : ℕ) (z : ℕ → JumpState α β) (hs : ∀ i < K,S (z i).1) :
    trajectoryProduct (regionKilledMultiplier S) K z =
      ENNReal.ofReal (Real.exp (-waitingSum (fun i => (z (i+1)).2.2) K)) := by
  classical
  have he : trajectoryProduct (regionKilledMultiplier S) K z =
      ∏ i : Fin K, ENNReal.ofReal (Real.exp (-(z ((i : ℕ)+1)).2.2)) := by
    unfold trajectoryProduct
    apply Finset.prod_congr rfl
    intro i _
    have hi : S ((Preorder.frestrictLe (i : ℕ) z) ⟨(i : ℕ),Finset.mem_Iic.mpr le_rfl⟩).1 := hs i i.isLt
    dsimp only [regionKilledMultiplier]
    rw [if_pos hi,unit_multiplier_wait]
  rw [he,Fin.prod_univ_eq_prod_range (fun i => ENNReal.ofReal (Real.exp (-(z (i+1)).2.2))) K]
  have hf := food_product_formula (fun _ => 0) (fun i => (z (i+1)).2.2) 1 K
  simpa only [incomingSum,Finset.sum_const_zero,pow_zero,one_mul,neg_one_mul] using hf

variable {α β : Type*}
  [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
  [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]

theorem regionKilledMultiplier_measurable (S : α → Prop) (k : ℕ) :
    Measurable (fun p : (Finset.Iic k → JumpState α β) × JumpState α β => regionKilledMultiplier S k p.1 p.2) := by
  classical
  have hs : MeasurableSet {x : α | S x} := (Set.to_countable _).measurableSet
  exact Measurable.ite (hs.preimage (((measurable_pi_apply
    (⟨k,Finset.mem_Iic.mpr le_rfl⟩ : Finset.Iic k)).comp measurable_fst).fst))
    ((jumpMultiplier_measurable _ _).comp measurable_snd) measurable_const

theorem region_killed_product_bound (initial : α) (next : α → β → α) (rate : α → β → ℝ)
    (hr : ∀ x b, 0 ≤ rate x b) (ht : ∀ x, 0 < ∑ b, rate x b)
    (S : α → Prop) (q : ℝ) (hbound : ∀ x,S x → (∑ b,rate x b) ≤ q) (K : ℕ) :
    (∫⁻ z,trajectoryProduct (regionKilledMultiplier S) K z ∂jumpTrajectoryLaw initial next rate hr ht) ≤
      (ENNReal.ofReal (q/(q+1)))^K := by
  classical
  apply predictable_product_integral_le (jumpTrajectoryLaw initial next rate hr ht)
    (jumpHistoryKernel next rate hr ht)
    (fun _ => Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure)
    (regionKilledMultiplier S) (regionKilledMultiplier_measurable S)
  intro k h
  by_cases hs : S (h ⟨k,Finset.mem_Iic.mpr le_rfl⟩).1
  · simp only [regionKilledMultiplier,if_pos hs]
    exact (jumpState_wait_contraction next rate hr ht (h ⟨k,Finset.mem_Iic.mpr le_rfl⟩).1 q (hbound _ hs)).1
  · simp only [regionKilledMultiplier,if_neg hs,lintegral_zero]
    exact bot_le

/-- Infinite jumps in a bounded-rate region cannot fit in finite time. -/
theorem bounded_region_before_time_null (initial : α) (next : α → β → α) (rate : α → β → ℝ)
    (hr : ∀ x b, 0 ≤ rate x b) (ht : ∀ x, 0 < ∑ b, rate x b)
    (S : α → Prop) (q : ℝ) (hq : 0 < q) (hbound : ∀ x,S x → (∑ b,rate x b) ≤ q) (T : ℝ) :
    jumpTrajectoryLaw initial next rate hr ht {z |
      (∀ K,waitingSum (fun i => (z (i+1)).2.2) K ≤ T) ∧ ∀ K,S (z K).1} = 0 := by
  let μ := jumpTrajectoryLaw initial next rate hr ht
  let A := {z : ℕ → JumpState α β | (∀ K,waitingSum (fun i => (z (i+1)).2.2) K ≤ T) ∧ ∀ K,S (z K).1}
  let a := ENNReal.ofReal (Real.exp (-T))
  let ρ := ENNReal.ofReal (q/(q+1))
  have hρ : ρ < 1 := by
    dsimp [ρ]
    rw [ENNReal.ofReal_lt_one]
    exact (div_lt_one (by linarith)).mpr (by linarith)
  have hb : ∀ K,a*μ A ≤ ρ^K := by
    intro K
    have hp : Measurable (trajectoryProduct (regionKilledMultiplier S) K) :=
      (prefixProduct_measurable (regionKilledMultiplier S) (regionKilledMultiplier_measurable S) K).comp
        (Preorder.measurable_frestrictLe (X := fun _ : ℕ => JumpState α β) K)
    have hsub : A ⊆ {z | a ≤ trajectoryProduct (regionKilledMultiplier S) K z} := by
      intro z hz
      change a <= trajectoryProduct (regionKilledMultiplier S) K z
      rw [region_killed_product_eq S K z (fun i _ => hz.2 i)]
      exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (neg_le_neg (hz.1 K)))
    exact (mul_le_mul_right (measure_mono hsub) a).trans
      ((mul_meas_ge_le_lintegral hp a).trans (region_killed_product_bound initial next rate hr ht S q hbound K))
  have hz : a*μ A=0 := by
    apply le_antisymm ?_ (by positivity)
    exact ge_of_tendsto (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hρ) (Eventually.of_forall hb)
  have ha : a ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _))
  exact (mul_eq_zero.mp hz).resolve_left ha

end CompositionalMemory
