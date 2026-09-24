import proofs.RandomViability.CensoredStateProducts
import proofs.RandomViability.PredictableProductCrossing

namespace RAF1519.Refinement
noncomputable section
open Classical MeasureTheory ProbabilityTheory RandomViability
open scoped BigOperators ENNReal

variable {α β : Type*}

def coordinateStop (good : Set α) (T : ℝ)
    (stop : (k : ℕ) → (Finset.Iic k → JumpState α β) → Prop)
    (k : ℕ) (h : Finset.Iic k → JumpState α β) : Prop :=
  stop k h ∨ (h ⟨k,Finset.mem_Iic.mpr le_rfl⟩).1 ∉ good ∨ T ≤ prefixElapsed k h

def coordinateWait (good : Set α) (T : ℝ)
    (stop : (k : ℕ) → (Finset.Iic k → JumpState α β) → Prop)
    (k : ℕ) (h : Finset.Iic k → JumpState α β) (y : JumpState α β) : ℝ :=
  if coordinateStop good T stop k h then 0 else min y.2.2 (T-prefixElapsed k h)

variable [Fintype β]

def coordinateCompensation (rate inc : α → β → ℝ) (good : Set α) (T : ℝ)
    (stop : (k : ℕ) → (Finset.Iic k → JumpState α β) → Prop)
    (k : ℕ) (h : Finset.Iic k → JumpState α β) (y : JumpState α β) : ℝ :=
  let x := (h ⟨k,Finset.mem_Iic.mpr le_rfl⟩).1
  if coordinateStop good T stop k h then 0 else
    (if y.2.2 ≤ T-prefixElapsed k h then y.2.1.elim (fun _ => 0) (inc x) else 0)-
      (∑ a,rate x a*inc x a)*min y.2.2 (T-prefixElapsed k h)

def coordinateMultiplier (rate inc : α → β → ℝ) (good : Set α) (θ v T : ℝ)
    (stop : (k : ℕ) → (Finset.Iic k → JumpState α β) → Prop) :=
  censoredStoppedMultiplier (fun x a => Real.exp (θ*inc x a))
    (fun x => θ*(∑ a,rate x a*inc x a)+θ^2*v)
    (fun k h => T-prefixElapsed k h) (coordinateStop good T stop)

variable [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
  [MeasurableSpace β] [MeasurableSingletonClass β]

omit [Fintype β] [MeasurableSingletonClass β] in
theorem coordinateStop_measurable (good : Set α) (T : ℝ)
    (stop : (k : ℕ) → (Finset.Iic k → JumpState α β) → Prop)
    (hstop : ∀ k,MeasurableSet {h | stop k h}) (k : ℕ) :
    MeasurableSet {h | coordinateStop good T stop k h} := by
  have hx : Measurable (fun h : Finset.Iic k → JumpState α β =>
      (h ⟨k,Finset.mem_Iic.mpr le_rfl⟩).1) := (measurable_pi_apply _).fst
  have hg : MeasurableSet good := (Set.to_countable good).measurableSet
  exact (hstop k).union ((hg.preimage hx).compl.union
    (measurableSet_le measurable_const (prefixElapsed_measurable k)))

theorem coordinateMultiplier_measurable (rate inc : α → β → ℝ) (good : Set α) (θ v T : ℝ)
    (stop : (k : ℕ) → (Finset.Iic k → JumpState α β) → Prop)
    (hstop : ∀ k,MeasurableSet {h | stop k h}) (k : ℕ) :
    Measurable (fun p : (Finset.Iic k → JumpState α β) × JumpState α β =>
      coordinateMultiplier rate inc good θ v T stop k p.1 p.2) :=
  censoredStoppedMultiplier_measurable _ _ _
    (fun j => measurable_const.sub (prefixElapsed_measurable j)) _
    (coordinateStop_measurable good T stop hstop) k

theorem coordinate_multiplier_mean (next : α → β → α) (rate inc : α → β → ℝ)
    (hr : ∀ x a,0 ≤ rate x a) (ht : ∀ x,0 < ∑ a,rate x a)
    (good : Set α) (θ v T : ℝ)
    (hsmall : ∀ x ∈ good, ∀ a, |θ*inc x a| ≤ 1)
    (hvar : ∀ x ∈ good, (∑ a,rate x a*(inc x a)^2) ≤ v)
    (stop : (k : ℕ) → (Finset.Iic k → JumpState α β) → Prop)
    (k : ℕ) (h : Finset.Iic k → JumpState α β) :
    (∫⁻ y,coordinateMultiplier rate inc good θ v T stop k h y
      ∂jumpHistoryKernel next rate hr ht k h) ≤ 1 := by
  by_cases hs : coordinateStop good T stop k h
  · simp only [coordinateMultiplier,censoredStoppedMultiplier,if_pos hs]
    simp
  · have hg := not_not.mp (not_or.mp (not_or.mp hs).2).1
    have hrem : 0 ≤ T-prefixElapsed k h := sub_nonneg.mpr
      (le_of_not_ge (not_or.mp (not_or.mp hs).2).2)
    simp only [coordinateMultiplier,censoredStoppedMultiplier,if_neg hs]
    apply jumpState_censored_tilt_le_one next rate hr ht _ _ θ _ _ hrem
    exact (rate_exponential_tilt_bound _ _ (hr _) θ (hsmall _ hg)).trans
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left (hvar _ hg) (sq_nonneg θ)))

omit [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
  [MeasurableSpace β] [MeasurableSingletonClass β] in
theorem coordinate_multiplier_exp (rate inc : α → β → ℝ) (good : Set α) (θ v T : ℝ)
    (stop : (k : ℕ) → (Finset.Iic k → JumpState α β) → Prop)
    (k : ℕ) (h : Finset.Iic k → JumpState α β) (y : JumpState α β) :
    coordinateMultiplier rate inc good θ v T stop k h y =
      ENNReal.ofReal (Real.exp (θ*coordinateCompensation rate inc good T stop k h y-
        θ^2*v*coordinateWait good T stop k h y)) := by
  unfold coordinateMultiplier censoredStoppedMultiplier coordinateCompensation coordinateWait
  dsimp only
  by_cases hs : coordinateStop good T stop k h
  · simp only [if_pos hs,mul_zero,sub_zero,Real.exp_zero,ENNReal.ofReal_one]
  · simp only [if_neg hs,censoredJumpMultiplier]
    by_cases ht : y.2.2 ≤ T-prefixElapsed k h
    · simp only [if_pos ht,min_eq_left ht]
      unfold jumpMultiplier
      have he : y.2.1.elim (fun _ => (1:ℝ))
          (fun a => Real.exp (θ*inc (h ⟨k,Finset.mem_Iic.mpr le_rfl⟩).1 a)) =
          Real.exp (θ*y.2.1.elim (fun _ => 0) (inc (h ⟨k,Finset.mem_Iic.mpr le_rfl⟩).1)) := by
        cases y.2.1 <;> simp
      rw [he,← ENNReal.ofReal_mul (Real.exp_pos _).le,← Real.exp_add]
      congr 2
      ring
    · simp only [if_neg ht,min_eq_right (le_of_not_ge ht)]
      congr 2
      ring

omit [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
  [MeasurableSpace β] [MeasurableSingletonClass β] in
theorem coordinate_product_exp (rate inc : α → β → ℝ) (good : Set α) (θ v T : ℝ)
    (stop : (k : ℕ) → (Finset.Iic k → JumpState α β) → Prop)
    (K : ℕ) (z : ℕ → JumpState α β) :
    trajectoryProduct (coordinateMultiplier rate inc good θ v T stop) K z =
      ENNReal.ofReal (Real.exp
        (θ*(∑ i : Fin K,coordinateCompensation rate inc good T stop
          i (Preorder.frestrictLe (i:ℕ) z) (z ((i:ℕ)+1)))-
        θ^2*v*(∑ i : Fin K,coordinateWait good T stop
          i (Preorder.frestrictLe (i:ℕ) z) (z ((i:ℕ)+1))))) := by
  unfold trajectoryProduct
  simp_rw [coordinate_multiplier_exp]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun _ _ => (Real.exp_pos _).le),← Real.exp_sum,
    Finset.sum_sub_distrib,← Finset.mul_sum,← Finset.mul_sum]

end
end RAF1519.Refinement
