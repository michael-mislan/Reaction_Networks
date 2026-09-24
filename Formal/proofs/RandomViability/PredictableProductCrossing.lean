import proofs.RandomViability.PredictableProductBounds
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 80000

variable {X : Type*}

def productHit (a : ℝ≥0∞) (m : (k : ℕ) → (Finset.Iic k → X) → X → ℝ≥0∞)
    (k : ℕ) (h : Finset.Iic k → X) : Prop :=
  ∃ j : Fin (k+1), a ≤ prefixProduct m j
    (Preorder.frestrictLe₂ (π := fun _ : ℕ => X) (by omega : (j : ℕ) ≤ k) h)

def firstHitMultiplier (a : ℝ≥0∞) (m : (k : ℕ) → (Finset.Iic k → X) → X → ℝ≥0∞)
    (k : ℕ) (h : Finset.Iic k → X) (y : X) : ℝ≥0∞ :=
  if productHit a m k h then 1 else m k h y

theorem productHit_restrict (a : ℝ≥0∞) (m : (k : ℕ) → (Finset.Iic k → X) → X → ℝ≥0∞)
    (k : ℕ) (z : ℕ → X) :
    productHit a m k (Preorder.frestrictLe k z) ↔ ∃ j, j ≤ k ∧ a ≤ trajectoryProduct m j z := by
  constructor
  · rintro ⟨j,hj⟩
    exact ⟨j,by omega,hj⟩
  · rintro ⟨j,hj,hh⟩
    exact ⟨⟨j,by omega⟩,hh⟩

theorem firstHit_before_eq (a : ℝ≥0∞) (m : (k : ℕ) → (Finset.Iic k → X) → X → ℝ≥0∞)
    (j : ℕ) (z : ℕ → X) (hbefore : ∀ i < j, ¬a ≤ trajectoryProduct m i z) :
    trajectoryProduct (firstHitMultiplier a m) j z = trajectoryProduct m j z := by
  unfold trajectoryProduct
  apply Finset.prod_congr rfl
  intro i _
  apply if_neg
  rw [productHit_restrict]
  rintro ⟨l,hl,hh⟩
  exact hbefore l (lt_of_le_of_lt hl i.isLt) hh

theorem firstHit_persists (a : ℝ≥0∞) (m : (k : ℕ) → (Finset.Iic k → X) → X → ℝ≥0∞)
    (j K : ℕ) (z : ℕ → X) (hjK : j ≤ K) (hj : a ≤ trajectoryProduct m j z) :
    trajectoryProduct (firstHitMultiplier a m) K z = trajectoryProduct (firstHitMultiplier a m) j z := by
  induction K, hjK using Nat.le_induction with
  | base => rfl
  | succ K hjK ih =>
    rw [trajectoryProduct_succ,ih]
    have hh : productHit a m K (Preorder.frestrictLe K z) :=
      (productHit_restrict a m K z).mpr ⟨j,hjK,hj⟩
    simp only [firstHitMultiplier,if_pos hh,mul_one]

theorem firstHit_crossing_lower (a : ℝ≥0∞) (m : (k : ℕ) → (Finset.Iic k → X) → X → ℝ≥0∞)
    (K : ℕ) (z : ℕ → X) (hh : ∃ j, j ≤ K ∧ a ≤ trajectoryProduct m j z) :
    a ≤ trajectoryProduct (firstHitMultiplier a m) K z := by
  have hex : ∃ j,a ≤ trajectoryProduct m j z := by obtain ⟨j,_,hj⟩ := hh; exact ⟨j,hj⟩
  let j := Nat.find hex
  have hj : a ≤ trajectoryProduct m j z := Nat.find_spec hex
  have hb : ∀ i < j, ¬a ≤ trajectoryProduct m i z := fun i hi => Nat.find_min hex hi
  have hjK : j ≤ K := by
    obtain ⟨l,hl,hh⟩ := hh
    exact (Nat.find_min' hex hh).trans hl
  rw [firstHit_persists a m j K z hjK hj,firstHit_before_eq a m j z hb]
  exact hj

variable [MeasurableSpace X]

theorem productHit_measurable (a : ℝ≥0∞) (m : (k : ℕ) → (Finset.Iic k → X) → X → ℝ≥0∞)
    (hm : ∀ k,Measurable (fun p : (Finset.Iic k → X) × X => m k p.1 p.2)) (k : ℕ) :
    MeasurableSet {h | productHit a m k h} := by
  simp only [productHit,Set.setOf_exists]
  apply MeasurableSet.iUnion
  intro j
  exact measurableSet_le measurable_const ((prefixProduct_measurable m hm j).comp
    (Preorder.measurable_frestrictLe₂ (X := fun _ : ℕ => X) (by omega : (j : ℕ) ≤ k)))

theorem firstHitMultiplier_measurable (a : ℝ≥0∞) (m : (k : ℕ) → (Finset.Iic k → X) → X → ℝ≥0∞)
    (hm : ∀ k,Measurable (fun p : (Finset.Iic k → X) × X => m k p.1 p.2)) (k : ℕ) :
    Measurable (fun p : (Finset.Iic k → X) × X => firstHitMultiplier a m k p.1 p.2) :=
  Measurable.ite ((productHit_measurable a m hm k).preimage measurable_fst) measurable_const (hm k)

theorem firstHitMultiplier_mean_le
    (κ : (k : ℕ) → Kernel (Finset.Iic k → X) X) [∀ k,IsMarkovKernel (κ k)]
    (m : (k : ℕ) → (Finset.Iic k → X) → X → ℝ≥0∞)
    (hmean : ∀ k h,(∫⁻ y,m k h y ∂κ k h) ≤ 1) (a : ℝ≥0∞) (k : ℕ) (h : Finset.Iic k → X) :
    (∫⁻ y,firstHitMultiplier a m k h y ∂κ k h) ≤ 1 := by
  by_cases hp : productHit a m k h
  · simp only [firstHitMultiplier,if_pos hp]
    simp
  · simpa only [firstHitMultiplier,if_neg hp] using hmean k h

theorem firstHit_product_integral_le (μ : Measure (ℕ → X)) [IsProbabilityMeasure μ]
    (κ : (k : ℕ) → Kernel (Finset.Iic k → X) X) [∀ k,IsMarkovKernel (κ k)]
    (htransition : ∀ k, μ.map (Preorder.frestrictLe k) ⊗ₘ κ k =
      μ.map (fun z => (Preorder.frestrictLe k z,z (k+1))))
    (m : (k : ℕ) → (Finset.Iic k → X) → X → ℝ≥0∞)
    (hm : ∀ k,Measurable (fun p : (Finset.Iic k → X) × X => m k p.1 p.2))
    (hmean : ∀ k h,(∫⁻ y,m k h y ∂κ k h) ≤ 1) (a : ℝ≥0∞) (K : ℕ) :
    (∫⁻ z,trajectoryProduct (firstHitMultiplier a m) K z ∂μ) ≤ 1 := by
  simpa only [one_pow] using predictable_product_integral_le μ κ htransition
    (firstHitMultiplier a m) (firstHitMultiplier_measurable a m hm) 1
    (firstHitMultiplier_mean_le κ m hmean a) K

theorem trajectory_product_threshold_bound (μ : Measure (ℕ → X))
    (m : (k : ℕ) → (Finset.Iic k → X) → X → ℝ≥0∞)
    (hm : ∀ k,Measurable (fun p : (Finset.Iic k → X) × X => m k p.1 p.2))
    (K : ℕ) (a : ℝ≥0∞) (hi : (∫⁻ z,trajectoryProduct m K z ∂μ) ≤ 1) :
    a*μ {z | a ≤ trajectoryProduct m K z} ≤ 1 := by
  have hp : Measurable (trajectoryProduct m K) :=
    (prefixProduct_measurable m hm K).comp
      (Preorder.measurable_frestrictLe (X := fun _ : ℕ => X) K)
  exact (mul_meas_ge_le_lintegral (μ := μ) hp a).trans hi

theorem predictable_product_crossing_bound (μ : Measure (ℕ → X)) [IsProbabilityMeasure μ]
    (κ : (k : ℕ) → Kernel (Finset.Iic k → X) X) [∀ k,IsMarkovKernel (κ k)]
    (htransition : ∀ k, μ.map (Preorder.frestrictLe k) ⊗ₘ κ k =
      μ.map (fun z => (Preorder.frestrictLe k z,z (k+1))))
    (m : (k : ℕ) → (Finset.Iic k → X) → X → ℝ≥0∞)
    (hm : ∀ k,Measurable (fun p : (Finset.Iic k → X) × X => m k p.1 p.2))
    (hmean : ∀ k h, (∫⁻ y,m k h y ∂κ k h) ≤ 1) (a : ℝ≥0∞) (K : ℕ) :
    a*μ {z | ∃ j,j ≤ K ∧ a ≤ trajectoryProduct m j z} ≤ 1 := by
  let ms := firstHitMultiplier a m
  have hms := firstHitMultiplier_measurable a m hm
  have hi : (∫⁻ z,trajectoryProduct ms K z ∂μ) ≤ 1 :=
    firstHit_product_integral_le μ κ htransition m hm hmean a K
  have ht := trajectory_product_threshold_bound μ ms hms K a hi
  have hsub : {z : ℕ → X | ∃ j,j ≤ K ∧ a ≤ trajectoryProduct m j z} ⊆
      {z | a ≤ trajectoryProduct ms K z} := by
    intro z hz
    exact firstHit_crossing_lower a m K z hz
  exact (mul_le_mul_right (measure_mono (μ := μ) hsub) a).trans ht

end
end RandomViability
