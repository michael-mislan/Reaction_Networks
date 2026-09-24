import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Tactic

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 30000

variable {X : Type*} [MeasurableSpace X]

def trajectoryProduct (m : (k : ℕ) → (Finset.Iic k → X) → X → ℝ≥0∞)
    (k : ℕ) (z : ℕ → X) : ℝ≥0∞ :=
  ∏ i : Fin k, m i (Preorder.frestrictLe (i : ℕ) z) (z ((i : ℕ)+1))

def prefixProduct (m : (k : ℕ) → (Finset.Iic k → X) → X → ℝ≥0∞)
    (k : ℕ) (h : Finset.Iic k → X) : ℝ≥0∞ :=
  ∏ i : Fin k, m i (Preorder.frestrictLe₂ (π := fun _ : ℕ => X) (Nat.le_of_lt i.isLt) h)
    (h ⟨(i : ℕ)+1, Finset.mem_Iic.mpr i.isLt⟩)

omit [MeasurableSpace X] in
theorem prefixProduct_restrict (m : (k : ℕ) → (Finset.Iic k → X) → X → ℝ≥0∞)
    (k : ℕ) (z : ℕ → X) : prefixProduct m k (Preorder.frestrictLe k z) = trajectoryProduct m k z := rfl

theorem prefixProduct_measurable (m : (k : ℕ) → (Finset.Iic k → X) → X → ℝ≥0∞)
    (hm : ∀ k, Measurable (fun p : (Finset.Iic k → X) × X => m k p.1 p.2)) (k : ℕ) :
    Measurable (prefixProduct m k) := by
  unfold prefixProduct
  apply Finset.measurable_prod
  intro i _
  exact (hm i).comp ((Preorder.measurable_frestrictLe₂ (X := fun _ : ℕ => X) (Nat.le_of_lt i.isLt)).prodMk
    (measurable_pi_apply (⟨(i : ℕ)+1, Finset.mem_Iic.mpr i.isLt⟩ : Finset.Iic k)))

omit [MeasurableSpace X] in
theorem trajectoryProduct_succ (m : (k : ℕ) → (Finset.Iic k → X) → X → ℝ≥0∞)
    (k : ℕ) (z : ℕ → X) :
    trajectoryProduct m (k+1) z = trajectoryProduct m k z * m k (Preorder.frestrictLe k z) (z (k+1)) := by
  unfold trajectoryProduct
  rw [Fin.prod_univ_castSucc]
  rfl

theorem predictable_product_integral (μ : Measure (ℕ → X)) [hμ : IsProbabilityMeasure μ]
    (κ : (k : ℕ) → Kernel (Finset.Iic k → X) X) [hκ : ∀ k, IsMarkovKernel (κ k)]
    (htransition : ∀ k, μ.map (Preorder.frestrictLe k) ⊗ₘ κ k =
      μ.map (fun z => (Preorder.frestrictLe k z, z (k+1))))
    (m : (k : ℕ) → (Finset.Iic k → X) → X → ℝ≥0∞)
    (hm : ∀ k, Measurable (fun p : (Finset.Iic k → X) × X => m k p.1 p.2))
    (hmean : ∀ k h, ∫⁻ y, m k h y ∂κ k h = 1) (k : ℕ) :
    ∫⁻ z, trajectoryProduct m k z ∂μ = 1 := by
  induction k with
  | zero => simp [trajectoryProduct]
  | succ k ih =>
    have hg := prefixProduct_measurable m hm k
    have hmeas : Measurable (fun p : (Finset.Iic k → X) × X => prefixProduct m k p.1 * m k p.1 p.2) :=
      (hg.comp measurable_fst).mul (hm k)
    have he : (∫⁻ p, prefixProduct m k p.1 * m k p.1 p.2 ∂(μ.map (Preorder.frestrictLe k) ⊗ₘ κ k)) =
        ∫⁻ z, trajectoryProduct m (k+1) z ∂μ := by
      rw [htransition k, lintegral_map hmeas (by fun_prop)]
      apply lintegral_congr
      intro z
      rw [prefixProduct_restrict, trajectoryProduct_succ]
    rw [Measure.lintegral_compProd hmeas] at he
    have hi : ∀ h : Finset.Iic k → X,
        (∫⁻ y, prefixProduct m k h * m k h y ∂κ k h) = prefixProduct m k h := by
      intro h
      have hmk : Measurable (m k h) := (hm k).comp (measurable_const.prodMk measurable_id)
      rw [lintegral_const_mul _ hmk, hmean, mul_one]
    simp_rw [hi] at he
    rw [lintegral_map hg (by fun_prop)] at he
    simpa only [prefixProduct_restrict, ih] using he.symm

end
end RandomViability
