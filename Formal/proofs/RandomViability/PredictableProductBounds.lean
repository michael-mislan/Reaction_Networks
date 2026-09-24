import proofs.RandomViability.PredictableProducts

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 30000

theorem predictable_product_integral_le {X : Type*} [MeasurableSpace X]
    (μ : Measure (ℕ → X)) [hμ : IsProbabilityMeasure μ]
    (κ : (k : ℕ) → Kernel (Finset.Iic k → X) X) [hκ : ∀ k, IsMarkovKernel (κ k)]
    (htransition : ∀ k, μ.map (Preorder.frestrictLe k) ⊗ₘ κ k =
      μ.map (fun z => (Preorder.frestrictLe k z, z (k+1))))
    (m : (k : ℕ) → (Finset.Iic k → X) → X → ℝ≥0∞)
    (hm : ∀ k, Measurable (fun p : (Finset.Iic k → X) × X => m k p.1 p.2))
    (ρ : ℝ≥0∞) (hmean : ∀ k h, ∫⁻ y, m k h y ∂κ k h ≤ ρ) (k : ℕ) :
    ∫⁻ z, trajectoryProduct m k z ∂μ ≤ ρ^k := by
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
    rw [← he]
    calc
      _ ≤ ∫⁻ h, prefixProduct m k h * ρ ∂μ.map (Preorder.frestrictLe k) := by
        apply lintegral_mono
        intro h
        have hmk : Measurable (m k h) := (hm k).comp (measurable_const.prodMk measurable_id)
        dsimp only
        rw [lintegral_const_mul _ hmk]
        exact mul_le_mul_right (hmean k h) (prefixProduct m k h)
      _ = (∫⁻ h, prefixProduct m k h ∂μ.map (Preorder.frestrictLe k))*ρ := lintegral_mul_const ρ hg
      _ ≤ ρ^k*ρ := by
        rw [lintegral_map hg (by fun_prop)]
        change (∫⁻ z, trajectoryProduct m k z ∂μ)*ρ ≤ _
        exact mul_le_mul_left ih ρ
      _ = ρ^(k+1) := (pow_succ ρ k).symm

end
end RandomViability
