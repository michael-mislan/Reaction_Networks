import proofs.RandomViability.PredictableProducts

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 30000

variable {X : Type*} [mX : MeasurableSpace X]

def seededPrefixProduct (seed : X → ℝ≥0∞)
    (m : (k : ℕ) → (Finset.Iic k → X) → X → ℝ≥0∞)
    (k : ℕ) (h : Finset.Iic k → X) : ℝ≥0∞ :=
  seed (h ⟨0,Finset.mem_Iic.mpr (Nat.zero_le k)⟩)*prefixProduct m k h

def seededTrajectoryProduct (seed : X → ℝ≥0∞)
    (m : (k : ℕ) → (Finset.Iic k → X) → X → ℝ≥0∞)
    (k : ℕ) (z : ℕ → X) : ℝ≥0∞ := seed (z 0)*trajectoryProduct m k z

theorem seededPrefixProduct_measurable (seed : X → ℝ≥0∞) (hs : Measurable seed)
    (m : (k : ℕ) → (Finset.Iic k → X) → X → ℝ≥0∞)
    (hm : ∀ k, Measurable (fun p : (Finset.Iic k → X) × X => m k p.1 p.2)) (k : ℕ) :
    Measurable (seededPrefixProduct seed m k) :=
  (hs.comp (measurable_pi_apply _)).mul (prefixProduct_measurable m hm k)

/-- Successive conditional lower bounds multiply on the actual trajectory law.
The bound is required only for prefixes retained by the prescribed event; the
seed factor also enforces the initial population. No reset or independence is
assumed. Indicator factors specialize this to productive path cylinders. -/
theorem prescribed_prefix_product_lower (μ : Measure (ℕ → X)) [hμ : IsProbabilityMeasure μ]
    (κ : (k : ℕ) → Kernel (Finset.Iic k → X) X) [hκ : ∀ k, IsMarkovKernel (κ k)]
    (htransition : ∀ k, μ.map (Preorder.frestrictLe k) ⊗ₘ κ k =
      μ.map (fun z => (Preorder.frestrictLe k z, z (k+1))))
    (seed : X → ℝ≥0∞) (hs : Measurable seed)
    (hinit : (∫⁻ z, seed (z 0) ∂μ) = 1)
    (m : (k : ℕ) → (Finset.Iic k → X) → X → ℝ≥0∞)
    (hm : ∀ k, Measurable (fun p : (Finset.Iic k → X) × X => m k p.1 p.2))
    (g : ℕ → ℝ≥0∞)
    (hmean : ∀ k h, seededPrefixProduct seed m k h ≠ 0 → g k ≤ ∫⁻ y, m k h y ∂κ k h)
    (k : ℕ) :
    (∏ i : Fin k, g i) ≤ ∫⁻ z, seededTrajectoryProduct seed m k z ∂μ := by
  induction k with
  | zero => simp [seededTrajectoryProduct, trajectoryProduct, hinit]
  | succ k ih =>
    have hg := seededPrefixProduct_measurable seed hs m hm k
    have hmeas : Measurable (fun p : (Finset.Iic k → X) × X =>
        seededPrefixProduct seed m k p.1*m k p.1 p.2) :=
      (hg.comp measurable_fst).mul (hm k)
    have he : (∫⁻ p, seededPrefixProduct seed m k p.1*m k p.1 p.2
        ∂(μ.map (Preorder.frestrictLe k) ⊗ₘ κ k)) =
        ∫⁻ z, seededTrajectoryProduct seed m (k+1) z ∂μ := by
      rw [htransition k, lintegral_map hmeas (by fun_prop)]
      apply lintegral_congr
      intro z
      simp only [seededPrefixProduct, seededTrajectoryProduct,
        prefixProduct_restrict, trajectoryProduct_succ]
      exact mul_assoc _ _ _
    rw [Measure.lintegral_compProd hmeas] at he
    have hlocal : ∀ h : Finset.Iic k → X,
        seededPrefixProduct seed m k h*g k ≤
          ∫⁻ y, seededPrefixProduct seed m k h*m k h y ∂κ k h := by
      intro h
      have hmk : Measurable (m k h) := (hm k).comp (measurable_const.prodMk measurable_id)
      rw [lintegral_const_mul _ hmk]
      by_cases hp : seededPrefixProduct seed m k h = 0
      · simp [hp]
      · exact mul_le_mul_right (hmean k h hp) _
    have hi := lintegral_mono (μ := μ.map (Preorder.frestrictLe k)) hlocal
    rw [lintegral_mul_const _ hg, lintegral_map hg (by fun_prop)] at hi
    change (∫⁻ z, seededTrajectoryProduct seed m k z ∂μ)*g k ≤ _ at hi
    rw [Fin.prod_univ_castSucc]
    exact (mul_le_mul_left ih (g k)).trans (hi.trans_eq he)

end
end RandomViability
