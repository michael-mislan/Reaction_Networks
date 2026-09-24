import proofs.RandomViability.ProductivePrefix
import proofs.RandomViability.MarkedWindow
import proofs.RandomViability.JumpInitial

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory Set
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 30000

variable {α β : Type*} [mα : MeasurableSpace α] [cα : Countable α]
  [sα : MeasurableSingletonClass α] [fβ : Fintype β]
  [mβ : MeasurableSpace β] [sβ : MeasurableSingletonClass β]

def prescribedSeed (s : ℕ → α) (y : JumpState α β) : ℝ≥0∞ :=
  if y.1 = s 0 then 1 else 0

def prescribedFactor (s : ℕ → α) (b : ℕ → β) (a d : ℕ → ℝ)
    (k : ℕ) (_ : Finset.Iic k → JumpState α β) (y : JumpState α β) : ℝ≥0∞ :=
  if y ∈ markedWindow (s (k+1)) (b k) (a k) (d k) then 1 else 0

def prescribedCylinder (s : ℕ → α) (b : ℕ → β) (a d : ℕ → ℝ)
    (K : ℕ) : Set (ℕ → JumpState α β) :=
  {z | (z 0).1 = s 0 ∧ ∀ i : Fin K,
    z (i+1) ∈ markedWindow (s (i+1)) (b i) (a i) (d i)}

omit mα cα sα fβ mβ sβ in
theorem prescribed_prefix_last (s : ℕ → α) (b : ℕ → β) (a d : ℕ → ℝ)
    (k : ℕ) (h : Finset.Iic k → JumpState α β)
    (hp : seededPrefixProduct (prescribedSeed s) (prescribedFactor s b a d) k h ≠ 0) :
    (h ⟨k, Finset.mem_Iic.mpr le_rfl⟩).1 = s k := by
  cases k with
  | zero =>
    simpa [seededPrefixProduct, prescribedSeed, prefixProduct] using hp
  | succ k =>
    have hn : prefixProduct (prescribedFactor s b a d) (k+1) h ≠ 0 :=
      (mul_ne_zero_iff.mp hp).2
    have hi := (Finset.prod_ne_zero_iff.mp hn) (⟨k, Nat.lt_succ_self k⟩ : Fin (k+1))
      (Finset.mem_univ _)
    simp only [prescribedFactor, ne_eq, ite_eq_right_iff, one_ne_zero, imp_false,
      not_not] at hi
    exact hi.1

omit cα fβ in
theorem prescribed_cylinder_measurable (s : ℕ → α) (b : ℕ → β) (a d : ℕ → ℝ)
    (K : ℕ) : MeasurableSet (prescribedCylinder s b a d K) := by
  have h0 : MeasurableSet {z : ℕ → JumpState α β | (z 0).1 = s 0} :=
    (measurable_pi_apply 0).fst (measurableSet_singleton (s 0))
  have hi (i : Fin K) : MeasurableSet {z : ℕ → JumpState α β |
      z (i+1) ∈ markedWindow (s (i+1)) (b i) (a i) (d i)} :=
    (measurable_pi_apply ((i : ℕ)+1))
      (markedWindow_measurable (s (i+1)) (b i) (a i) (d i))
  refine h0.inter ?_
  convert MeasurableSet.iInter hi using 1
  ext z
  simp only [Set.mem_iInter, Set.mem_setOf_eq]
  rfl

omit mα cα sα fβ mβ sβ in
theorem prescribed_product_indicator (s : ℕ → α) (b : ℕ → β) (a d : ℕ → ℝ)
    (K : ℕ) (z : ℕ → JumpState α β) :
    seededTrajectoryProduct (prescribedSeed s) (prescribedFactor s b a d) K z =
      (prescribedCylinder s b a d K).indicator (fun _ => (1 : ℝ≥0∞)) z := by
  by_cases h0 : (z 0).1 = s 0
  · by_cases hall : ∀ i : Fin K, z (i+1) ∈ markedWindow (s (i+1)) (b i) (a i) (d i)
    · simp [seededTrajectoryProduct, prescribedSeed, trajectoryProduct,
        prescribedFactor, prescribedCylinder, h0, hall]
    · have hex : ∃ i : Fin K, z (i+1) ∉ markedWindow (s (i+1)) (b i) (a i) (d i) :=
        not_forall.mp hall
      obtain ⟨i,hi⟩ := hex
      have hz : trajectoryProduct (prescribedFactor s b a d) K z = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        simp [prescribedFactor, hi]
      simp [seededTrajectoryProduct, hz, prescribedCylinder, h0, hall]
  · simp [seededTrajectoryProduct, prescribedSeed, prescribedCylinder, h0]

/-- An actual finite jump cylinder has at least the product of its paid label
and holding-window costs. All competing channels remain in the total rate. -/
theorem prescribed_cylinder_probability_lower
    (next : α → β → α) (rate : α → β → ℝ)
    (hr : ∀ x b, 0 ≤ rate x b) (ht : ∀ x, 0 < ∑ b, rate x b)
    (s : ℕ → α) (b : ℕ → β) (a d Q e : ℕ → ℝ) (K : ℕ)
    (hstep : ∀ k < K, next (s k) (b k) = s (k+1))
    (hQ : ∀ k < K, (∑ c, rate (s k) c) ≤ Q k)
    (ha : ∀ k < K, 0 ≤ a k) (hd : ∀ k < K, 0 ≤ d k)
    (he : ∀ k < K, 0 ≤ e k) (hb : ∀ k < K, e k ≤ rate (s k) (b k)) :
    (∏ i : Fin K, ENNReal.ofReal (e i*d i*Real.exp (-Q i*(a i+d i)))) ≤
      jumpTrajectoryLaw (s 0) next rate hr ht (prescribedCylinder s b a d K) := by
  let μ := jumpTrajectoryLaw (s 0) next rate hr ht
  have hs : Measurable (prescribedSeed s : JumpState α β → ℝ≥0∞) :=
    Measurable.ite (measurableSet_eq_fun measurable_fst measurable_const)
      measurable_const measurable_const
  have hm : ∀ k, Measurable (fun p : (Finset.Iic k → JumpState α β) × JumpState α β =>
      prescribedFactor s b a d k p.1 p.2) := by
    intro k
    exact Measurable.ite (measurable_snd (markedWindow_measurable _ _ _ _))
      measurable_const measurable_const
  have hinit : (∫⁻ z, prescribedSeed s (z 0) ∂μ) = 1 := by
    calc
      _ = ∫⁻ _ : ℕ → JumpState α β, (1 : ℝ≥0∞) ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [jumpTrajectory_initial_population (s 0) next rate hr ht] with z hz
        simp [prescribedSeed, hz]
      _ = 1 := by simp [μ]
  let g : ℕ → ℝ≥0∞ := fun k =>
    if k < K then ENNReal.ofReal (e k*d k*Real.exp (-Q k*(a k+d k))) else 0
  have hmean : ∀ k h, seededPrefixProduct (prescribedSeed s)
      (prescribedFactor s b a d) k h ≠ 0 →
      g k ≤ ∫⁻ y, prescribedFactor s b a d k h y ∂jumpHistoryKernel next rate hr ht k h := by
    intro k h hp
    by_cases hk : k < K
    · have hlast := prescribed_prefix_last s b a d k h hp
      have heq : jumpHistoryKernel next rate hr ht k h = jumpStateKernel next rate hr ht (s k) := by
        change jumpStateKernel next rate hr ht _ = _
        exact congrArg (jumpStateKernel next rate hr ht) hlast
      rw [heq]
      have hint : (∫⁻ y, prescribedFactor s b a d k h y ∂jumpStateKernel next rate hr ht (s k)) =
          jumpStateKernel next rate hr ht (s k) (markedWindow (s (k+1)) (b k) (a k) (d k)) := by
        simpa only [prescribedFactor, Set.indicator, Pi.one_apply] using
          (lintegral_indicator_one (μ := jumpStateKernel next rate hr ht (s k))
            (markedWindow_measurable (s (k+1)) (b k) (a k) (d k)))
      rw [hint]
      simp only [g, if_pos hk]
      rw [← hstep k hk]
      exact jumpStateKernel_marked_window_lower next rate hr ht (s k) (b k)
        (Q k) (a k) (d k) (e k) (hQ k hk) (ha k hk) (hd k hk) (he k hk) (hb k hk)
    · simp [g, hk]
  have hout := prescribed_prefix_product_lower μ (jumpHistoryKernel next rate hr ht)
    (fun _ => Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure)
    (prescribedSeed s) hs hinit (prescribedFactor s b a d) hm g hmean K
  have hi : (∫⁻ z, seededTrajectoryProduct (prescribedSeed s) (prescribedFactor s b a d) K z ∂μ) =
      μ (prescribedCylinder s b a d K) := by
    simp_rw [prescribed_product_indicator]
    exact lintegral_indicator_one (prescribed_cylinder_measurable s b a d K)
  rw [hi] at hout
  simpa only [g, Fin.isLt, if_true] using hout

end
end RandomViability
