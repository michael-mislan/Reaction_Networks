import proofs.OverlappingSiphonInvasion.SampledRepulsion

noncomputable section
open Set Filter
namespace OverlappingSiphonInvasion

theorem compact_product_collar {E : Type*} [TopologicalSpace E]
    (K : Set E) (hK : IsCompact K) (P A : E → ℝ)
    (hP : Continuous P) (hA : Continuous A) (hP0 : ∀ z ∈ K, 0 ≤ P z)
    (hb : ∀ z ∈ K, P z = 0 → 1 < A z) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ z ∈ K, P z ≤ ε → 1 < A z := by
  let B := K ∩ {z | A z ≤ 1}
  have hB : IsCompact B := hK.inter_right (isClosed_le hA continuous_const)
  by_cases hn : B.Nonempty
  · obtain ⟨z,hz,hmin⟩ := hB.exists_isMinOn hn hP.continuousOn
    have hpz : 0 < P z := by
      have hp0 := hP0 z hz.1
      by_contra hh
      have he : P z = 0 := le_antisymm (not_lt.mp hh) hp0
      exact (not_le_of_gt (hb z hz.1 he)) hz.2
    refine ⟨P z/2,by linarith,?_⟩
    intro w hw hsmall
    by_contra hh
    have hle : A w ≤ 1 := not_lt.mp hh
    have hmin' : P z ≤ P w := hmin ⟨hw,hle⟩
    linarith
  · refine ⟨1,by norm_num,?_⟩
    intro z hz _
    by_contra hh
    exact hn ⟨z,hz,not_lt.mp hh⟩

/-- A continuous boundary growth multiplier yields a uniform eventual sampled
product floor on the entire compact set. All multipliers remain exact. -/
theorem compact_sampled_product_floor {E : Type*} [TopologicalSpace E]
    (K : Set E) (hK : IsCompact K) (f : E → E) (P A : E → ℝ)
    (hf : ∀ z ∈ K, f z ∈ K) (hP : Continuous P) (hA : Continuous A)
    (hP0 : ∀ z ∈ K, 0 ≤ P z)
    (hmult : ∀ z ∈ K, P (f z) = Real.exp (A z)*P z)
    (hb : ∀ z ∈ K, P z = 0 → 1 < A z) :
    ∃ η : ℝ, 0 < η ∧ ∀ z ∈ K, 0 < P z → ∀ᶠ n : ℕ in atTop, η ≤ P (f^[n] z) := by
  obtain ⟨ε,hε,hcollar⟩ := compact_product_collar K hK P A hP hA hP0 hb
  obtain ⟨b,hbnd⟩ := hK.bddBelow_image hA.continuousOn
  let c := min 1 (Real.exp b)
  have hc : 0 < c := lt_min (by norm_num) (Real.exp_pos b)
  have hc1 : c ≤ 1 := min_le_left _ _
  have hiter : ∀ (n : ℕ) z, z ∈ K → f^[n] z ∈ K := by
    intro n
    induction n with
    | zero => intro z hz; exact hz
    | succ n ih =>
      intro z hz
      rw [Function.iterate_succ_apply']
      exact hf _ (ih z hz)
  refine ⟨c*ε,mul_pos hc hε,?_⟩
  intro z hz hpz
  have hpos : ∀ n : ℕ, 0 < P (f^[n] z) := by
    intro n
    induction n with
    | zero => exact hpz
    | succ n ih =>
      rw [Function.iterate_succ_apply',hmult _ (hiter n z hz)]
      exact mul_pos (Real.exp_pos _) ih
  apply sampled_growth_eventual_floor (fun n => P (f^[n] z)) ε c hε hc hc1 hpos
  · intro n
    rw [Function.iterate_succ_apply',hmult _ (hiter n z hz)]
    have hh : b ≤ A (f^[n] z) := hbnd ⟨f^[n] z,hiter n z hz,rfl⟩
    exact mul_le_mul_of_nonneg_right
      ((min_le_right _ _).trans (Real.exp_le_exp.mpr hh)) (hpos n).le
  · intro n hn
    rw [Function.iterate_succ_apply',hmult _ (hiter n z hz)]
    have hh := hcollar (f^[n] z) (hiter n z hz) hn
    have he : 2 ≤ Real.exp (A (f^[n] z)) :=
      (by linarith [Real.add_one_le_exp (1:ℝ)] : (2:ℝ) ≤ Real.exp 1).trans
        (Real.exp_le_exp.mpr hh.le)
    exact mul_le_mul_of_nonneg_right he (hpos n).le

end OverlappingSiphonInvasion
