import proofs.FiniteCopy.FiniteJump

namespace CompositionalMemory
open FiniteCopy Filter Set
open scoped Topology

/-- A C1 concave cap. It reaches one at the recovery-tube boundary and is
constant outside, allowing local polynomial inequalities to control all states. -/
noncomputable def smoothQuadraticCap (e : ℝ) : ℝ := if e ≤ 1 then 2*e-e*e else 1
noncomputable def smoothQuadraticSlope (e : ℝ) : ℝ := if e ≤ 1 then 2-2*e else 0

theorem smoothQuadraticCap_le_one (e : ℝ) : smoothQuadraticCap e ≤ 1 := by
  by_cases h : e ≤ 1
  · simp only [smoothQuadraticCap,if_pos h]
    nlinarith [sq_nonneg (e-1)]
  · simp [smoothQuadraticCap,h]

theorem smoothQuadraticCap_nonneg (e : ℝ) (he : 0 ≤ e) : 0 ≤ smoothQuadraticCap e := by
  by_cases h : e ≤ 1
  · simp only [smoothQuadraticCap,if_pos h]
    nlinarith [mul_nonneg he (sub_nonneg.mpr h)]
  · simp [smoothQuadraticCap,h]

theorem smoothQuadraticSlope_bounds (e : ℝ) (he : 0 ≤ e) :
    0 ≤ smoothQuadraticSlope e ∧ smoothQuadraticSlope e ≤ 2 := by
  by_cases h : e ≤ 1
  · simp only [smoothQuadraticSlope,if_pos h]
    constructor <;> linarith
  · norm_num [smoothQuadraticSlope,h]

theorem smoothQuadraticCap_tangent (a b : ℝ) :
    smoothQuadraticCap b ≤ smoothQuadraticCap a+smoothQuadraticSlope a*(b-a) := by
  by_cases ha : a ≤ 1
  · by_cases hb : b ≤ 1
    · simp only [smoothQuadraticCap,smoothQuadraticSlope,if_pos ha,if_pos hb]
      nlinarith [sq_nonneg (b-a)]
    · have hprod := mul_nonneg (sub_nonneg.mpr ha) (show 0 ≤ b-1 by linarith)
      simp only [smoothQuadraticCap,smoothQuadraticSlope,if_pos ha,if_neg hb]
      nlinarith [sq_nonneg (1-a)]
  · simp only [smoothQuadraticCap,smoothQuadraticSlope,if_neg ha,zero_mul,add_zero]
    exact smoothQuadraticCap_le_one b

theorem smoothQuadraticCap_slope_at_one :
    slope smoothQuadraticCap 1=fun y : ℝ => max (1-y) 0 := by
  funext y
  rw [slope_def_field]
  by_cases hy : y=1
  · subst y; norm_num [smoothQuadraticCap]
  · by_cases h : y ≤ 1
    · rw [max_eq_left (sub_nonneg.mpr h)]
      norm_num [smoothQuadraticCap,h]
      field_simp
      ring
    · have hn : 1-y ≤ 0 := by linarith
      norm_num [smoothQuadraticCap,h,max_eq_right hn]

theorem hasDerivAt_smoothQuadraticCap (e : ℝ) :
    HasDerivAt smoothQuadraticCap (smoothQuadraticSlope e) e := by
  rcases lt_trichotomy e 1 with h | h | h
  · have hp : HasDerivAt (fun y : ℝ => 2*y-y*y) (2-2*e) e := by
      convert ((hasDerivAt_id e).const_mul 2).sub ((hasDerivAt_id e).mul (hasDerivAt_id e)) using 1
      dsimp only [id]
      ring
    simp only [smoothQuadraticSlope,if_pos h.le]
    apply hp.congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds h] with y hy
    simp [smoothQuadraticCap,show y ≤ 1 from le_of_lt hy]
  · subst e
    simp only [smoothQuadraticSlope,le_refl,if_true,mul_one,sub_self]
    apply hasDerivAt_iff_tendsto_slope.mpr
    rw [smoothQuadraticCap_slope_at_one]
    have hc : Continuous (fun y : ℝ => max (1-y) 0) :=
      (continuous_const.sub continuous_id).max continuous_const
    have ht : Tendsto (fun y : ℝ => max (1-y) 0) (𝓝 (1 : ℝ)) (𝓝 (0 : ℝ)) := by
      simpa using hc.tendsto 1
    exact ht.mono_left nhdsWithin_le_nhds
  · simp only [smoothQuadraticSlope,if_neg (not_le.mpr h)]
    apply (hasDerivAt_const e (1 : ℝ)).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds h] with y hy
    simp [smoothQuadraticCap,show ¬y ≤ 1 from not_le.mpr hy]

theorem smoothQuadraticCap_generator {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] (M : FiniteJumpModel α β) (E : α → ℝ) (x : α) :
    M.generator (fun y => smoothQuadraticCap (E y)) x ≤
      smoothQuadraticSlope (E x)*M.generator E x := by
  unfold FiniteJumpModel.generator
  calc
    _ ≤ ∑ r,M.rate x r*(smoothQuadraticSlope (E x)*(E (M.next x r)-E x)) := by
      apply Finset.sum_le_sum
      intro r _
      apply mul_le_mul_of_nonneg_left _ (M.nonneg x r)
      linarith only [smoothQuadraticCap_tangent (E x) (E (M.next x r))]
    _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro r _; ring

/-- Local time-plus-generator control is enough for a global bounded C1
barrier. This is an algebraic ingredient, not yet finite-time law transport. -/
theorem smoothQuadraticCap_local_to_global {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] (M : FiniteJumpModel α β) (E dE : α → ℝ) (c : ℝ)
    (hc : 0 ≤ c) (hE : ∀ x, 0 ≤ E x)
    (hlocal : ∀ x, E x ≤ 1 → dE x+M.generator E x ≤ c) (x : α) :
    smoothQuadraticSlope (E x)*dE x+M.generator (fun y => smoothQuadraticCap (E y)) x ≤ 2*c := by
  have hg := smoothQuadraticCap_generator M E x
  by_cases hx : E x ≤ 1
  · have hs := smoothQuadraticSlope_bounds (E x) (hE x)
    have hl := mul_le_mul_of_nonneg_left (hlocal x hx) hs.1
    have hu := mul_le_mul_of_nonneg_right hs.2 hc
    nlinarith only [hg,hl,hu]
  · simp only [smoothQuadraticSlope,if_neg hx,zero_mul,zero_add] at hg ⊢
    linarith

end CompositionalMemory
