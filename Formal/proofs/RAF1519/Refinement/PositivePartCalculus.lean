import proofs.RAF1519.Refinement.GraphBarrierEnergy

namespace RAF1519.Refinement
noncomputable section
open Filter Asymptotics
open scoped Topology

theorem hasDerivAt_positive_square (x : ℝ) :
    HasDerivAt (fun y : ℝ => (max 0 y)^2) (2*max 0 x) x := by
  rcases lt_trichotomy x 0 with hx|hx|hx
  · have he : (fun y : ℝ => (max 0 y)^2) =ᶠ[𝓝 x] (fun _ => (0:ℝ)) := by
      filter_upwards [gt_mem_nhds hx] with y hy
      simp only [max_eq_left hy.le,zero_pow (by decide : (2:ℕ) ≠ 0)]
    simpa only [max_eq_left hx.le,mul_zero] using
      (hasDerivAt_const x (0:ℝ)).congr_of_eventuallyEq he
  · subst x
    have hs : (fun y : ℝ => y^2) =o[𝓝 (0:ℝ)] (fun y => y) := by
      simpa using ((hasDerivAt_id (0:ℝ)).pow 2).isLittleO
    have hb : (fun y : ℝ => (max 0 y)^2) =O[𝓝 (0:ℝ)] (fun y => y^2) := by
      apply IsBigO.of_bound'
      apply Filter.Eventually.of_forall
      intro y
      rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (max 0 y)),
        abs_of_nonneg (sq_nonneg y)]
      by_cases hy : 0 ≤ y
      · simp only [max_eq_right hy,le_refl]
      · simp only [max_eq_left (le_of_not_ge hy),zero_pow (by decide : (2:ℕ) ≠ 0)]
        exact sq_nonneg y
    apply HasDerivAt.of_isLittleO
    simpa using hb.trans_isLittleO hs
  · have he : (fun y : ℝ => (max 0 y)^2) =ᶠ[𝓝 x] (fun y => y^2) := by
      filter_upwards [lt_mem_nhds hx] with y hy
      rw [max_eq_right hy.le]
    have hd := ((hasDerivAt_id x).pow 2).congr_of_eventuallyEq he
    simpa [max_eq_right hx.le] using hd

theorem hasDerivWithinAt_positive_square (f : ℝ → ℝ) (v t : ℝ) (s : Set ℝ)
    (h : HasDerivWithinAt f v s t) :
    HasDerivWithinAt (fun u => (max 0 (f u))^2) (2*max 0 (f t)*v) s t :=
  (hasDerivAt_positive_square (f t)).comp_hasDerivWithinAt t h

end
end RAF1519.Refinement
