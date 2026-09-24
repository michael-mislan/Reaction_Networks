import Mathlib

namespace RAF1519.Refinement
noncomputable section
open Filter
open scoped Topology

/-- Elapsed portion of one holding interval, as a continuous function of time. -/
def holdingRamp (a h t : ℝ) : ℝ := max 0 (min h (t-a))

theorem holdingRamp_continuous (a h : ℝ) : Continuous (holdingRamp a h) := by
  unfold holdingRamp
  fun_prop

theorem holdingRamp_right_derivative (a h t : ℝ) (hh : 0 ≤ h) :
    HasDerivWithinAt (holdingRamp a h) (if a ≤ t ∧ t < a+h then 1 else 0) (Set.Ici t) t := by
  by_cases hb : t < a
  · have he : holdingRamp a h =ᶠ[𝓝[Set.Ici t] t] (fun _ => (0:ℝ)) := by
      filter_upwards [(gt_mem_nhds hb).filter_mono nhdsWithin_le_nhds] with u hu
      unfold holdingRamp
      exact max_eq_left ((min_le_right h (u-a)).trans (sub_nonpos.mpr hu.le))
    have hd := (hasDerivAt_const t (0:ℝ)).hasDerivWithinAt.congr_of_eventuallyEq_of_mem he
      (by simp : t ∈ Set.Ici t)
    simpa only [if_neg (show ¬(a ≤ t ∧ t < a+h) from fun hx => not_le_of_gt hb hx.1)] using hd
  · have ha : a ≤ t := le_of_not_gt hb
    by_cases he : a+h ≤ t
    · have heq : holdingRamp a h =ᶠ[𝓝[Set.Ici t] t] (fun _ => h) := by
        filter_upwards [self_mem_nhdsWithin] with u hu
        have hu' : h ≤ u-a := by change t ≤ u at hu; linarith
        simp only [holdingRamp,min_eq_left hu',max_eq_right hh]
      have hd := (hasDerivAt_const t h).hasDerivWithinAt.congr_of_eventuallyEq_of_mem heq
        (by simp : t ∈ Set.Ici t)
      simpa only [if_neg (show ¬(a ≤ t ∧ t < a+h) from fun hx => not_lt_of_ge he hx.2)] using hd
    · have ht : t < a+h := lt_of_not_ge he
      have heq : holdingRamp a h =ᶠ[𝓝[Set.Ici t] t] (fun u => u-a) := by
        filter_upwards [self_mem_nhdsWithin,(gt_mem_nhds ht).filter_mono nhdsWithin_le_nhds] with u hu hul
        change t ≤ u at hu
        have hl : 0 ≤ u-a := by linarith
        have hr : u-a ≤ h := by linarith
        simp only [holdingRamp,min_eq_right hr,max_eq_right hl]
      have hd := ((hasDerivAt_id t).sub_const a).hasDerivWithinAt.congr_of_eventuallyEq_of_mem heq
        (by simp : t ∈ Set.Ici t)
      simpa only [if_pos (And.intro ha ht)] using hd

end
end RAF1519.Refinement

