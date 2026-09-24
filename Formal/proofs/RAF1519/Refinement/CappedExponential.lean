import Mathlib

namespace RAF1519.Refinement
noncomputable section
open Filter
open scoped Topology

def cappedExponential (c a H t : ℝ) : ℝ := min (c*Real.exp (a*t)) H

theorem cappedExponential_continuous (c a H : ℝ) : Continuous (cappedExponential c a H) := by
  unfold cappedExponential
  fun_prop

theorem cappedExponential_right_derivative (c a H t : ℝ) (hc : 0 ≤ c) (ha : 0 ≤ a) :
    HasDerivWithinAt (cappedExponential c a H)
      (if c*Real.exp (a*t) < H then a*c*Real.exp (a*t) else 0) (Set.Ici t) t := by
  have hd : HasDerivAt (fun u => c*Real.exp (a*u)) (a*c*Real.exp (a*t)) t := by
    simpa [mul_assoc,mul_comm,mul_left_comm] using (((hasDerivAt_id t).const_mul a).exp).const_mul c
  by_cases hlt : c*Real.exp (a*t) < H
  · have he : cappedExponential c a H =ᶠ[𝓝[Set.Ici t] t] (fun u => c*Real.exp (a*u)) := by
      have hevent : ∀ᶠ u in 𝓝 t, c*Real.exp (a*u) < H :=
        hd.continuousAt.eventually (gt_mem_nhds hlt)
      filter_upwards [hevent.filter_mono nhdsWithin_le_nhds] with u hu
      exact min_eq_left hu.le
    simpa only [if_pos hlt] using hd.hasDerivWithinAt.congr_of_eventuallyEq_of_mem he (by simp : t ∈ Set.Ici t)
  · have he : cappedExponential c a H =ᶠ[𝓝[Set.Ici t] t] (fun _ => H) := by
      filter_upwards [self_mem_nhdsWithin] with u hu
      have hm := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hu ha)) hc
      exact min_eq_right ((le_of_not_gt hlt).trans hm)
    simpa only [if_neg hlt] using (hasDerivAt_const t H).hasDerivWithinAt.congr_of_eventuallyEq_of_mem he
      (by simp : t ∈ Set.Ici t)

end
end RAF1519.Refinement
