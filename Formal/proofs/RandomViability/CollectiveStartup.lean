import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

set_option maxHeartbeats 20000

namespace RandomViability
open Set

/-- Scalar integrating-factor comparison on the actual finite time interval.
No equilibrium assumption or infinite-time limit is used. -/
theorem scalar_startup_lower (y dy : ℝ → ℝ) (a e t : ℝ) (ht : 0 ≤ t)
    (hd : ∀ s ∈ Icc 0 t, HasDerivAt y (dy s) s)
    (hb : ∀ s ∈ Icc 0 t, a*(e-y s) ≤ dy s) :
    (y 0-e)/Real.exp (a*t)+e ≤ y t := by
  let f : ℝ → ℝ := fun s => Real.exp (a*s)*(y s-e)
  have hf (s : ℝ) (hs : s ∈ Icc 0 t) :
      HasDerivAt f (Real.exp (a*s)*(dy s+a*(y s-e))) s := by
    have he := ((hasDerivAt_id s).const_mul a).exp
    convert he.mul ((hd s hs).sub_const e) using 1
    dsimp only [id_eq]
    ring
  have hc : ContinuousOn f (Icc 0 t) := fun s hs => (hf s hs).continuousAt.continuousWithinAt
  have hm : MonotoneOn f (Icc 0 t) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 t) hc
    · intro s hs
      exact (hf s (interior_subset hs)).hasDerivWithinAt
    · intro s hs
      apply mul_nonneg (Real.exp_pos _).le
      linarith [hb s (interior_subset hs)]
  have he := hm (left_mem_Icc.mpr ht) (right_mem_Icc.mpr ht) ht
  have he' : y 0-e ≤ Real.exp (a*t)*(y t-e) := by simpa [f] using he
  have hdiv : (y 0-e)/Real.exp (a*t) ≤ y t-e := by
    apply (div_le_iff₀ (Real.exp_pos _)).2
    nlinarith only [he']
  linarith

theorem scalar_startup_floor (y dy : ℝ → ℝ) (a e t : ℝ) (ht : 0 ≤ t)
    (hd : ∀ s ∈ Icc 0 t, HasDerivAt y (dy s) s)
    (hb : ∀ s ∈ Icc 0 t, a*(e-y s) ≤ dy s) (h0 : e ≤ y 0) : e ≤ y t := by
  have h := scalar_startup_lower y dy a e t ht hd hb
  have hn : 0 ≤ (y 0-e)/Real.exp (a*t) := div_nonneg (by linarith) (Real.exp_pos _).le
  linarith

end RandomViability
