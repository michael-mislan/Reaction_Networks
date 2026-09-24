import Mathlib

open Filter Topology

namespace CoreCouplingGlobal

/-- A scalar differential inequality gives eventual entry below any strict
upper bound on its limiting comparison equilibrium. -/
theorem eventual_upper_of_linear_drift (y v : ℝ → ℝ) (T C k R : ℝ)
    (hk : 0 < k) (hR : C/k < R)
    (hd : ∀ t, T ≤ t → HasDerivAt y (v t) t)
    (hb : ∀ t, T ≤ t → v t ≤ C-k*y t) :
    ∀ᶠ t in atTop, y t < R := by
  have hbound : ∀ t, T ≤ t → y t ≤ gronwallBound (y T) (-k) C (t-T) := by
    intro t ht
    have hc : ContinuousOn y (Set.Icc T t) := by
      intro s hs
      exact (hd s hs.1).continuousAt.continuousWithinAt
    have hg := le_gronwallBound_of_liminf_deriv_right_le (K := -k) (ε := C) hc
      (fun s hs _ hr => (hd s hs.1).hasDerivWithinAt.liminf_right_slope_le hr)
      (le_refl (y T)) (fun s hs => by linarith only [hb s hs.1])
    exact hg t ⟨ht,le_rfl⟩
  have he : Tendsto (fun t : ℝ => Real.exp (-k*(t-T))) atTop (𝓝 0) := by
    have ht : Tendsto (fun t : ℝ => t-T) atTop atTop := by
      simpa only [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-T) tendsto_id
    exact Real.tendsto_exp_atBot.comp
      (ht.const_mul_atTop_of_neg (neg_neg_of_pos hk))
  have hg : Tendsto (fun t => gronwallBound (y T) (-k) C (t-T)) atTop (𝓝 (C/k)) := by
    simp only [gronwallBound_of_K_ne_0 (ne_of_lt (neg_neg_of_pos hk))]
    convert (he.const_mul (y T)).add ((he.sub_const 1).const_mul (C/(-k))) using 1
    simp [div_neg]
  filter_upwards [hg.eventually_lt_const hR,eventually_ge_atTop T] with t ht htT
  exact (hbound t htT).trans_lt ht

end CoreCouplingGlobal
