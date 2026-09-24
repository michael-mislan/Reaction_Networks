import Mathlib

namespace CoreCouplingCAC

/-- A local strict Lyapunov estimate supplies its own invariant sublevel.
The conclusion applies on every time interval on which an actual solution is
defined; existence/continuation must be supplied separately. -/
theorem local_energy_barrier (f f' : ℝ → ℝ) (T ρ κ : ℝ)
    (hρ : 0 < ρ) (hκ : 0 < κ)
    (hc : ContinuousOn f (Set.Icc 0 T))
    (hd : ∀ t ∈ Set.Ico 0 T, HasDerivWithinAt f (f' t) (Set.Ici t) t)
    (h0 : f 0 ≤ ρ)
    (hb : ∀ t ∈ Set.Ico 0 T, f t ≤ ρ → f' t ≤ -κ*f t) :
    ∀ t ∈ Set.Icc 0 T, f t ≤ ρ ∧ f t ≤ f 0*Real.exp (-κ*t) := by
  have hi : ∀ t ∈ Set.Icc 0 T, f t ≤ ρ := by
    apply image_le_of_deriv_right_lt_deriv_boundary hc hd h0
      (fun _ => hasDerivAt_const _ ρ)
    intro t ht heq
    have h := hb t ht heq.le
    rw [heq] at h
    have hn : -κ*ρ < 0 := mul_neg_of_neg_of_pos (neg_neg_of_pos hκ) hρ
    exact lt_of_le_of_lt h hn
  have hg := le_gronwallBound_of_liminf_deriv_right_le (K := -κ) (ε := 0) hc
    (fun t ht _ hr => (hd t ht).liminf_right_slope_le hr)
    (le_refl (f 0))
    (fun t ht => (hb t ht (hi t ⟨ht.1,ht.2.le⟩)).trans (by simp))
  intro t ht
  refine ⟨hi t ht, ?_⟩
  have hh := hg t ht
  simpa [gronwallBound_ε0] using hh

end CoreCouplingCAC
