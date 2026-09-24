import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

/-! Finite-interval comparison. Applied separately on smooth protocol segments;
no assay-to-regeneration bridge is assumed or claimed. -/
namespace G6PDReserve
noncomputable section
open Set

theorem upper_drift_comparison (g d : ℝ → ℝ) (b c T : ℝ) (hT : 0 ≤ T)
    (hd : ∀ t ∈ Icc 0 T, HasDerivAt g (d t) t)
    (hbound : ∀ t ∈ Icc 0 T, d t ≤ b * (c - g t)) :
    g T ≤ c + (g 0 - c) * Real.exp (-b*T) := by
  let F : ℝ → ℝ := fun t => Real.exp (b*t) * (g t-c)
  have hF (t : ℝ) (ht : t ∈ Icc 0 T) :
      HasDerivAt F (Real.exp (b*t) * (d t + b*(g t-c))) t := by
    convert (((hasDerivAt_id t).const_mul b).exp.mul ((hd t ht).sub_const c)) using 1
    dsimp [F]
    ring
  have hmono : AntitoneOn F (Icc 0 T) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 T)
    · intro t ht
      exact (hF t ht).continuousAt.continuousWithinAt
    · intro t ht
      exact (hF t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(hF t (interior_subset ht)).deriv]
      apply mul_nonpos_of_nonneg_of_nonpos (le_of_lt (Real.exp_pos _))
      have := hbound t (interior_subset ht)
      linarith
  have hFT := hmono (show 0 ∈ Icc (0:ℝ) T from ⟨le_rfl,hT⟩)
    (show T ∈ Icc (0:ℝ) T from ⟨hT,le_rfl⟩) hT
  dsimp [F] at hFT
  simp only [mul_zero, Real.exp_zero, one_mul] at hFT
  have he : Real.exp (-b*T) * Real.exp (b*T) = 1 := by
    rw [← Real.exp_add]
    have hz : -b*T + b*T = 0 := by ring
    rw [hz, Real.exp_zero]
  have hh := mul_le_mul_of_nonneg_left hFT (le_of_lt (Real.exp_pos (-b*T)))
  rw [← mul_assoc, he, one_mul] at hh
  nlinarith

theorem lower_drift_comparison (g d : ℝ → ℝ) (b c T : ℝ) (hT : 0 ≤ T)
    (hd : ∀ t ∈ Icc 0 T, HasDerivAt g (d t) t)
    (hbound : ∀ t ∈ Icc 0 T, b * (c - g t) ≤ d t) :
    c + (g 0 - c) * Real.exp (-b*T) ≤ g T := by
  have hh := upper_drift_comparison (fun t => -g t) (fun t => -d t) b (-c) T hT
    (fun t ht => (hd t ht).neg) (by
      intro t ht
      have := hbound t ht
      linarith)
  dsimp at hh
  linarith

/-- An upper-only carrier model excludes demand exceeding the maximal reserve
trajectory at any time. It cannot supply a positive guaranteed lower drift. -/
theorem constant_demand_exclusion (g d u v : ℝ → ℝ)
    (a b C q T : ℝ) (ha : 0 ≤ a) (hb : b ≠ 0) (hT : 0 ≤ T)
    (hd : ∀ t ∈ Icc 0 T, HasDerivAt g (d t) t)
    (hbalance : ∀ t ∈ Icc 0 T, d t = u t-v t)
    (hu : ∀ t ∈ Icc 0 T, u t ≤ b*(C-g t))
    (hv : ∀ t ∈ Icc 0 T, q ≤ v t)
    (hcap : v T ≤ a*g T) :
    q ≤ a * (C-q/b + (g 0-(C-q/b))*Real.exp (-b*T)) := by
  have hg := upper_drift_comparison g d b (C-q/b) T hT hd (by
    intro t ht
    rw [hbalance t ht]
    have hcancel : b*(q/b)=q := by field_simp
    have h1 := hu t ht
    have h2 := hv t ht
    nlinarith)
  exact le_trans (le_trans (hv T ⟨hT,le_rfl⟩) hcap) (mul_le_mul_of_nonneg_left hg ha)

end
end G6PDReserve
