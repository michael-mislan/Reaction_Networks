import Mathlib

noncomputable section
open Filter
namespace OverlappingSiphonInvasion

theorem relative_growth_upper (y v : ℝ → ℝ) (L : ℝ)
    (hd : ∀ t, 0 ≤ t → HasDerivAt y (v t) t)
    (hv : ∀ t, 0 ≤ t → v t ≤ L*y t) (t : ℝ) (ht : 0 ≤ t) :
    y t ≤ Real.exp (L*t)*y 0 := by
  have hh := le_gronwallBound_of_liminf_deriv_right_le (b := t) (K := L) (ε := 0)
    (fun s hs => (hd s hs.1).continuousAt.continuousWithinAt)
    (fun s hs _ hr => (hd s hs.1).hasDerivWithinAt.liminf_right_slope_le hr)
    (le_refl (y 0)) (fun s hs => by simpa using hv s hs.1) t ⟨ht,le_rfl⟩
  simpa only [gronwallBound_ε0,sub_zero,mul_comm] using hh

/-- A bound on growth up to the next sample rules out arbitrarily deep dips
between samples. The resulting floor is uniform in the trajectory. -/
theorem sampled_to_continuous_floor (y : ℝ → ℝ) (T M η : ℝ) (hT : 0 < T) (hM : 0 < M)
    (hupper : ∀ t s, 0 ≤ t → 0 ≤ s → s ≤ T → y (t+s) ≤ M*y t)
    (hsample : ∀ᶠ n : ℕ in atTop, η ≤ y ((n:ℝ)*T)) :
    ∀ᶠ t : ℝ in atTop, η/M ≤ y t := by
  obtain ⟨n0,hn0⟩ := eventually_atTop.1 hsample
  apply eventually_atTop.2
  refine ⟨(n0:ℝ)*T,?_⟩
  intro t ht
  have ht0 : 0 ≤ t := (mul_nonneg (Nat.cast_nonneg n0) hT.le).trans ht
  let n := Nat.floor (t/T)+1
  have hfloor : (Nat.floor (t/T):ℝ) ≤ t/T := Nat.floor_le (div_nonneg ht0 hT.le)
  have hceil : t/T < (n:ℝ) := by
    simpa only [n,Nat.cast_add,Nat.cast_one] using Nat.lt_floor_add_one (t/T)
  have hn0' : n0 ≤ n := (Nat.le_floor ((le_div_iff₀ hT).mpr ht)).trans (Nat.le_succ _)
  have htn : t ≤ (n:ℝ)*T := ((div_lt_iff₀ hT).mp hceil).le
  have hgap : (n:ℝ)*T-t ≤ T := by
    have hh := (le_div_iff₀ hT).mp hfloor
    dsimp [n]
    push_cast
    nlinarith only [hh]
  have hh := hupper t ((n:ℝ)*T-t) ht0 (sub_nonneg.mpr htn) hgap
  have hy := hn0 n hn0'
  have hh' : y ((n:ℝ)*T) ≤ M*y t := by simpa only [add_sub_cancel] using hh
  apply (div_le_iff₀ hM).mpr
  nlinarith only [hy,hh']

end OverlappingSiphonInvasion
