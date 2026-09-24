import proofs.CompositionalMemory.SmoothQuadraticCap
import proofs.CompositionalMemory.SixthCapDerivativeBounds
import Mathlib.Analysis.Convex.Deriv

namespace CompositionalMemory
open Set

private theorem shifted_derivative (x : ℝ) :
    HasDerivAt (fun y : ℝ => 2*y^6-y^12-6*y^2) (12*x^5-12*x^11-12*x) x := by
  convert ((((hasDerivAt_id x).pow 6).const_mul 2).sub ((hasDerivAt_id x).pow 12)).sub
    (((hasDerivAt_id x).pow 2).const_mul 6) using 1
  dsimp only [id]
  ring

private theorem shifted_second (x : ℝ) :
    HasDerivAt (fun y : ℝ => 12*y^5-12*y^11-12*y) (60*x^4-132*x^10-12) x := by
  convert ((((hasDerivAt_id x).pow 5).const_mul 12).sub
    (((hasDerivAt_id x).pow 11).const_mul 12)).sub ((hasDerivAt_id x).const_mul 12) using 1
  dsimp only [id]
  ring

private theorem shifted_concave :
    ConcaveOn ℝ (Icc (0 : ℝ) 1) (fun y : ℝ => 2*y^6-y^12-6*y^2) := by
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc 0 1) (by fun_prop)
    (fun x _ => (shifted_derivative x).hasDerivWithinAt)
    (fun x _ => (shifted_second x).hasDerivWithinAt)
  intro x hx
  have hm : x ∈ Icc (0 : ℝ) 1 := interior_subset hx
  linarith only [sixth_cap_second_le_twelve x hm.1 hm.2]

theorem sixth_polynomial_taylor (u y : ℝ) (hu : u ∈ Icc (0 : ℝ) 1)
    (hy : y ∈ Icc (0 : ℝ) 1) :
    2*y^6-y^12 ≤ 2*u^6-u^12+(12*u^5-12*u^11)*(y-u)+6*(y-u)^2 := by
  rcases lt_trichotomy u y with h | h | h
  · have hs := shifted_concave.slope_le_of_hasDerivAt hu hy h (shifted_derivative u)
    rw [slope_def_field] at hs
    have hh := (div_le_iff₀ (sub_pos.mpr h)).mp hs
    nlinarith only [hh]
  · subst y; ring_nf; exact le_rfl
  · have hs := shifted_concave.le_slope_of_hasDerivAt hy hu h (shifted_derivative u)
    rw [slope_def_field] at hs
    have hh := (le_div_iff₀ (sub_pos.mpr h)).mp hs
    nlinarith only [hh]

theorem sixth_cap_eq_polynomial (u : ℝ) (hl : 0 ≤ u) (hu : u ≤ 1) :
    smoothQuadraticCap (u^6)=2*u^6-u^12 := by
  have hp : u^6 ≤ 1 := pow_le_one₀ hl hu
  rw [smoothQuadraticCap,if_pos hp]
  ring

theorem sixth_cap_slope_nonneg (u : ℝ) (hl : 0 ≤ u) (hu : u ≤ 1) :
    0 ≤ 12*u^5-12*u^11 := by
  have hp : u^6 ≤ 1 := pow_le_one₀ hl hu
  have hh := mul_nonneg (pow_nonneg hl 5) (sub_nonneg.mpr hp)
  nlinarith only [hh]

/-- The initial-allocation estimate needs a one-sided Taylor bound even
when partition or refill noise takes the newborn outside the unit region. -/
theorem sixth_cap_taylor (u y : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) (hy : 0 ≤ y) :
    smoothQuadraticCap (y^6) ≤ smoothQuadraticCap (u^6)+
      (12*u^5-12*u^11)*(y-u)+6*(y-u)^2 := by
  rw [sixth_cap_eq_polynomial u hu.1 hu.2]
  by_cases hh : y ≤ 1
  · rw [sixth_cap_eq_polynomial y hy hh]
    exact sixth_polynomial_taylor u y hu ⟨hy,hh⟩
  · have ht := sixth_polynomial_taylor u 1 hu (by norm_num)
    norm_num at ht
    have hs := mul_nonneg (sixth_cap_slope_nonneg u hu.1 hu.2)
      (show 0 ≤ y-1 by linarith)
    have hq := mul_nonneg (show 0 ≤ y-1 by linarith)
      (show 0 ≤ y+1-2*u by linarith [hu.2])
    nlinarith only [ht,hs,hq,smoothQuadraticCap_le_one (y^6)]

/-- Separate the centered linear noise from its nonnegative quadratic energy.
Only a second moment of the quadratic energy is needed after this bound. -/
theorem sixth_cap_noise_upper (u s q : ℝ) (hu : u ∈ Icc (0 : ℝ) 1)
    (hD : 0 ≤ u+2*s+q) (hcross : s^2 ≤ u*q) :
    smoothQuadraticCap ((u+2*s+q)^6) ≤ smoothQuadraticCap (u^6)+
      2*(12*u^5-12*u^11)*s+(12*u^5-12*u^11+48*u)*q+12*q^2 := by
  have ht := sixth_cap_taylor u (u+2*s+q) hu hD
  nlinarith only [ht,hcross,sq_nonneg (2*s-q)]

end CompositionalMemory
