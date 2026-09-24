import Mathlib

namespace CompositionalMemory

theorem linear_exponential_absorption (x : ℝ) : x*Real.exp (-x) ≤ 2*Real.exp (-x/2) := by
  have hx : x/2 ≤ Real.exp (x/2) := by linarith only [Real.add_one_le_exp (x/2)]
  calc
    _ = (x/2)*(2*Real.exp (-x)) := by ring
    _ ≤ Real.exp (x/2)*(2*Real.exp (-x)) := mul_le_mul_of_nonneg_right hx (by positivity)
    _ = 2*(Real.exp (x/2)*Real.exp (-x)) := by ring
    _ = _ := by rw [← Real.exp_add]; congr 2; ring

theorem scaled_linear_exponential_absorption (α N g : ℝ) (hα : 0 < α) (hg : 0 < g) :
    N*Real.exp (-α*N*g) ≤ (2/(α*g))*Real.exp (-α*N*g/2) := by
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (mul_pos hα hg)).mpr
  have hh := linear_exponential_absorption (α*N*g)
  rw [show -(α*N*g)=-α*N*g by ring] at hh
  nlinarith only [hh]

/-- Absorb the linear copy-number prefactor in the safety ceiling. -/
theorem generation_exit_exponential (k α N H t a b core ceiling : ℝ)
    (hk : 0 ≤ k) (hα : 0 < α) (hN : 0 ≤ N) (hH : 0 ≤ H) (ht : 0 ≤ t)
    (hcore : core ≤ a) (hgap : a < b)
    (hceiling : ceiling ≤ (α*H*N/4)*Real.exp (α*N*core)) :
    k*(Real.exp (α*N*a)+t*ceiling)/Real.exp (α*N*b) ≤
      k*(1+t*H/(2*(b-a)))*Real.exp (-α*N*(b-a)/2) := by
  have hg : 0 < b-a := sub_pos.mpr hgap
  have hnorm : Real.exp (α*N*a)/Real.exp (α*N*b)=Real.exp (-α*N*(b-a)) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  have hceil : ceiling ≤ (α*H*N/4)*Real.exp (α*N*a) := hceiling.trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left hcore (mul_nonneg hα.le hN))) (by positivity))
  have hnoise : t*ceiling/Real.exp (α*N*b) ≤
      (t*α*H/4)*(N*Real.exp (-α*N*(b-a))) := by
    calc
      _ ≤ t*((α*H*N/4)*Real.exp (α*N*a))/Real.exp (α*N*b) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hceil ht) (Real.exp_pos _).le
      _ = (t*α*H/4)*N*(Real.exp (α*N*a)/Real.exp (α*N*b)) := by ring
      _ = _ := by rw [hnorm]; ring
  have hnoise' : t*ceiling/Real.exp (α*N*b) ≤
      (t*H/(2*(b-a)))*Real.exp (-α*N*(b-a)/2) := by
    have hh := mul_le_mul_of_nonneg_left (scaled_linear_exponential_absorption α N (b-a) hα hg)
      (show 0 ≤ t*α*H/4 by positivity)
    apply hnoise.trans
    convert hh using 1
    field_simp
    ring
  have hfirst : Real.exp (α*N*a)/Real.exp (α*N*b) ≤ Real.exp (-α*N*(b-a)/2) := by
    rw [hnorm]
    apply Real.exp_le_exp.mpr
    have hh : 0 ≤ α*N*(b-a) := by positivity
    linarith only [hh]
  have hh := mul_le_mul_of_nonneg_left (add_le_add hfirst hnoise') hk
  calc
    _ = k*(Real.exp (α*N*a)/Real.exp (α*N*b)+t*ceiling/Real.exp (α*N*b)) := by ring
    _ ≤ k*(Real.exp (-α*N*(b-a)/2)+(t*H/(2*(b-a)))*Real.exp (-α*N*(b-a)/2)) := hh
    _ = _ := by ring

end CompositionalMemory
