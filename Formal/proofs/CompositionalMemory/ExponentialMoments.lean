import Mathlib.Analysis.Complex.Exponential
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option maxHeartbeats 60000

namespace CompositionalMemory

theorem exponential_sum_le_two_moments {ι : Type*} [Fintype ι]
    (rate δ : ι → ℝ) (a : ℝ) (hrate : ∀ j, 0 ≤ rate j)
    (hsmall : ∀ j, |a*δ j| ≤ 1) :
    ∑ j, rate j*(Real.exp (a*δ j)-1) ≤
      a*(∑ j, rate j*δ j)+a^2*(∑ j, rate j*(δ j)^2) := by
  have hpoint (j) : rate j*(Real.exp (a*δ j)-1) ≤
      a*(rate j*δ j)+a^2*(rate j*(δ j)^2) := by
    have h := mul_le_mul_of_nonneg_left
      (abs_le.mp (Real.abs_exp_sub_one_sub_id_le (hsmall j))).2 (hrate j)
    nlinarith only [h]
  have hs := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hpoint j)
  rwa [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hs

/-- A local jump-generator bound from actual energy increments and moments.
No transition probability or inheritance conclusion is assumed. -/
theorem exponential_generator_of_moments {ι : Type*} [Fintype ι]
    (rate delta : ι → ℝ) (α N r f K B C : ℝ)
    (ha : 0 ≤ α) (hN : 0 < N)
    (hrate : ∀ j, 0 ≤ rate j)
    (hsmall : ∀ j, |α*N*delta j| ≤ 1)
    (hdrift : ∑ j, rate j*delta j ≤ -(59/100 : ℝ)*r^2+f*r+K/N)
    (hvariance : ∑ j, rate j*(delta j)^2 ≤ B*r^2/N+C/N^3)
    (habsorb : α*B ≤ 9/100) :
    ∑ j, rate j*(Real.exp (α*N*delta j)-1) ≤
      α*(-N*r^2/4+K+α*C/N+N*f^2) := by
  have hstep (j) : rate j*(Real.exp (α*N*delta j)-1) ≤
      α*N*(rate j*delta j)+(α*N)^2*(rate j*(delta j)^2) := by
    have h := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le (hsmall j))).2
    have hh := mul_le_mul_of_nonneg_left h (hrate j)
    nlinarith only [hh]
  have hs := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hstep j)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hs
  have hd := mul_le_mul_of_nonneg_left hdrift (mul_nonneg ha hN.le)
  have hv := mul_le_mul_of_nonneg_left hvariance (sq_nonneg (α*N))
  have hzero : N ≠ 0 := ne_of_gt hN
  have hid : α*N*(-(59/100 : ℝ)*r^2+f*r+K/N)+
      (α*N)^2*(B*r^2/N+C/N^3) =
      α*(-(59/100 : ℝ)*N*r^2+N*f*r+K+α*B*N*r^2+α*C/N) := by
    field_simp [hzero]
    ring
  have hb := mul_le_mul_of_nonneg_right habsorb (mul_nonneg hN.le (sq_nonneg r))
  have hy : f*r ≤ r^2/4+f^2 := by nlinarith only [sq_nonneg (r/2-f)]
  have hyn := mul_le_mul_of_nonneg_left hy hN.le
  have hinner : -(59/100 : ℝ)*N*r^2+N*f*r+K+α*B*N*r^2+α*C/N ≤
      -N*r^2/4+K+α*C/N+N*f^2 := by nlinarith only [hb,hyn]
  have hlast := mul_le_mul_of_nonneg_left hinner ha
  calc
    _ ≤ α*N*(∑ j, rate j*delta j)+(α*N)^2*(∑ j, rate j*(delta j)^2) := hs
    _ ≤ α*N*(-(59/100 : ℝ)*r^2+f*r+K/N)+
        (α*N)^2*(B*r^2/N+C/N^3) := add_le_add hd hv
    _ = _ := hid
    _ ≤ _ := hlast

theorem uniform_remainder_constants :
    (1/1000000000000 : ℝ)*14112*1000001 ≤ 9/100 ∧
    (1/1000000000000 : ℝ)*3528*5041*1000001 ≤ 18 ∧
    (1/1000000000000 : ℝ)*(5964/400+211722) ≤ 1 ∧
    (23856 : ℝ)^2 ≤ 600000000 := by norm_num

end CompositionalMemory
