import Mathlib

namespace HeritableCompositions

/-- Birth-volume scaling of the energy observable preserves the source upper
generator inequality, since N/currentVolume is between zero and one. -/
theorem exp_scaled_increment (θ u : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    Real.exp (θ*u)-1 ≤ θ*(Real.exp u-1) := by
  have h := convexOn_exp.2 (Set.mem_univ u) (Set.mem_univ (0 : ℝ))
    hθ (sub_nonneg.mpr hθ1) (by ring : θ+(1-θ)=1)
  simp only [smul_eq_mul, mul_zero, add_zero, Real.exp_zero, mul_one] at h
  linarith only [h]

theorem scaled_generator_sum {ι : Type*} [Fintype ι]
    (a u : ι → ℝ) (θ b : ℝ) (ha : ∀ r, 0 ≤ a r)
    (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hbound : ∑ r, a r*(Real.exp (u r)-1) ≤ b) :
    ∑ r, a r*(Real.exp (θ*u r)-1) ≤ θ*b := by
  calc
    ∑ r, a r*(Real.exp (θ*u r)-1) ≤
        ∑ r, θ*(a r*(Real.exp (u r)-1)) := by
      apply Finset.sum_le_sum
      intro r _
      have h := mul_le_mul_of_nonneg_left (exp_scaled_increment θ (u r) hθ hθ1) (ha r)
      nlinarith only [h]
    _ = θ*(∑ r, a r*(Real.exp (u r)-1)) := (Finset.mul_sum ..).symm
    _ ≤ θ*b := mul_le_mul_of_nonneg_left hbound hθ

theorem exp_two_scale_increment (n m a b : ℝ)
    (hn : 0 ≤ n) (hm : 0 < m) (hnm : n ≤ m) :
    Real.exp (n*b)-Real.exp (n*a) ≤
      (n/m)*Real.exp ((n-m)*a)*(Real.exp (m*b)-Real.exp (m*a)) := by
  have hθ : 0 ≤ n/m := div_nonneg hn hm.le
  have hθ1 : n/m ≤ 1 := (div_le_one hm).mpr hnm
  have h := exp_scaled_increment (n/m) (m*(b-a)) hθ hθ1
  have hid : (n/m)*(m*(b-a)) = n*(b-a) := by field_simp
  rw [hid] at h
  have hmul := mul_le_mul_of_nonneg_left h (Real.exp_pos (n*a)).le
  have he1 : Real.exp (n*b) = Real.exp (n*a)*Real.exp (n*(b-a)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have he2 : Real.exp (m*b) = Real.exp (m*a)*Real.exp (m*(b-a)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have he3 : Real.exp ((n-m)*a)*Real.exp (m*a) = Real.exp (n*a) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he1,he2]
  calc
    Real.exp (n*a)*Real.exp (n*(b-a))-Real.exp (n*a) ≤
      Real.exp (n*a)*((n/m)*(Real.exp (m*(b-a))-1)) := by nlinarith only [hmul]
    _ = (n/m)*Real.exp ((n-m)*a)*(Real.exp (m*a)*Real.exp (m*(b-a))-Real.exp (m*a)) := by
      rw [← he3]
      ring

end HeritableCompositions
