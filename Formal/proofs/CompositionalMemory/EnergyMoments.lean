import proofs.CompositionalMemory.ExponentialMoments

namespace CompositionalMemory

theorem energy_first_moment {ι : Type*} [Fintype ι]
    (rate δ d : ι → ℝ) (r D V N : ℝ)
    (hr : 0 ≤ r) (hrate : ∀ j, 0 ≤ rate j)
    (hδ : ∀ j, |δ j| ≤ 84*r*d j+42*(d j)^2)
    (hfirst : ∑ j, rate j*d j ≤ D)
    (hsecond : ∑ j, rate j*(d j)^2 ≤ V/N) :
    ∑ j, rate j*δ j ≤ (84*D)*r+42*V/N := by
  have hp (j) : rate j*δ j ≤ (84*r)*(rate j*d j)+42*(rate j*(d j)^2) := by
    have h := mul_le_mul_of_nonneg_left ((le_abs_self (δ j)).trans (hδ j)) (hrate j)
    nlinarith only [h]
  have hs := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hp j)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hs
  have h1 := mul_le_mul_of_nonneg_left hfirst (show 0 ≤ 84*r by positivity)
  have h2 := mul_le_mul_of_nonneg_left hsecond (by norm_num : (0:ℝ) ≤ 42)
  simp only [div_eq_mul_inv] at h2 ⊢
  nlinarith only [hs,h1,h2]

theorem quadratic_increment_square (δ r d : ℝ)
    (hδ : |δ| ≤ 84*r*d+42*d^2) :
    δ^2 ≤ 14112*r^2*d^2+3528*d^4 := by
  have h : δ^2 ≤ (84*r*d+42*d^2)^2 := by
    simpa only [← pow_two, sq_abs] using mul_self_le_mul_self (abs_nonneg δ) hδ
  nlinarith only [h,sq_nonneg (84*r*d-42*d^2)]

/-- A local energy jump second moment derived from coordinate jump sizes. -/
theorem energy_second_moment {ι : Type*} [Fintype ι]
    (rate δ d : ι → ℝ) (N r V D : ℝ)
    (hN : 0 < N) (hrate : ∀ j, 0 ≤ rate j)
    (hδ : ∀ j, |δ j| ≤ 84*r*d j+42*(d j)^2)
    (hjump : ∀ j, (d j)^2 ≤ D^2/N^2)
    (hmoment : ∑ j, rate j*(d j)^2 ≤ V/N) :
    ∑ j, rate j*(δ j)^2 ≤ 14112*V*r^2/N+3528*D^2*V/N^3 := by
  let c := 14112*r^2+3528*D^2/N^2
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hpoint (j) : rate j*(δ j)^2 ≤ c*(rate j*(d j)^2) := by
    have hq := quadratic_increment_square (δ j) r (d j) (hδ j)
    have hd := mul_le_mul_of_nonneg_right (hjump j) (sq_nonneg (d j))
    have hupper : (δ j)^2 ≤ c*(d j)^2 := by
      dsimp [c]
      simp only [div_eq_mul_inv] at hd ⊢
      nlinarith only [hq,hd]
    have h := mul_le_mul_of_nonneg_left hupper (hrate j)
    nlinarith only [h]
  calc
    _ ≤ ∑ j, c*(rate j*(d j)^2) := Finset.sum_le_sum (fun j _ => hpoint j)
    _ = c*(∑ j, rate j*(d j)^2) := (Finset.mul_sum ..).symm
    _ ≤ c*(V/N) := mul_le_mul_of_nonneg_left hmoment hc
    _ = _ := by
      dsimp [c]
      field_simp

end CompositionalMemory
