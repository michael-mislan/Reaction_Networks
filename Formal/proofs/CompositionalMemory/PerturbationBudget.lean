import proofs.CompositionalMemory.ExponentialMoments

namespace CompositionalMemory

/-- Uniform perturbation budget; V controls total jump variance, including both
directions of exchange. The resident negative term is supplied separately. -/
theorem perturbation_moment_budget {ι : Type*} [Fintype ι]
    (rate δ : ι → ℝ) (N r f V : ℝ)
    (hN : 1 ≤ N) (hV : 0 ≤ V) (hVmax : V ≤ 1/1000000)
    (hrate : ∀ j, 0 ≤ rate j)
    (hsmall : ∀ j, |(1/1000000000000 : ℝ)*N*δ j| ≤ 1)
    (hdrift : ∑ j, rate j*δ j ≤ f*r+42*V/N)
    (hvariance : ∑ j, rate j*(δ j)^2 ≤
      14112*V*r^2/N+3528*5041*V/N^3) :
    ∑ j, rate j*(Real.exp ((1/1000000000000 : ℝ)*N*δ j)-1) ≤
      (1/1000000000000 : ℝ)*(N*r^2/4+2*N*f^2+1) := by
  let a : ℝ := 1/1000000000000
  have hNp : 0 < N := by linarith only [hN]
  have ha : 0 ≤ a := by norm_num [a]
  have hbase := exponential_sum_le_two_moments rate δ (a*N) hrate hsmall
  have hd := mul_le_mul_of_nonneg_left hdrift (mul_nonneg ha hNp.le)
  have hv := mul_le_mul_of_nonneg_left hvariance (sq_nonneg (a*N))
  have hid : a*N*(f*r+42*V/N)+(a*N)^2*
      (14112*V*r^2/N+3528*5041*V/N^3) =
      a*(N*f*r+42*V+a*14112*V*N*r^2+a*3528*5041*V/N) := by
    field_simp
    ring
  have hy : f*r ≤ r^2/8+2*f^2 := by nlinarith only [sq_nonneg (r-4*f)]
  have hyn := mul_le_mul_of_nonneg_left hy hNp.le
  have hab : a*14112*V ≤ 1/8 := by dsimp [a]; linarith only [hVmax]
  have hb := mul_le_mul_of_nonneg_right hab (mul_nonneg hNp.le (sq_nonneg r))
  have hdiv : V/N ≤ V := (div_le_iff₀ hNp).mpr (by nlinarith only [mul_nonneg hV (sub_nonneg.mpr hN)])
  have hc : 42*V+a*3528*5041*V/N ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left hdiv (show 0 ≤ a*3528*5041 by positivity)
    dsimp [a] at h ⊢
    simp only [div_eq_mul_inv] at h ⊢
    linarith only [h,hVmax]
  have hinner : N*f*r+42*V+a*14112*V*N*r^2+a*3528*5041*V/N ≤
      N*r^2/4+2*N*f^2+1 := by nlinarith only [hyn,hb,hc]
  calc
    _ ≤ a*N*(∑ j, rate j*δ j)+(a*N)^2*(∑ j, rate j*(δ j)^2) := hbase
    _ ≤ a*N*(f*r+42*V/N)+(a*N)^2*
        (14112*V*r^2/N+3528*5041*V/N^3) := add_le_add hd hv
    _ = _ := hid
    _ ≤ _ := mul_le_mul_of_nonneg_left hinner ha

theorem incident_noise_budget (γ κ : ℝ)
    (hγ : γ ≤ 1/100000000000) (hκ : κ ≤ 1/100000000000) :
    20164*γ+8*κ ≤ (1/1000000 : ℝ) := by linarith only [hγ,hκ]

end CompositionalMemory
