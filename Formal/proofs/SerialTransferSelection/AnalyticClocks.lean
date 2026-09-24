import proofs.FiniteCopy.Source

namespace SerialTransferSelection
open FiniteCopy

theorem density_clock_bound (x : Point) (q : ℝ) (hq : 0 ≤ q)
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 70) :
    (∑ r, densityRates (1/100000) q x r) ≤ 17000 := by
  have h0 := hx 0
  have h1 := hx 1
  have h2 := hx 2
  have h3 := hx 3
  have hp : x 1*x 2 ≤ (4900 : ℝ) := by nlinarith [mul_nonneg (sub_nonneg.mpr h1.2) h2.1]
  have ha : x 0*(x 0-q) ≤ (4900 : ℝ) := by
    have hs : (x 0)^2 ≤ (70 : ℝ)^2 := (sq_le_sq₀ h0.1 (by norm_num)).mpr h0.2
    nlinarith [mul_nonneg h0.1 hq]
  have hz : x 2*(x 2-q) ≤ (4900 : ℝ) := by
    have hs : (x 2)^2 ≤ (70 : ℝ)^2 := (sq_le_sq₀ h2.1 (by norm_num)).mpr h2.2
    nlinarith [mul_nonneg h2.1 hq]
  norm_num [densityRates,Fin.sum_univ_succ]
  nlinarith only [h0.2,h1.2,h2.2,h3.2,hp,ha,hz]

theorem cell_clock_bound (N m : ℝ) (hm : 0 ≤ m) (hmN : m ≤ 2*N)
    (x : Point) (q : ℝ) (hq : 0 ≤ q) (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 70) :
    m*(∑ r, densityRates (1/100000) q x r) ≤ 34000*N := by
  have h := mul_le_mul_of_nonneg_left (density_clock_bound x q hq hx) hm
  linarith only [h,hmN]

end SerialTransferSelection
