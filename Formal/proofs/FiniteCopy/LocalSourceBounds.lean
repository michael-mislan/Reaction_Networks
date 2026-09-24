import proofs.FiniteCopy.LocalDissipation
import proofs.FiniteCopy.JumpNoise

namespace FiniteCopy

theorem normSq_small (y : Point) (hy : ∀ i, |y i| ≤ 1/400) : normSq y ≤ 1/40000 := by
  have h0 := abs_le.mp (hy 0)
  have h1 := abs_le.mp (hy 1)
  have h2 := abs_le.mp (hy 2)
  have h3 := abs_le.mp (hy 3)
  unfold normSq
  nlinarith [h0.1,h0.2,h1.1,h1.2,h2.1,h2.2,h3.1,h3.2]

theorem local_rate_upper (x : Point) (q : ℝ) (hq : 0 ≤ q)
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 35) (r : Fin 13) :
    densityRates (1/100000) q x r ≤ 10000 := by
  have h0 := hx 0
  have h1 := hx 1
  have h2 := hx 2
  have h3 := hx 3
  have h12 : x 1*x 2 ≤ 1225 := by nlinarith [mul_nonneg (sub_nonneg.mpr h1.2) h2.1]
  have hq0 := mul_nonneg hq h0.1
  have hq2 := mul_nonneg hq h2.1
  have h00 : (x 0)^2 ≤ 1225 := by nlinarith
  have h22 : (x 2)^2 ≤ 1225 := by nlinarith
  fin_cases r <;> norm_num [densityRates] <;> nlinarith only [h0.1,h0.2,h1.1,h1.2,h2.1,h2.2,h3.1,h3.2,h12,hq0,hq2,h00,h22]

theorem local_rate_sum_upper (x : Point) (q : ℝ) (hq : 0 ≤ q)
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 35) :
    ∑ r, densityRates (1/100000) q x r ≤ 200000 := by
  have h := Finset.sum_le_sum (fun r (_ : r ∈ Finset.univ) => local_rate_upper x q hq hx r)
  norm_num at h
  linarith only [h]

noncomputable def sourceCorrection (x : Point) : Point :=
  ![2/100000*x 0,-1/100000*x 0,4*x 2,-2*x 2]

theorem bounded_bilinear_term (u v c : ℝ) (hu : |u| ≤ 1/400) (hv : |v| ≤ 35) :
    c*u*v ≤ |c| * (35/400) := by
  have h := mul_le_mul hu hv (abs_nonneg v) (by norm_num : (0:ℝ) ≤ 1/400)
  have hh := mul_le_mul_of_nonneg_left h (abs_nonneg c)
  rw [← abs_mul,← mul_assoc,← abs_mul] at hh
  calc c*u*v ≤ |c*u*v| := le_abs_self _
       _ ≤ |c| * (35/400) := by convert hh using 1 <;> ring

theorem lowcorrection_bound (y x : Point)
    (hy : ∀ i, |y i| ≤ 1/400) (hx : ∀ i, |x i| ≤ 35) :
    2*lowPair y (sourceCorrection x) ≤ 10000 := by
  have t0 := bounded_bilinear_term (y 0) (x 0) (284531/5000000000 : ℝ) (hy 0) (hx 0)
  norm_num at t0
  have t1 := bounded_bilinear_term (y 1) (x 0) (-467783/10000000000 : ℝ) (hy 1) (hx 0)
  norm_num at t1
  have t2 := bounded_bilinear_term (y 2) (x 0) (7031407/50000000000 : ℝ) (hy 2) (hx 0)
  norm_num at t2
  have t3 := bounded_bilinear_term (y 3) (x 0) (5162077/25000000000 : ℝ) (hy 3) (hx 0)
  norm_num at t3
  have t4 := bounded_bilinear_term (y 0) (x 2) (1247209/250000 : ℝ) (hy 0) (hx 2)
  norm_num at t4
  have t5 := bounded_bilinear_term (y 1) (x 2) (-622121/125000 : ℝ) (hy 1) (hx 2)
  norm_num at t5
  have t6 := bounded_bilinear_term (y 2) (x 2) (839177/62500 : ℝ) (hy 2) (hx 2)
  norm_num at t6
  have t7 := bounded_bilinear_term (y 3) (x 2) (4840179/250000 : ℝ) (hy 3) (hx 2)
  norm_num at t7
  have hid : 2*lowPair y (sourceCorrection x) =
    (284531/5000000000 : ℝ)*y 0*x 0 + (-467783/10000000000 : ℝ)*y 1*x 0 + (7031407/50000000000 : ℝ)*y 2*x 0 + (5162077/25000000000 : ℝ)*y 3*x 0 + (1247209/250000 : ℝ)*y 0*x 2 + (-622121/125000 : ℝ)*y 1*x 2 + (839177/62500 : ℝ)*y 2*x 2 + (4840179/250000 : ℝ)*y 3*x 2 := by
    norm_num [lowPair,sourceCorrection,Matrix.cons_val_two,Matrix.cons_val_three]
    ring
  rw [hid]
  linarith only [t0,t1,t2,t3,t4,t5,t6,t7]

theorem lowpair_drift_sum (x y : Point) (q : ℝ) :
    (∑ r, densityRates (1/100000) q x r*(2*lowPair y (jump r))) =
      2*lowPair y (drift (1/100000) q x) := by
  norm_num [drift_formula,densityRates,lowPair,jump,Fin.sum_univ_succ,Matrix.cons_val_two,Matrix.cons_val_three]
  ring

theorem lowpair_correction_identity (x y : Point) (q : ℝ) :
    2*lowPair y (drift (1/100000) q x) =
      2*lowPair y (drift (1/100000) 0 x)+q*(2*lowPair y (sourceCorrection x)) := by
  norm_num [drift_formula,lowPair,sourceCorrection,Matrix.cons_val_two,Matrix.cons_val_three]
  ring

theorem highcorrection_bound (y x : Point)
    (hy : ∀ i, |y i| ≤ 1/400) (hx : ∀ i, |x i| ≤ 35) :
    2*highPair y (sourceCorrection x) ≤ 10000 := by
  have t0 := bounded_bilinear_term (y 0) (x 0) (1425829/25000000000 : ℝ) (hy 0) (hx 0)
  norm_num at t0
  have t1 := bounded_bilinear_term (y 1) (x 0) (-831621/6250000000 : ℝ) (hy 1) (hx 0)
  norm_num at t1
  have t2 := bounded_bilinear_term (y 2) (x 0) (11487349/50000000000 : ℝ) (hy 2) (hx 0)
  norm_num at t2
  have t3 := bounded_bilinear_term (y 3) (x 0) (2156643/6250000000 : ℝ) (hy 3) (hx 0)
  norm_num at t3
  have t4 := bounded_bilinear_term (y 0) (x 2) (74728/15625 : ℝ) (hy 0) (hx 2)
  norm_num at t4
  have t5 := bounded_bilinear_term (y 1) (x 2) (-1665129/125000 : ℝ) (hy 1) (hx 2)
  norm_num at t5
  have t6 := bounded_bilinear_term (y 2) (x 2) (22301/1000 : ℝ) (hy 2) (hx 2)
  norm_num at t6
  have t7 := bounded_bilinear_term (y 3) (x 2) (8362441/250000 : ℝ) (hy 3) (hx 2)
  norm_num at t7
  have hid : 2*highPair y (sourceCorrection x) =
    (1425829/25000000000 : ℝ)*y 0*x 0 + (-831621/6250000000 : ℝ)*y 1*x 0 + (11487349/50000000000 : ℝ)*y 2*x 0 + (2156643/6250000000 : ℝ)*y 3*x 0 + (74728/15625 : ℝ)*y 0*x 2 + (-1665129/125000 : ℝ)*y 1*x 2 + (22301/1000 : ℝ)*y 2*x 2 + (8362441/250000 : ℝ)*y 3*x 2 := by
    norm_num [highPair,sourceCorrection,Matrix.cons_val_two,Matrix.cons_val_three]
    ring
  rw [hid]
  linarith only [t0,t1,t2,t3,t4,t5,t6,t7]

theorem highpair_drift_sum (x y : Point) (q : ℝ) :
    (∑ r, densityRates (1/100000) q x r*(2*highPair y (jump r))) =
      2*highPair y (drift (1/100000) q x) := by
  norm_num [drift_formula,densityRates,highPair,jump,Fin.sum_univ_succ,Matrix.cons_val_two,Matrix.cons_val_three]
  ring

theorem highpair_correction_identity (x y : Point) (q : ℝ) :
    2*highPair y (drift (1/100000) q x) =
      2*highPair y (drift (1/100000) 0 x)+q*(2*highPair y (sourceCorrection x)) := by
  norm_num [drift_formula,highPair,sourceCorrection,Matrix.cons_val_two,Matrix.cons_val_three]
  ring

end FiniteCopy
