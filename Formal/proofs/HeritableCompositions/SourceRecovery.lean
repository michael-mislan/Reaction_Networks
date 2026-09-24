import proofs.FiniteCopy.LocalDissipation
import proofs.HeritableCompositions.GrowthDrift
import proofs.HeritableCompositions.RecoveryBudget

namespace HeritableCompositions
open FiniteCopy CoreCouplingCAC Set

theorem bilinear_term_bound (c a b r : ℝ) (hr : 0 ≤ r)
    (ha : |a| ≤ r) (hb : |b| ≤ 36) : c*a*b ≤ |c| *36*r := by
  calc
    c*a*b ≤ |c*a*b| := le_abs_self _
    _ = |c| *(|a| *|b|) := by rw [abs_mul, abs_mul]; ring
    _ ≤ |c| *(r*36) := mul_le_mul_of_nonneg_left
      (mul_le_mul ha hb (abs_nonneg _) hr) (abs_nonneg _)
    _ = |c| *36*r := by ring

theorem low_pair_box_bound (y v : Point) (r : ℝ) (hr : 0 ≤ r)
    (hy : ∀ i, |y i| ≤ r) (hv : ∀ i, |v i| ≤ 36) :
    |lowPair y v| ≤ 7200*r := by
  apply abs_le.mpr
  constructor

  · have t0 := bilinear_term_bound (-1115801/1000000 : ℝ) (y 0) (v 0) r hr (hy 0) (hv 0)

    have t1 := bilinear_term_bound (153427/250000 : ℝ) (y 0) (v 1) r hr (hy 0) (hv 1)

    have t2 := bilinear_term_bound (-2346047/1000000 : ℝ) (y 0) (v 2) r hr (hy 0) (hv 2)

    have t3 := bilinear_term_bound (-688977/200000 : ℝ) (y 0) (v 3) r hr (hy 0) (hv 3)

    have t4 := bilinear_term_bound (153427/250000 : ℝ) (y 1) (v 0) r hr (hy 1) (hv 0)

    have t5 := bilinear_term_bound (-1111499/1000000 : ℝ) (y 1) (v 1) r hr (hy 1) (hv 1)

    have t6 := bilinear_term_bound (2339313/1000000 : ℝ) (y 1) (v 2) r hr (hy 1) (hv 2)

    have t7 := bilinear_term_bound (214649/62500 : ℝ) (y 1) (v 3) r hr (hy 1) (hv 3)

    have t8 := bilinear_term_bound (-2346047/1000000 : ℝ) (y 2) (v 0) r hr (hy 2) (hv 0)

    have t9 := bilinear_term_bound (2339313/1000000 : ℝ) (y 2) (v 1) r hr (hy 2) (hv 1)

    have t10 := bilinear_term_bound (-6767757/1000000 : ℝ) (y 2) (v 2) r hr (hy 2) (hv 2)

    have t11 := bilinear_term_bound (-5089403/500000 : ℝ) (y 2) (v 3) r hr (hy 2) (hv 3)

    have t12 := bilinear_term_bound (-688977/200000 : ℝ) (y 3) (v 0) r hr (hy 3) (hv 0)

    have t13 := bilinear_term_bound (214649/62500 : ℝ) (y 3) (v 1) r hr (hy 3) (hv 1)

    have t14 := bilinear_term_bound (-5089403/500000 : ℝ) (y 3) (v 2) r hr (hy 3) (hv 2)

    have t15 := bilinear_term_bound (-15517433/1000000 : ℝ) (y 3) (v 3) r hr (hy 3) (hv 3)

    norm_num only [abs_of_pos, abs_of_neg] at t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15

    unfold lowPair
    linarith only [hr, t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15]

  · have t0 := bilinear_term_bound (1115801/1000000 : ℝ) (y 0) (v 0) r hr (hy 0) (hv 0)

    have t1 := bilinear_term_bound (-153427/250000 : ℝ) (y 0) (v 1) r hr (hy 0) (hv 1)

    have t2 := bilinear_term_bound (2346047/1000000 : ℝ) (y 0) (v 2) r hr (hy 0) (hv 2)

    have t3 := bilinear_term_bound (688977/200000 : ℝ) (y 0) (v 3) r hr (hy 0) (hv 3)

    have t4 := bilinear_term_bound (-153427/250000 : ℝ) (y 1) (v 0) r hr (hy 1) (hv 0)

    have t5 := bilinear_term_bound (1111499/1000000 : ℝ) (y 1) (v 1) r hr (hy 1) (hv 1)

    have t6 := bilinear_term_bound (-2339313/1000000 : ℝ) (y 1) (v 2) r hr (hy 1) (hv 2)

    have t7 := bilinear_term_bound (-214649/62500 : ℝ) (y 1) (v 3) r hr (hy 1) (hv 3)

    have t8 := bilinear_term_bound (2346047/1000000 : ℝ) (y 2) (v 0) r hr (hy 2) (hv 0)

    have t9 := bilinear_term_bound (-2339313/1000000 : ℝ) (y 2) (v 1) r hr (hy 2) (hv 1)

    have t10 := bilinear_term_bound (6767757/1000000 : ℝ) (y 2) (v 2) r hr (hy 2) (hv 2)

    have t11 := bilinear_term_bound (5089403/500000 : ℝ) (y 2) (v 3) r hr (hy 2) (hv 3)

    have t12 := bilinear_term_bound (688977/200000 : ℝ) (y 3) (v 0) r hr (hy 3) (hv 0)

    have t13 := bilinear_term_bound (-214649/62500 : ℝ) (y 3) (v 1) r hr (hy 3) (hv 1)

    have t14 := bilinear_term_bound (5089403/500000 : ℝ) (y 3) (v 2) r hr (hy 3) (hv 2)

    have t15 := bilinear_term_bound (15517433/1000000 : ℝ) (y 3) (v 3) r hr (hy 3) (hv 3)

    norm_num only [abs_of_pos, abs_of_neg] at t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15

    unfold lowPair
    linarith only [hr, t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15]


theorem low_growth_perturbation (γ r : ℝ) (y x : Point)
    (hγ : 0 ≤ γ) (hr : 0 ≤ r) (hz : 0 ≤ x 2 ∧ x 2 ≤ 4)
    (hy : ∀ i, |y i| ≤ r) (hv : ∀ i, |x i+membraneDirection i| ≤ 36) :
    2*lowPair y (growthField γ x) ≤
      2*lowPair y (drift (1/100000) 0 x)+60000*γ*r := by
  have hp := low_pair_box_bound y (fun i => x i+membraneDirection i) r hr hy hv
  have ht : -(2*γ*x 2)*lowPair y (fun i => x i+membraneDirection i) ≤ 60000*γ*r := by
    have h := mul_le_mul_of_nonneg_left (abs_le.mp hp).1
      (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hγ) hz.1)
    have hz' := mul_le_mul_of_nonneg_right hz.2 (mul_nonneg hγ hr)
    nlinarith only [h, hz', mul_nonneg hγ hr]
  have hid : 2*lowPair y (growthField γ x) =
      2*lowPair y (drift (1/100000) 0 x) -
      (2*γ*x 2)*lowPair y (fun i => x i+membraneDirection i) := by
    unfold lowPair growthField
    ring
  linarith only [ht, hid]

theorem high_pair_box_bound (y v : Point) (r : ℝ) (hr : 0 ≤ r)
    (hy : ∀ i, |y i| ≤ r) (hv : ∀ i, |v i| ≤ 36) :
    |highPair y v| ≤ 7200*r := by
  apply abs_le.mpr
  constructor

  · have t0 := bilinear_term_bound (-211521/250000 : ℝ) (y 0) (v 0) r hr (hy 0) (hv 0)

    have t1 := bilinear_term_bound (115949/100000 : ℝ) (y 0) (v 1) r hr (hy 0) (hv 1)

    have t2 := bilinear_term_bound (-2352853/1000000 : ℝ) (y 0) (v 2) r hr (hy 0) (hv 2)

    have t3 := bilinear_term_bound (-1755029/500000 : ℝ) (y 0) (v 3) r hr (hy 0) (hv 3)

    have t4 := bilinear_term_bound (115949/100000 : ℝ) (y 1) (v 0) r hr (hy 1) (hv 0)

    have t5 := bilinear_term_bound (-1083497/250000 : ℝ) (y 1) (v 1) r hr (hy 1) (hv 1)

    have t6 := bilinear_term_bound (6781643/1000000 : ℝ) (y 1) (v 2) r hr (hy 1) (hv 2)

    have t7 := bilinear_term_bound (2558257/250000 : ℝ) (y 1) (v 3) r hr (hy 1) (hv 3)

    have t8 := bilinear_term_bound (-2352853/1000000 : ℝ) (y 2) (v 0) r hr (hy 2) (hv 0)

    have t9 := bilinear_term_bound (6781643/1000000 : ℝ) (y 2) (v 1) r hr (hy 2) (hv 1)

    have t10 := bilinear_term_bound (-11398763/1000000 : ℝ) (y 2) (v 2) r hr (hy 2) (hv 2)

    have t11 := bilinear_term_bound (-4305569/250000 : ℝ) (y 2) (v 3) r hr (hy 2) (hv 3)

    have t12 := bilinear_term_bound (-1755029/500000 : ℝ) (y 3) (v 0) r hr (hy 3) (hv 0)

    have t13 := bilinear_term_bound (2558257/250000 : ℝ) (y 3) (v 1) r hr (hy 3) (hv 1)

    have t14 := bilinear_term_bound (-4305569/250000 : ℝ) (y 3) (v 2) r hr (hy 3) (hv 2)

    have t15 := bilinear_term_bound (-26082111/1000000 : ℝ) (y 3) (v 3) r hr (hy 3) (hv 3)

    norm_num only [abs_of_pos, abs_of_neg] at t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15

    unfold highPair
    linarith only [hr, t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15]

  · have t0 := bilinear_term_bound (211521/250000 : ℝ) (y 0) (v 0) r hr (hy 0) (hv 0)

    have t1 := bilinear_term_bound (-115949/100000 : ℝ) (y 0) (v 1) r hr (hy 0) (hv 1)

    have t2 := bilinear_term_bound (2352853/1000000 : ℝ) (y 0) (v 2) r hr (hy 0) (hv 2)

    have t3 := bilinear_term_bound (1755029/500000 : ℝ) (y 0) (v 3) r hr (hy 0) (hv 3)

    have t4 := bilinear_term_bound (-115949/100000 : ℝ) (y 1) (v 0) r hr (hy 1) (hv 0)

    have t5 := bilinear_term_bound (1083497/250000 : ℝ) (y 1) (v 1) r hr (hy 1) (hv 1)

    have t6 := bilinear_term_bound (-6781643/1000000 : ℝ) (y 1) (v 2) r hr (hy 1) (hv 2)

    have t7 := bilinear_term_bound (-2558257/250000 : ℝ) (y 1) (v 3) r hr (hy 1) (hv 3)

    have t8 := bilinear_term_bound (2352853/1000000 : ℝ) (y 2) (v 0) r hr (hy 2) (hv 0)

    have t9 := bilinear_term_bound (-6781643/1000000 : ℝ) (y 2) (v 1) r hr (hy 2) (hv 1)

    have t10 := bilinear_term_bound (11398763/1000000 : ℝ) (y 2) (v 2) r hr (hy 2) (hv 2)

    have t11 := bilinear_term_bound (4305569/250000 : ℝ) (y 2) (v 3) r hr (hy 2) (hv 3)

    have t12 := bilinear_term_bound (1755029/500000 : ℝ) (y 3) (v 0) r hr (hy 3) (hv 0)

    have t13 := bilinear_term_bound (-2558257/250000 : ℝ) (y 3) (v 1) r hr (hy 3) (hv 1)

    have t14 := bilinear_term_bound (4305569/250000 : ℝ) (y 3) (v 2) r hr (hy 3) (hv 2)

    have t15 := bilinear_term_bound (26082111/1000000 : ℝ) (y 3) (v 3) r hr (hy 3) (hv 3)

    norm_num only [abs_of_pos, abs_of_neg] at t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15

    unfold highPair
    linarith only [hr, t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15]


theorem high_growth_perturbation (γ r : ℝ) (y x : Point)
    (hγ : 0 ≤ γ) (hr : 0 ≤ r) (hz : 0 ≤ x 2 ∧ x 2 ≤ 4)
    (hy : ∀ i, |y i| ≤ r) (hv : ∀ i, |x i+membraneDirection i| ≤ 36) :
    2*highPair y (growthField γ x) ≤
      2*highPair y (drift (1/100000) 0 x)+60000*γ*r := by
  have hp := high_pair_box_bound y (fun i => x i+membraneDirection i) r hr hy hv
  have ht : -(2*γ*x 2)*highPair y (fun i => x i+membraneDirection i) ≤ 60000*γ*r := by
    have h := mul_le_mul_of_nonneg_left (abs_le.mp hp).1
      (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hγ) hz.1)
    have hz' := mul_le_mul_of_nonneg_right hz.2 (mul_nonneg hγ hr)
    nlinarith only [h, hz', mul_nonneg hγ hr]
  have hid : 2*highPair y (growthField γ x) =
      2*highPair y (drift (1/100000) 0 x) -
      (2*γ*x 2)*highPair y (fun i => x i+membraneDirection i) := by
    unfold highPair growthField
    ring
  linarith only [ht, hid]


end HeritableCompositions
