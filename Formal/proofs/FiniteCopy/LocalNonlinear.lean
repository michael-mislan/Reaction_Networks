import proofs.FiniteCopy.LocalLinear

namespace FiniteCopy

noncomputable def sourceRemainder (y : Point) : Point :=
  ![-2/100000*y 0^2+y 1*y 2,1/100000*y 0^2-y 1*y 2,
    -y 1*y 2-4*y 2^2,2*y 2^2]

theorem source_remainder_identity (s y : Point) :
    drift (1/100000) 0 (fun i => s i+y i) =
      fun i => drift (1/100000) 0 s i+sourceLinear (s 0) (s 1) (s 2) y i+sourceRemainder y i := by
  simp only [drift_formula]
  ext i
  fin_cases i <;> norm_num [sourceLinear,sourceRemainder,Matrix.cons_val_two,Matrix.cons_val_three] <;> ring

theorem cubic_term_bound (x : Point) (i j k : Fin 4) (c : ℝ)
    (hx : ∀ i, |x i| ≤ 1/400) :
    c*x i*x j*x k ≤ (|c| /400)*normSq x := by
  have hp : |x i*x j*x k| ≤ normSq x*(1/400) := by
    rw [abs_mul]
    exact mul_le_mul (abs_product_le_normSq x i j) (hx k) (abs_nonneg _) (normSq_nonneg x)
  calc
    c*x i*x j*x k ≤ |c*(x i*x j*x k)| := by ring_nf; exact le_abs_self _
    _ = |c| * |x i*x j*x k| := abs_mul _ _
    _ ≤ |c| * (normSq x*(1/400)) := mul_le_mul_of_nonneg_left hp (abs_nonneg c)
    _ = (|c| /400)*normSq x := by ring

theorem lowPair_add (x u v : Point) :
    lowPair x (fun i => u i+v i) = lowPair x u+lowPair x v := by
  unfold lowPair
  ring

theorem lowcubic_bound (x : Point) (hx : ∀ i, |x i| ≤ 1/400) :
    2*lowPair x (sourceRemainder x) ≤ (1/4)*normSq x := by
  have t0 := cubic_term_bound x 0 0 0 (-284531/5000000000 : ℝ) hx
  norm_num only [abs_of_pos,abs_of_neg] at t0
  have t1 := cubic_term_bound x 0 1 2 (-308269/250000 : ℝ) hx
  norm_num only [abs_of_pos,abs_of_neg] at t1
  have t2 := cubic_term_bound x 0 2 2 (-1247209/250000 : ℝ) hx
  norm_num only [abs_of_pos,abs_of_neg] at t2
  have t3 := cubic_term_bound x 0 0 1 (467783/10000000000 : ℝ) hx
  norm_num only [abs_of_pos,abs_of_neg] at t3
  have t4 := cubic_term_bound x 1 1 2 (307053/250000 : ℝ) hx
  norm_num only [abs_of_pos,abs_of_neg] at t4
  have t5 := cubic_term_bound x 1 2 2 (406087/500000 : ℝ) hx
  norm_num only [abs_of_pos,abs_of_neg] at t5
  have t6 := cubic_term_bound x 0 0 2 (-7031407/50000000000 : ℝ) hx
  norm_num only [abs_of_pos,abs_of_neg] at t6
  have t7 := cubic_term_bound x 2 2 2 (-839177/62500 : ℝ) hx
  norm_num only [abs_of_pos,abs_of_neg] at t7
  have t8 := cubic_term_bound x 0 0 3 (-5162077/25000000000 : ℝ) hx
  norm_num only [abs_of_pos,abs_of_neg] at t8
  have t9 := cubic_term_bound x 1 2 3 (-3299537/500000 : ℝ) hx
  norm_num only [abs_of_pos,abs_of_neg] at t9
  have t10 := cubic_term_bound x 2 2 3 (-4840179/250000 : ℝ) hx
  norm_num only [abs_of_pos,abs_of_neg] at t10
  have hid : 2*lowPair x (sourceRemainder x) =
    (-284531/5000000000 : ℝ)*x 0*x 0*x 0 + (-308269/250000 : ℝ)*x 0*x 1*x 2 + (-1247209/250000 : ℝ)*x 0*x 2*x 2 + (467783/10000000000 : ℝ)*x 0*x 0*x 1 + (307053/250000 : ℝ)*x 1*x 1*x 2 + (406087/500000 : ℝ)*x 1*x 2*x 2 + (-7031407/50000000000 : ℝ)*x 0*x 0*x 2 + (-839177/62500 : ℝ)*x 2*x 2*x 2 + (-5162077/25000000000 : ℝ)*x 0*x 0*x 3 + (-3299537/500000 : ℝ)*x 1*x 2*x 3 + (-4840179/250000 : ℝ)*x 2*x 2*x 3 := by
    norm_num [lowPair,sourceRemainder,Matrix.cons_val_two,Matrix.cons_val_three]
    ring
  rw [hid]
  nlinarith only [normSq_nonneg x,t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10]

theorem highPair_add (x u v : Point) :
    highPair x (fun i => u i+v i) = highPair x u+highPair x v := by
  unfold highPair
  ring

theorem highcubic_bound (x : Point) (hx : ∀ i, |x i| ≤ 1/400) :
    2*highPair x (sourceRemainder x) ≤ (1/4)*normSq x := by
  have t0 := cubic_term_bound x 0 0 0 (-1425829/25000000000 : ℝ) hx
  norm_num only [abs_of_pos,abs_of_neg] at t0
  have t1 := cubic_term_bound x 0 1 2 (-347279/500000 : ℝ) hx
  norm_num only [abs_of_pos,abs_of_neg] at t1
  have t2 := cubic_term_bound x 0 2 2 (-74728/15625 : ℝ) hx
  norm_num only [abs_of_pos,abs_of_neg] at t2
  have t3 := cubic_term_bound x 0 0 1 (831621/6250000000 : ℝ) hx
  norm_num only [abs_of_pos,abs_of_neg] at t3
  have t4 := cubic_term_bound x 1 1 2 (257633/100000 : ℝ) hx
  norm_num only [abs_of_pos,abs_of_neg] at t4
  have t5 := cubic_term_bound x 1 2 2 (4396249/500000 : ℝ) hx
  norm_num only [abs_of_pos,abs_of_neg] at t5
  have t6 := cubic_term_bound x 0 0 2 (-11487349/50000000000 : ℝ) hx
  norm_num only [abs_of_pos,abs_of_neg] at t6
  have t7 := cubic_term_bound x 2 2 2 (-22301/1000 : ℝ) hx
  norm_num only [abs_of_pos,abs_of_neg] at t7
  have t8 := cubic_term_bound x 0 0 3 (-2156643/6250000000 : ℝ) hx
  norm_num only [abs_of_pos,abs_of_neg] at t8
  have t9 := cubic_term_bound x 1 2 3 (-347919/50000 : ℝ) hx
  norm_num only [abs_of_pos,abs_of_neg] at t9
  have t10 := cubic_term_bound x 2 2 3 (-8362441/250000 : ℝ) hx
  norm_num only [abs_of_pos,abs_of_neg] at t10
  have hid : 2*highPair x (sourceRemainder x) =
    (-1425829/25000000000 : ℝ)*x 0*x 0*x 0 + (-347279/500000 : ℝ)*x 0*x 1*x 2 + (-74728/15625 : ℝ)*x 0*x 2*x 2 + (831621/6250000000 : ℝ)*x 0*x 0*x 1 + (257633/100000 : ℝ)*x 1*x 1*x 2 + (4396249/500000 : ℝ)*x 1*x 2*x 2 + (-11487349/50000000000 : ℝ)*x 0*x 0*x 2 + (-22301/1000 : ℝ)*x 2*x 2*x 2 + (-2156643/6250000000 : ℝ)*x 0*x 0*x 3 + (-347919/50000 : ℝ)*x 1*x 2*x 3 + (-8362441/250000 : ℝ)*x 2*x 2*x 3 := by
    norm_num [highPair,sourceRemainder,Matrix.cons_val_two,Matrix.cons_val_three]
    ring
  rw [hid]
  nlinarith only [normSq_nonneg x,t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10]

end FiniteCopy
