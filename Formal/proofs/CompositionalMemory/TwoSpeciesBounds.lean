import proofs.CompositionalMemory.TwoSpeciesCore

namespace CompositionalMemory

theorem two_coordinate_abs_le (y : TwoPoint) (i : Fin 2) : |y i| ≤ ‖y‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg y)).mp le_rfl i

theorem two_norm_sq_le (y : TwoPoint) : ‖y‖^2 ≤ (y 0)^2+(y 1)^2 := by
  have hm : ‖y‖=max |y 0| |y 1| := by
    apply le_antisymm
    · apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
      intro i
      fin_cases i
      · exact le_max_left _ _
      · exact le_max_right _ _
    · exact max_le (two_coordinate_abs_le y 0) (two_coordinate_abs_le y 1)
  rw [hm]
  rcases le_total |y 0| |y 1| with h | h
  · rw [max_eq_right h, sq_abs]
    nlinarith only [sq_nonneg (y 0)]
  · rw [max_eq_left h, sq_abs]
    nlinarith only [sq_nonneg (y 1)]

theorem twoQ_coercive (b : Bool) (y : TwoPoint) : ‖y‖^2 ≤ twoQ b y y :=
  (two_norm_sq_le y).trans (two_quadratic_coercivity b y)

theorem two_bilinear_operator (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (y z : TwoPoint) :
    |a*y 0*z 0+b*(y 0*z 1+y 1*z 0)+c*y 1*z 1| ≤ (a+2*b+c)*‖y‖*‖z‖ := by
  have ht (v : ℝ) (hv : 0 ≤ v) (i j : Fin 2) : |v*y i*z j| ≤ v*‖y‖*‖z‖ := by
    rw [abs_mul,abs_mul,abs_of_nonneg hv]
    gcongr
    · exact two_coordinate_abs_le y i
    · exact two_coordinate_abs_le z j
  calc
    _ = |a*y 0*z 0+b*y 0*z 1+b*y 1*z 0+c*y 1*z 1| := by congr 1; ring
    _ ≤ |a*y 0*z 0|+|b*y 0*z 1|+|b*y 1*z 0|+|c*y 1*z 1| := by
      exact (abs_add_le _ _).trans (add_le_add
        ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
    _ ≤ a*‖y‖*‖z‖+b*‖y‖*‖z‖+b*‖y‖*‖z‖+c*‖y‖*‖z‖ :=
      add_le_add (add_le_add (add_le_add (ht a ha 0 0) (ht b hb 0 1)) (ht b hb 1 0)) (ht c hc 1 1)
    _ = _ := by ring

theorem twoQ_operator (b : Bool) (y z : TwoPoint) : |twoQ b y z| ≤ 50000*‖y‖*‖z‖ := by
  have hp := mul_nonneg (norm_nonneg y) (norm_nonneg z)
  cases b
  · have h := two_bilinear_operator 5292 10434 20929 (by norm_num) (by norm_num) (by norm_num) y z
    change |5292*y 0*z 0+10434*(y 0*z 1+y 1*z 0)+20929*y 1*z 1| ≤ _
    nlinarith only [h,hp]
  · have h := two_bilinear_operator 1732 2690 4187 (by norm_num) (by norm_num) (by norm_num) y z
    change |1732*y 0*z 0+2690*(y 0*z 1+y 1*z 0)+4187*y 1*z 1| ≤ _
    nlinarith only [h,hp]

theorem two_remainder_bound (y : TwoPoint) : ‖twoRemainder y‖ ≤ 7*‖y‖^2 := by
  have h₀ := two_coordinate_abs_le y 0
  have h₁ := two_coordinate_abs_le y 1
  have hs : (y 0)^2 ≤ ‖y‖^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (y 0)) (norm_nonneg y)).mpr h₀
  have hp : |y 0*y 1| ≤ ‖y‖^2 := by
    rw [abs_mul,pow_two]
    exact mul_le_mul h₀ h₁ (abs_nonneg _) (norm_nonneg _)
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  fin_cases i
  · change |-6*(y 0)^2-y 0*y 1/6| ≤ 7*‖y‖^2
    have ha := abs_add_le (-6*(y 0)^2) (-(y 0*y 1/6))
    have heq : |-6*(y 0)^2|=6*(y 0)^2 := by rw [abs_mul,abs_of_nonneg (sq_nonneg (y 0))]; norm_num
    have heq₂ : |-(y 0*y 1/6)|=|y 0*y 1|/6 := by simp only [abs_neg,abs_div]; norm_num
    rw [heq,heq₂] at ha
    have hh : |-6*(y 0)^2-y 0*y 1/6| ≤ 6*(y 0)^2+|y 0*y 1|/6 := by simpa only [sub_eq_add_neg] using ha
    nlinarith only [hh,hs,hp,sq_nonneg ‖y‖]
  · change |6*(y 0)^2| ≤ 7*‖y‖^2
    rw [abs_mul,abs_of_nonneg (sq_nonneg (y 0))]
    norm_num
    nlinarith only [hs,sq_nonneg ‖y‖]

end CompositionalMemory
