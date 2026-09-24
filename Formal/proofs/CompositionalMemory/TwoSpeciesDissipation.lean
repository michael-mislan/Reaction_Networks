import proofs.CompositionalMemory.TwoSpeciesBounds

namespace CompositionalMemory

theorem two_uniform_linear_decay (b : Bool) (y : TwoPoint) :
    2*twoQ b y (twoJacobian b y) ≤ -304*‖y‖^2 := by
  rw [two_linear_lyapunov]
  have hn := two_norm_sq_le y
  cases b <;> simp only [Bool.false_eq_true,if_false,if_true] <;>
    nlinarith only [hn,sq_nonneg (y 0),sq_nonneg (y 1)]

theorem two_nonlinear_lyapunov_bound (b : Bool) (y : TwoPoint) :
    2*twoQ b y (twoRemainder y) ≤ 700000*‖y‖^3 := by
  have hq := twoQ_operator b y (twoRemainder y)
  have hr := two_remainder_bound y
  have hh := mul_le_mul_of_nonneg_left hr (show 0 ≤ 100000*‖y‖ by positivity)
  nlinarith only [le_abs_self (twoQ b y (twoRemainder y)),hq,hh]

/-- A common strict recovery bound on both wells of the two-species application. -/
theorem two_local_dissipation (b : Bool) (y : TwoPoint) (hr : ‖y‖ ≤ 1/10000) :
    2*twoQ b y (twoField (twoCenter b+y)) ≤ -200*‖y‖^2 := by
  rw [two_field_expansion,map_add]
  have hl := two_uniform_linear_decay b y
  have hn := two_nonlinear_lyapunov_bound b y
  have hs : ‖y‖^3 ≤ (1/10000)*‖y‖^2 := by
    nlinarith only [mul_le_mul_of_nonneg_right hr (sq_nonneg ‖y‖)]
  nlinarith only [hl,hn,hs,sq_nonneg ‖y‖]

end CompositionalMemory
