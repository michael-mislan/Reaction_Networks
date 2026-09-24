import Mathlib

noncomputable section
namespace OverlappingSiphonInvasion

theorem resident_entropy_identity (s u se ue α μ₀ : ℝ) (hs : s ≠ 0) (hu : u ≠ 0) :
    (1-se/s)*(-(μ₀+α*ue)*(s-se)-α*s*(u-ue))+
      (1-ue/u)*(α*u*(s-se)) = -(μ₀+α*ue)/s*(s-se)^2 := by
  field_simp
  ring

theorem resident_cross_identity (s u se ue α K : ℝ) :
    (-K*(s-se)-α*s*(u-ue))*(u-ue)+(s-se)*(α*u*(s-se)) =
      -α*s*(u-ue)^2-K*(s-se)*(u-ue)+α*u*(s-se)^2 := by ring

/-- A small cross term makes the resident entropy dissipate both variables.
The hypotheses require an upper box and a susceptible floor, but no infected
floor and no convergence assumption. -/
theorem resident_strict_drift (α K M l ε s u x y : ℝ)
    (hα : 0 < α) (hK : 0 < K) (hM : 0 < M) (hl : 0 < l) (hε : 0 < ε)
    (hls : l ≤ s) (hsM : s ≤ M) (huM : u ≤ M)
    (hε1 : ε*α*M ≤ K/(4*M)) (hε2 : ε*K*M ≤ α*l/2) :
    -(K/s-ε*α*u)*x^2-ε*K*x*y-ε*α*s*y^2 ≤
      -(K/(2*M))*x^2-(ε*α*l/2)*y^2 := by
  have hs : 0 < s := hl.trans_le hls
  have hb := mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_left hK.le hs hsM) (sq_nonneg x)
  have heu : ε*α*u ≤ K/(4*M) :=
    (mul_le_mul_of_nonneg_left huM (mul_pos hε hα).le).trans hε1
  have heux := mul_le_mul_of_nonneg_right heu (sq_nonneg x)
  have hel := mul_le_mul_of_nonneg_left hls (mul_pos hε hα).le
  have hely := mul_le_mul_of_nonneg_right hel (sq_nonneg y)
  have hsmall := mul_le_mul_of_nonneg_left hε2 hε.le
  have hsmally := mul_le_mul_of_nonneg_right hsmall (sq_nonneg y)
  have hsq := mul_nonneg (show 0 ≤ K/(4*M) by positivity)
    (sq_nonneg (x+2*ε*M*y))
  have hid : K/(4*M)*(x+2*ε*M*y)^2 =
      K/(4*M)*x^2+ε*K*x*y+ε^2*K*M*y^2 := by
    field_simp
    ring
  rw [hid] at hsq
  have hhalf : K/(2*M) = 2*(K/(4*M)) := by ring
  have hfull : K/M = 4*(K/(4*M)) := by ring
  rw [hfull] at hb
  rw [hhalf]
  nlinarith only [hb,heux,hely,hsmally,hsq]

end OverlappingSiphonInvasion
