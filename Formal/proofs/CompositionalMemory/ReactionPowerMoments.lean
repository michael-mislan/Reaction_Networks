import proofs.CompositionalMemory.BilinearJumpBounds
import proofs.CompositionalMemory.SixthPowerDrift

namespace CompositionalMemory

/-- Lift the unclipped channel increments before combining them with the
inventory energy. This avoids assigning a fictitious small quadratic jump
to an absorbing exhausted state. -/
theorem raw_channel_sixth_bound {ι : Type*} [Fintype ι]
    (rate delta : ι → ℝ) (D dD d drift variance : ℝ)
    (hrate : ∀ r,0 ≤ rate r) (hD : 0 ≤ D) (hd : 0 ≤ d)
    (hjump : ∀ r,|delta r| ≤ d) (hfirst : dD+∑ r,rate r*delta r ≤ drift)
    (hsecond : ∑ r,rate r*(delta r)^2 ≤ variance) :
    6*D^5*dD+(∑ r,rate r*((D+delta r)^6-D^6)) ≤
      6*D^5*drift+sixthRemainderCoefficient D d*variance := by
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun r _ =>
    mul_le_mul_of_nonneg_left (sixth_increment_upper D (delta r) d hD (hjump r)) (hrate r))
  have he : (∑ r,rate r*(6*D^5*delta r+sixthRemainderCoefficient D d*(delta r)^2))=
      6*D^5*(∑ r,rate r*delta r)+sixthRemainderCoefficient D d*(∑ r,rate r*(delta r)^2) := by
    simp only [Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro r _
    ring
  rw [he] at hs
  have hc : 0 ≤ sixthRemainderCoefficient D d := by unfold sixthRemainderCoefficient; positivity
  have h1 := mul_le_mul_of_nonneg_left hfirst (show 0 ≤ 6*D^5 by positivity)
  have h2 := mul_le_mul_of_nonneg_left hsecond hc
  nlinarith only [hs,h1,h2]

theorem bilinear_reaction_jump_bounds {V ι : Type*} [AddCommGroup V] [Module ℝ V] [Fintype ι]
    (Q : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hsym : ∀ x y,Q x y=Q y x) (hpos : ∀ x,0 ≤ Q x x)
    (y : V) (jump : ι → V) (a : ι → ℝ) (volume x h b : ℝ)
    (hv : 0 < volume) (hx : 0 ≤ x) (hh : 0 ≤ h) (hD : Q y y=x^2)
    (ha : ∀ r,0 ≤ a r) (hH : ∀ r,Q (jump r) (jump r) ≤ h^2)
    (hnoise : ∑ r,a r*Q (jump r) (jump r) ≤ b) :
    (∀ r,|Q (y+(1/volume) • jump r) (y+(1/volume) • jump r)-Q y y| ≤
      h*(2*x/volume+h/volume^2)) ∧
    (∑ r,volume*a r*(Q (y+(1/volume) • jump r) (y+(1/volume) • jump r)-Q y y)^2) ≤
      volume*b*(2*x/volume+h/volume^2)^2 := by
  let tau := 2*x/volume+h/volume^2
  have htau : 0 ≤ tau := by dsimp [tau]; positivity
  have hs (r : ι) :
      (Q (y+(1/volume) • jump r) (y+(1/volume) • jump r)-Q y y)^2 ≤
        Q (jump r) (jump r)*tau^2 := by
    rw [scaled_bilinear_energy_increment Q hsym]
    have hc := bilinear_cauchy_sq Q hsym hpos y (jump r)
    rw [hD] at hc
    exact quadratic_increment_squared_bound _ _ x h volume (hpos _) hx hh hv hc (hH r)
  constructor
  · intro r
    have hb := (hs r).trans (mul_le_mul_of_nonneg_right (hH r) (sq_nonneg tau))
    apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hh htau)).mp
    simpa only [sq_abs,mul_pow] using hb
  · have hsum := Finset.sum_le_sum (s := Finset.univ) (fun r _ =>
      mul_le_mul_of_nonneg_left (hs r) (mul_nonneg hv.le (ha r)))
    have he : (∑ r,volume*a r*(Q (jump r) (jump r)*tau^2))=
        volume*(∑ r,a r*Q (jump r) (jump r))*tau^2 := by
      simp only [Finset.mul_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro r _
      ring
    rw [he] at hsum
    exact hsum.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hnoise hv.le) (sq_nonneg tau))

end CompositionalMemory
