import Mathlib

namespace MultiConsumerPermanence

/-- Smooth reservoir storage; bounded on the eventual interval [0,2]. -/
noncomputable def reservoirPotential (R : ℝ) : ℝ := (R-1)^2/2

theorem reservoir_potential_bounds (R : ℝ) (hR : 0 ≤ R) (hR' : R ≤ 2) :
    0 ≤ reservoirPotential R ∧ reservoirPotential R ≤ 1/2 := by
  dsimp [reservoirPotential]
  constructor
  · positivity
  · nlinarith only [mul_nonneg hR (sub_nonneg.mpr hR')]

theorem reservoir_potential_hasDerivAt (R : ℝ → ℝ) (t v : ℝ)
    (hR : HasDerivAt R v t) :
    HasDerivAt (fun s => reservoirPotential (R s)) ((R t-1)*v) t := by
  convert ((hR.sub_const 1).pow 2).div_const 2 using 1
  ring

theorem reservoir_potential_drift (R z S d Z : ℝ)
    (hz : 0 ≤ z) (hz' : z ≤ Z) (hS : 0 ≤ S) :
    (R-1)*(d*(1-R)-R*z*S) ≤ -d*(R-1)^2+(Z/4)*S := by
  have hq : R*(1-R) ≤ 1/4 := by nlinarith only [sq_nonneg (R-1/2)]
  have hmul := mul_le_mul_of_nonneg_right hq (mul_nonneg hz hS)
  have hzS := mul_le_mul_of_nonneg_right hz' hS
  nlinarith only [hmul,hzS]

theorem reservoir_square_completion (v z Z : ℝ) :
    1/4+z*v+2*Z^2*v^2 = 2*(z*v+1/4)^2+1/8+2*(Z^2-z^2)*v^2 := by ring

theorem reservoir_corrected_gap (R z Z : ℝ) (hz : 0 ≤ z) (hz' : z ≤ Z) :
    1/8 ≤ 1/4+z*(R-1)+2*Z^2*(R-1)^2 := by
  rw [reservoir_square_completion]
  have hs : 0 ≤ Z^2-z^2 := by nlinarith
  have hp := mul_nonneg hs (sq_nonneg (R-1))
  nlinarith only [hp,sq_nonneg (z*(R-1)+1/4)]

/-- Algebraic reservoir correction, ready for literal donor instantiation.
The input is a dissipation/derivative estimate, not a persistence hypothesis. -/
theorem reservoir_corrected_growth (R z Z S D vV vPhi b d : ℝ)
    (hR : R ≤ 2) (hz : 0 ≤ z) (hz' : z ≤ Z) (hS : 0 ≤ S)
    (hb : 0 ≤ b) (hbd : b*d = 2*Z^2)
    (hgap : 1/4 ≤ z-1/2+150000*D)
    (hV : vV ≤ -D+400*R*S)
    (hPhi : vPhi ≤ -d*(R-1)^2+(Z/4)*S) :
    1/8-(120000000+b*Z/4)*S ≤ R*z-1/2-150000*vV-b*vPhi := by
  have hRS := mul_le_mul_of_nonneg_right hR hS
  have hPhi' := mul_le_mul_of_nonneg_left hPhi hb
  have hcorr := reservoir_corrected_gap R z Z hz hz'
  have hid : b*(-d*(R-1)^2+(Z/4)*S) = -2*Z^2*(R-1)^2+(b*Z/4)*S := by
    calc
      _ = -(b*d)*(R-1)^2+(b*Z/4)*S := by ring
      _ = _ := by rw [hbd]; ring
  rw [hid] at hPhi'
  nlinarith only [hRS,hPhi',hcorr,hV,hgap]

end MultiConsumerPermanence
