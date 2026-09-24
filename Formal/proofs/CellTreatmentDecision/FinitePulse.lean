import proofs.CellTreatmentDecision.Resolution

namespace CellTreatmentDecision
noncomputable section

def pulseA (x : ℝ) : ℝ :=
  (x^4+x^3+x^2+x+1)*(3*x^5+6*x^4+9*x^3+12*x^2+8*x+4)
def pulseQ (x : ℝ) : ℝ :=
  3*x^8+12*x^7+30*x^6+60*x^5+98*x^4+137*x^3+170*x^2+159*x+66
def pulseD (x c : ℝ) : ℝ := x^2*(x-1)^3/210*(4*c*pulseA x+(x-1)*pulseQ x)

theorem finite_pulse_witnesses :
    pulseD (7/8) (-(1/5)) = (771817626293/659706976665600:ℝ) ∧
    pulseD (7/8) (1/5) = -(48037425121/219902325555200:ℝ) := by
  norm_num [pulseD, pulseA, pulseQ]

theorem finite_pulse_margin :
    (527449/4033680000:ℝ) < 48037425121/219902325555200 ∧
    (527449/4033680000:ℝ) < 771817626293/659706976665600 := by norm_num

theorem occupation_margin :
    (15317159/150994944:ℝ)/500 < 48037425121/219902325555200 := by norm_num

theorem classification_robust_margin :
    (17209/504210000:ℝ) < (428807/251658240)/10 := by norm_num

theorem asymmetric_covariance (a b c : ℝ) :
    a^2+a*b+b^2*(1/4+c)-(a+b/2)^2 = b^2*c := by ring

end
end CellTreatmentDecision
