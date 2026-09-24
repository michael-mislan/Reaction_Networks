import Mathlib.Tactic

namespace CellTreatmentDecision

noncomputable section

def offspring (c s t : ℝ) : ℝ :=
  (1/4+c)*(s*s+t*t)+(1/2-2*c)*s*t

theorem kernel_valid (c : ℝ) (lo : -(1/4:ℝ) ≤ c) (hi : c ≤ 1/4) :
    0 ≤ 1/4+c ∧ 0 ≤ 1/4-c ∧
    (1/4+c)+(1/4-c)+(1/4-c)+(1/4+c)=1 := by
  constructor
  · linarith
  constructor
  · linarith
  · ring

theorem one_sister (c : ℝ) : (1/4+c)+(1/4-c) = (1/2:ℝ) := by ring

theorem hidden_direction (c h s t : ℝ) :
    offspring (c+h) s t - offspring c s t = h*(s-t)^2 := by
  unfold offspring
  ring

theorem agreement (c : ℝ) : (1/4+c)+(1/4+c) = (1/2:ℝ)+2*c := by ring

theorem noisy_agreement (c eta : ℝ) :
    (1/2+2*c)*((1-eta)^2+eta^2)+(1/2-2*c)*(2*eta*(1-eta)) =
      1/2+2*c*(1-2*eta)^2 := by ring

theorem complementary_reconstruction (a r i j i' j' : ℤ)
    (ha : i+i'=a) (hr : j+j'=r) : i'=a-i ∧ j'=r-j := by omega

end
end CellTreatmentDecision
