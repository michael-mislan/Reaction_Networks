import proofs.ThermoCoreCompatibility.MultiInterface.WeightedPair

namespace ThermoCoreCompatibility.BeyondJunction

open MultiInterface

def unitFactors : Factors := ⟨1, 1, by norm_num, by norm_num⟩
def doubleFactors : Factors := ⟨2, 1, by norm_num, by norm_num⟩

theorem tangent_source_witness :
    doubleFactors.Productive (1/10) (13/200) ∧
    doubleFactors.Productive (13/200) (43/1000) ∧
    unitFactors.Productive (1/10) (43/1000) := by
  norm_num [Factors.Productive, doubleFactors, unitFactors]

theorem tangent_witness_boxes :
    (1/10 : ℝ) ∈ Set.Icc (1/25) (1/10) ∧
    (13/200 : ℝ) ∈ Set.Icc (1/25) (1/10) ∧
    (43/1000 : ℝ) ∈ Set.Icc (1/25) (1/10) := by norm_num

theorem tangent_certificate_impossible (dA dB dC : ℝ)
    (hA : 0 < dA) (hAB : (4/3)*dA < dB)
    (hBC : (4/3)*dB < dC) (hAC : dC < (5/3)*dA) : False := by
  linarith

theorem unit_shortcut_comparison (x : ℝ) :
    unitFactors.upper (unitFactors.upper x) - unitFactors.lower x =
    x*(x-1)*(3*x^2+9*x+2)/24 := by
  simp only [Factors.upper, Factors.lower, unitFactors]
  ring

theorem weighted_shortcut_comparison (x : ℝ) :
    doubleFactors.upper (doubleFactors.upper x) - unitFactors.lower x =
    x*(x-1)*(x^2+5*x-3)/27 := by
  simp only [Factors.upper, Factors.lower, doubleFactors, unitFactors]
  ring

end ThermoCoreCompatibility.BeyondJunction
