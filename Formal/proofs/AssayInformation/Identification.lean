import Mathlib.Tactic

noncomputable section
namespace AssayInformation

def sourceRate (b g R z : ℝ) : ℝ := (b+g*z)*(1-z/R)

/-- Exact reversal ambiguity in the literal source family. -/
theorem rate_reversal :
    sourceRate 2 1 6 0 = sourceRate (8/3) (2/3) 4 2 ∧
    sourceRate 2 1 6 1 = sourceRate (8/3) (2/3) 4 1 ∧
    sourceRate 2 1 6 2 = sourceRate (8/3) (2/3) 4 0 := by
  norm_num [sourceRate]

def endpointTransform (b g R s : ℝ) : ℝ :=
  (sourceRate b g R 0 / (sourceRate b g R 0+s)) *
  (sourceRate b g R 1 / (sourceRate b g R 1+s)) *
  (sourceRate b g R 2 / (sourceRate b g R 2+s))

/-- Algebraic transform equality. Probability-law identification is separate. -/
theorem endpoint_transform_equal (s : ℝ) :
    endpointTransform 2 1 6 s = endpointTransform (8/3) (2/3) 4 s := by
  norm_num [endpointTransform,sourceRate]
  ring

/-- Common positive speed cancels pathwise, before taking any distribution. -/
theorem clock_cancel (eᵢ eⱼ c qᵢ qⱼ : ℝ) (hc : c ≠ 0)
    (hi : qᵢ ≠ 0) (hj : qⱼ ≠ 0) (he : eᵢ ≠ 0) :
    (eⱼ/(c*qⱼ))/(eᵢ/(c*qᵢ)) = (qᵢ/qⱼ)*(eⱼ/eᵢ) := by
  field_simp

def capacityRatio (R i j : ℝ) : ℝ := (R-j)/(R-i)
def reconstruct (k i j : ℝ) : ℝ := (j-k*i)/(1-k)

theorem capacity_reconstruction (R i j : ℝ) (hi : i < R) (hij : i < j) :
    reconstruct (capacityRatio R i j) i j = R := by
  have hri : R-i ≠ 0 := ne_of_gt (sub_pos.mpr hi)
  have hji : j-i ≠ 0 := ne_of_gt (sub_pos.mpr hij)
  unfold reconstruct capacityRatio
  field_simp
  field_simp [hji]
  ring

/-- Exact finite difference quantifies blow-up near k=1. -/
theorem inverse_difference (k l i j : ℝ) (hk : k ≠ 1) (hl : l ≠ 1) :
    reconstruct l i j - reconstruct k i j =
      (j-i)*(l-k)/((1-l)*(1-k)) := by
  unfold reconstruct
  field_simp
  ring

theorem paired_discrimination :
    sourceRate (1/100) 1 5 2 /
      (sourceRate (1/100) 1 5 2 + sourceRate (1/100) 1 5 4) = 603/1004 ∧
    sourceRate (1/100) 1 10 2 /
      (sourceRate (1/100) 1 10 2 + sourceRate (1/100) 1 10 4) = 268/669 ∧
    (268/669:ℝ) < 603/1004 := by
  norm_num [sourceRate]

end AssayInformation
