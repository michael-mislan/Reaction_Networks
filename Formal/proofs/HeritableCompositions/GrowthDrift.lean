import proofs.FiniteCopy.Source

namespace HeritableCompositions
open FiniteCopy

noncomputable def membraneDirection : Point := ![0, 0, 1, 0]

noncomputable def growthField (γ : ℝ) (x : Point) : Point :=
  fun i => drift (1/100000) 0 x i - γ*x 2*(x i+membraneDirection i)

noncomputable def countConcentrationDrift (γ m : ℝ) (x : Point) : Point :=
  fun i => drift (1/100000) (1/m) x i -
    γ*x 2*m*(x i+membraneDirection i)/(m+1)

theorem membrane_jump (n m u : ℝ) (hm : 0 < m) :
    (n-u)/(m+1)-n/m = -(n/m+u)/(m+1) := by
  have hm0 : m ≠ 0 := ne_of_gt hm
  have hm1 : m+1 ≠ 0 := by linarith
  field_simp
  ring

theorem growth_correction (γ m : ℝ) (hm : 0 < m) (x : Point) :
    countConcentrationDrift γ m x - growthField γ x =
      fun i => (![2*(1/100000)*x 0, -(1/100000)*x 0, 4*x 2, -2*x 2] : Point) i/m +
        γ*x 2*(x i+membraneDirection i)/(m+1) := by
  have hm0 : m ≠ 0 := ne_of_gt hm
  have hm1 : m+1 ≠ 0 := by linarith
  ext i
  simp only [Pi.sub_apply, countConcentrationDrift, growthField, drift_formula]
  fin_cases i <;> norm_num [membraneDirection]
  all_goals field_simp
  all_goals ring

theorem proportional_division (n V p : ℝ) (hV : V ≠ 0) (hp : p ≠ 0) :
    (p*n)/(p*V) = n/V := by
  field_simp

theorem complementary_deviation (n D N : ℝ) :
    (n-D)/N-n/(2*N) = -(D/N-n/(2*N)) := by
  by_cases hN : N = 0
  · simp [hN]
  · field_simp
    ring

end HeritableCompositions
