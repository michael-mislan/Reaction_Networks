import Mathlib

namespace HeritableCompositions

noncomputable def outerEnergy : ℝ := 1/32000000
noncomputable def innerEnergy : ℝ := outerEnergy/16

/-- A deliberately weaker bound than the guide's 23856 leaves ample room for
direct coefficient estimates of both source quadratic forms. -/
theorem growth_absorption_budget (γ r E : ℝ)
    (hγ : 0 ≤ γ) (hγmax : γ ≤ 1/100000000000)
    (hr : 0 ≤ r) (hE : innerEnergy ≤ E) (hupper : E ≤ 42*r^2) :
    60000*γ*r ≤ (59/200)*r^2 := by
  have hc : (60000*γ)^2 ≤ (59/200)^2*(innerEnergy/42) := by
    have hg : γ^2 ≤ (1/100000000000 : ℝ)^2 := by nlinarith
    norm_num [innerEnergy, outerEnergy] at *
    nlinarith only [hg]
  have hr2 : innerEnergy/42 ≤ r^2 := by linarith only [hE, hupper]
  have hsmall : 60000*γ ≤ (59/200)*r := by
    nlinarith only [hc, hr2, hr, hγ]
  nlinarith only [mul_le_mul_of_nonneg_right hsmall hr]

theorem annular_growth_decay (γ r E resident perturbation : ℝ)
    (hγ : 0 ≤ γ) (hγmax : γ ≤ 1/100000000000)
    (hr : 0 ≤ r) (hE : innerEnergy ≤ E) (hupper : E ≤ 42*r^2)
    (hresident : resident ≤ -(59/100)*r^2)
    (hperturbation : perturbation ≤ 60000*γ*r) :
    resident+perturbation ≤ -(59/8400)*E := by
  have ha := growth_absorption_budget γ r E hγ hγmax hr hE hupper
  nlinarith only [ha, hresident, hperturbation, hupper]

theorem partition_margin :
    (42 : ℝ)*16*(1/1000000)^2 < innerEnergy := by
  norm_num [innerEnergy, outerEnergy]

theorem recovery_time_budget :
    (300 : ℝ)*(59/8400) > 2 := by norm_num

end HeritableCompositions
