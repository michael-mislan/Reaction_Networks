import proofs.HeritableCompositions.GrowingEnvelope

namespace HeritableCompositions
open FiniteCopy

theorem growing_ceiling_exponential (N γ : ℝ) (hN : 0 ≤ N)
    (hγ : 0 ≤ γ) (hγmax : γ ≤ 1/100000000000) :
    growingCeiling N γ ≤ Real.exp (3*(N*localAlpha*innerEnergy)/2) := by
  let u := N*localAlpha*innerEnergy
  have hu : 0 ≤ u := by dsimp [u,localAlpha,innerEnergy,outerEnergy]; positivity
  have hg : γ^2 ≤ (1/100000000000 : ℝ)^2 := by nlinarith only [hγ,hγmax]
  have hng := mul_le_mul_of_nonneg_left hg hN
  have hshift : 1344000000000*localAlpha*N*γ^2 ≤ u/8 := by
    dsimp [u,localAlpha,innerEnergy,outerEnergy]
    nlinarith only [hng,hN]
  have hpref : 2*(localAlpha*(200000000+8000000000*N*γ^2)) ≤ 1+u := by
    dsimp [u,localAlpha,innerEnergy,outerEnergy]
    nlinarith only [hng,hN]
  have hconst : Real.exp (33600000000*localAlpha) ≤ 2 := by
    have hh := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le
      (by norm_num [localAlpha] : |33600000000*localAlpha| ≤ 1))).2
    norm_num [localAlpha] at hh ⊢
    linarith only [hh]
  have hs := Real.exp_le_exp.mpr hshift
  have hprod := mul_le_mul hconst hs (Real.exp_pos _).le (by norm_num : (0 : ℝ) ≤ 2)
  rw [← Real.exp_add] at hprod
  have hfirst := mul_le_mul_of_nonneg_left hprod
    (by unfold localAlpha; positivity : 0 ≤ localAlpha*(200000000+8000000000*N*γ^2))
  have hsecond := mul_le_mul_of_nonneg_right hpref (Real.exp_pos (u/8)).le
  have hlinear : 1+u ≤ Real.exp u := by linarith only [Real.add_one_le_exp u]
  have hthird := mul_le_mul_of_nonneg_right hlinear (Real.exp_pos (u/8)).le
  have hlast : Real.exp u*Real.exp (u/8) ≤ Real.exp (3*u/2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith only [hu]
  change _ ≤ Real.exp (3*u/2)
  unfold growingCeiling
  nlinarith only [hfirst,hsecond,hthird,hlast]

theorem growing_ceiling_tail (N γ R : ℝ) (hN : 0 ≤ N)
    (hγ : 0 ≤ γ) (hγmax : γ ≤ 1/100000000000) (hR : 2*innerEnergy ≤ R) :
    growingCeiling N γ*Real.exp (-N*localAlpha*R) ≤
      Real.exp (-(N*localAlpha*innerEnergy)/2) := by
  have hh := mul_le_mul_of_nonneg_right (growing_ceiling_exponential N γ hN hγ hγmax)
    (Real.exp_pos (-N*localAlpha*R)).le
  rw [← Real.exp_add] at hh
  apply hh.trans
  apply Real.exp_le_exp.mpr
  have hr := mul_le_mul_of_nonneg_left hR
    (by unfold localAlpha; positivity : 0 ≤ N*localAlpha)
  nlinarith only [hr]

end HeritableCompositions
