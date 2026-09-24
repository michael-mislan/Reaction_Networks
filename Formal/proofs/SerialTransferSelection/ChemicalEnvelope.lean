import proofs.SerialTransferSelection.ManyCycleParameters
import Mathlib.Analysis.SpecialFunctions.Exp

namespace SerialTransferSelection
open ResourceLimitedCompetition HeritableCompositions FiniteCopy Filter Topology

/-- Uniform chemical envelope; all resident, division and deadline terms retained. -/
theorem chemicalCycleError_envelope (N M : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    let u := (N : ℝ)*localAlpha*innerEnergy
    chemicalCycleError N M t ≤ ((M : ℝ)*(76+16*u+t*u/21)+2)*Real.exp (-u/2) := by
  dsimp only
  let u := (N : ℝ)*localAlpha*innerEnergy
  have hu : 0 ≤ u := by dsimp [u,localAlpha,innerEnergy,outerEnergy]; positivity
  have he (x : ℝ) (hx : u/2 ≤ x) : Real.exp (-x) ≤ Real.exp (-u/2) := by
    apply Real.exp_le_exp.mpr
    linarith
  have h1 := he (7*u) (by linarith)
  have h2 := he (4*u) (by linarith)
  have h3 := he (15*u/2) (by linarith)
  have h4 := he u (by linarith)
  have h5 := he (3*u/2) (by linarith)
  have h6 := he ((N : ℝ)/(35*10^12)) (by
    norm_num [u,localAlpha,innerEnergy,outerEnergy]; linarith [Nat.cast_nonneg (α := ℝ) N])
  have h7 := he ((N : ℝ)/2500) (by
    norm_num [u,localAlpha,innerEnergy,outerEnergy]; linarith [Nat.cast_nonneg (α := ℝ) N])
  have h8 := he (19*(N : ℝ)/500000) (by
    norm_num [u,localAlpha,innerEnergy,outerEnergy]; linarith [Nat.cast_nonneg (α := ℝ) N])
  have h9 := he (8*u) (by linarith)
  have h10 := he (31*u/2) (by linarith)
  unfold chemicalCycleError
  rw [phaseChemicalRawError_expanded]
  change (M : ℝ)*Real.exp (-7*u)+14*M*Real.exp (-4*u)+
    M*t*u/42*Real.exp (-15*u/2)+M*Real.exp (-u)+M*t*u/42*Real.exp (-3*u/2)+
    7*M*partitionError N+Real.exp (-(N : ℝ)/2500)+Real.exp (-(19*(N : ℝ)/500000))+
    M*recoveryError u ≤ _
  unfold partitionError recoveryError
  have hm : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hc : 0 ≤ (M : ℝ)*t*u/42 := by positivity
  have hs := add_le_add
    (add_le_add (add_le_add (add_le_add (add_le_add
      (mul_le_mul_of_nonneg_left h1 hm)
      (mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ 14*(M : ℝ))))
      (mul_le_mul_of_nonneg_left h3 hc))
      (mul_le_mul_of_nonneg_left h4 hm))
      (mul_le_mul_of_nonneg_left h5 hc))
    (mul_le_mul_of_nonneg_left h6 (by positivity : 0 ≤ 56*(M : ℝ)))
  have hr := mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add (add_le_add h4 (le_refl (2*Real.exp (-u/2)))) h9)
      (mul_le_mul_of_nonneg_left h10 (by positivity : 0 ≤ 16*u))) hm
  have hall := add_le_add (add_le_add (add_le_add hs h7) h8) hr
  simp only [neg_mul, neg_div] at hall ⊢
  convert hall using 1 <;> dsimp [u] <;> ring

theorem chemicalCycleError_tendsto (M : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    Tendsto (fun N : ℕ => chemicalCycleError N M t) atTop (𝓝 0) := by
  let a : ℝ := localAlpha*innerEnergy/2
  have ha : 0 < a := by norm_num [a,localAlpha,innerEnergy,outerEnergy]
  have hn : Tendsto (fun N : ℕ => a*(N : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop).const_mul_atTop ha
  have he := Real.tendsto_exp_neg_atTop_nhds_zero.comp hn
  have hx := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hn
  have hx' : Tendsto (fun N : ℕ => (N : ℝ)*Real.exp (-(a*(N : ℝ)))) atTop (𝓝 0) := by
    have hh := hx.const_mul a⁻¹
    simp only [mul_zero] at hh
    convert hh using 1
    simp [pow_one, ← mul_assoc, ne_of_gt ha]
  have hb := (he.const_mul ((M : ℝ)*76+2)).add
    (hx'.const_mul ((M : ℝ)*(16+t/21)*(localAlpha*innerEnergy)))
  simp only [mul_zero,add_zero] at hb
  apply squeeze_zero (fun N => by
    unfold chemicalCycleError phaseChemicalRawError recoveryError partitionError localAlpha innerEnergy outerEnergy
    positivity) (fun N => chemicalCycleError_envelope N M t ht)
  convert hb using 1
  funext N
  have hex : -((N : ℝ)*localAlpha*innerEnergy)/2 = -(a*(N : ℝ)) := by dsimp [a]; ring
  rw [hex]
  dsimp only [Function.comp_def]
  ring

end SerialTransferSelection
