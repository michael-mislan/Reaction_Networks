import proofs.ProductiveMemory.ExtractionChemicalProbability

namespace ProductiveMemory
open ResourceLimitedCompetition HeritableCompositions FiniteCopy
noncomputable section
set_option Elab.async false

def productiveM : ℕ := 4000000000
def productiveTime : NNReal := 800000000000
def productiveGamma : ℝ := 1/100000000000

def productiveCycleError (N M : ℕ) (t p eps : ℝ) : ℝ :=
  productiveChemicalRawError N M t+Real.exp (-(N:ℝ)/2500)+Real.exp (-(19*(N:ℝ)/500000))+
    Real.exp (-((N:ℝ)*M))+2/10^6+32/(eps^2*p*(M:ℝ))+2*(M:ℝ)/10^18

theorem productiveChemicalRawError_expanded (N : ℕ) (M t : ℝ) :
    let u := (N : ℝ)*localAlpha*readyLevel
    productiveChemicalRawError N M t = M*Real.exp (-7*u)+14*M*Real.exp (-4*u)+
      M*t*u/60*Real.exp (-15*u/2)+M*Real.exp (-u)+M*t*u/60*Real.exp (-3*u/2)+7*M*partitionError N := by
  dsimp only
  let u := (N : ℝ)*localAlpha*readyLevel
  have h1 : Real.exp (-7*u)=Real.exp (-8*u)*Real.exp u := by rw [← Real.exp_add]; congr 1; ring
  have h2 : Real.exp (-4*u)=Real.exp (-8*u)*Real.exp (4*u) := by rw [← Real.exp_add]; congr 1; ring
  have h3 : Real.exp (-15*u/2)=Real.exp (-8*u)*Real.exp (u/2) := by rw [← Real.exp_add]; congr 1; ring
  have h4 : Real.exp (-u)=Real.exp (-2*u)*Real.exp u := by rw [← Real.exp_add]; congr 1; ring
  have h5 : Real.exp (-3*u/2)=Real.exp (-2*u)*Real.exp (u/2) := by rw [← Real.exp_add]; congr 1; ring
  change productiveChemicalRawError N M t = M*Real.exp (-7*u)+14*M*Real.exp (-4*u)+
    M*t*u/60*Real.exp (-15*u/2)+M*Real.exp (-u)+M*t*u/60*Real.exp (-3*u/2)+7*M*partitionError N
  rw [h1,h2,h3,h4,h5]
  unfold productiveChemicalRawError
  dsimp only
  change Real.exp (-(8*u))*(M*Real.exp u+14*M*Real.exp (4*u)+t*(16*M*(u/960)*Real.exp (u/2)))+
    Real.exp (-(2*u))*(M*Real.exp u+t*(16*M*(u/960)*Real.exp (u/2)))+7*M*partitionError N = _
  simp only [neg_mul]
  ring

theorem productive_exp_tail (x : ℝ) (hx : 128 ≤ x) : Real.exp (-x) ≤ 1/10^38 := by
  have h1 : (2:ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1:ℝ)]
  have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) h1 128
  have he : (Real.exp 1)^128=Real.exp 128 := by rw [← Real.exp_nat_mul]; norm_num
  rw [he] at hp
  have hneg : Real.exp (-128:ℝ) ≤ 1/(2:ℝ)^128 := by
    rw [Real.exp_neg,inv_eq_one_div]
    exact one_div_le_one_div_of_le (by positivity) hp
  exact (Real.exp_le_exp.mpr (by linarith only [hx])).trans (hneg.trans (by norm_num))

theorem productive_cycle_error_evaluated (p : ℝ) (hp : 1/100 ≤ p) :
    productiveCycleError recoveryCount productiveM productiveTime p (1/50) ≤ 2003/1000000 := by
  have hp' : 0 < p := by linarith
  have ht : 32/((1/50:ℝ)^2*p*(productiveM:ℝ)) ≤ 1/500 := by
    have hd : (0:ℝ) < (1/50)^2*p*productiveM := by unfold productiveM; positivity
    apply (div_le_iff₀ hd).mpr
    norm_num [productiveM]
    nlinarith only [hp]
  have h896 := productive_exp_tail 896 (by norm_num)
  have h512 := productive_exp_tail 512 (by norm_num)
  have h960 := productive_exp_tail 960 (by norm_num)
  have h128 := productive_exp_tail 128 (by norm_num)
  have h192 := productive_exp_tail 192 (by norm_num)
  have hpart := productive_exp_tail ((recoveryCount:ℝ)/(35*10^12)) (by norm_num [recoveryCount])
  have hdeadline := productive_exp_tail ((recoveryCount:ℝ)/2500) (by norm_num [recoveryCount])
  have hodds := productive_exp_tail (19*(recoveryCount:ℝ)/500000) (by norm_num [recoveryCount])
  have houtput := productive_exp_tail ((recoveryCount:ℝ)*productiveM) (by norm_num [recoveryCount,productiveM])
  unfold productiveCycleError
  rw [productiveChemicalRawError_expanded]
  norm_num [recoveryCount,productiveM,productiveTime,localAlpha,readyLevel,outerLevel,partitionError]
    at hpart hdeadline hodds houtput ⊢
  norm_num [productiveM] at ht
  linarith only [ht,h896,h512,h960,h128,h192,hpart,hdeadline,hodds,houtput]

end
end ProductiveMemory
