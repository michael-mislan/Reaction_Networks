import proofs.SerialTransferSelection.CycleProbability
import proofs.SerialTransferSelection.ParameterMargins

namespace SerialTransferSelection
open ResourceLimitedCompetition HeritableCompositions FiniteCopy

def candidateN : ℕ := 131072000000000000000000
def candidateM : ℕ := 1000000000000000
def candidateTime : ℝ := 800000000000
noncomputable def candidateGamma : ℝ := 1/100000000000

theorem phaseChemicalRawError_expanded (N : ℕ) (M t : ℝ) :
    let u := (N : ℝ)*localAlpha*innerEnergy
    phaseChemicalRawError N M t = M*Real.exp (-7*u)+14*M*Real.exp (-4*u)+
      M*t*u/42*Real.exp (-15*u/2)+M*Real.exp (-u)+M*t*u/42*Real.exp (-3*u/2)+7*M*partitionError N := by
  dsimp only
  let u := (N : ℝ)*localAlpha*innerEnergy
  have h1 : Real.exp (-7*u)=Real.exp (-8*u)*Real.exp u := by rw [← Real.exp_add]; congr 1; ring
  have h2 : Real.exp (-4*u)=Real.exp (-8*u)*Real.exp (4*u) := by rw [← Real.exp_add]; congr 1; ring
  have h3 : Real.exp (-15*u/2)=Real.exp (-8*u)*Real.exp (u/2) := by rw [← Real.exp_add]; congr 1; ring
  have h4 : Real.exp (-u)=Real.exp (-2*u)*Real.exp u := by rw [← Real.exp_add]; congr 1; ring
  have h5 : Real.exp (-3*u/2)=Real.exp (-2*u)*Real.exp (u/2) := by rw [← Real.exp_add]; congr 1; ring
  change phaseChemicalRawError N M t = M*Real.exp (-7*u)+14*M*Real.exp (-4*u)+
    M*t*u/42*Real.exp (-15*u/2)+M*Real.exp (-u)+M*t*u/42*Real.exp (-3*u/2)+7*M*partitionError N
  rw [h1,h2,h3,h4,h5]
  unfold phaseChemicalRawError
  dsimp only
  change Real.exp (-(8*u))*(M*Real.exp u+14*M*Real.exp (4*u)+t*(16*M*(u/672)*Real.exp (u/2)))+
    Real.exp (-(2*u))*(M*Real.exp u+t*(16*M*(u/672)*Real.exp (u/2)))+7*M*partitionError N = _
  simp only [neg_mul]
  ring

noncomputable def nonserviceCycleError (N M : ℕ) (t p ε : ℝ) : ℝ :=
  phaseChemicalRawError N M t+Real.exp (-(N : ℝ)/2500)+Real.exp (-(19*(N : ℝ)/500000))+
    32/(ε^2*p*(M : ℝ))+(M : ℝ)*recoveryError ((N : ℝ)*localAlpha*innerEnergy)

theorem candidate_nonservice_error (p : ℝ) (hp : 1/100 ≤ p) :
    nonserviceCycleError candidateN candidateM candidateTime p (1/50) ≤ 1/1000000 := by
  have hp' : 0 < p := by linarith
  have ht : 32/((1/50 : ℝ)^2*p*(candidateM : ℝ)) ≤ 8/1000000000 := by
    have hd : (0 : ℝ) < (1/50)^2*p*candidateM := by unfold candidateM; positivity
    apply (div_le_iff₀ hd).mpr
    norm_num [candidateM]
    nlinarith only [hp]
  have h (x : ℝ) (hx : 128 ≤ x) : Real.exp (-x) ≤ 1/10^38 :=
    (exp_negative_uniform_bound x hx).trans (by norm_num)
  have h896 := h 1792 (by norm_num)
  have h1024 := h 1024 (by norm_num)
  have h1920 := h 1920 (by norm_num)
  have h256 := h 256 (by norm_num)
  have h384 := h 384 (by norm_num)
  have hpart := h ((candidateN : ℝ)/(35*10^12)) (by norm_num [candidateN])
  have hdeadline := h ((candidateN : ℝ)/2500) (by norm_num [candidateN])
  have hodds := h (19*(candidateN : ℝ)/500000) (by norm_num [candidateN])
  have h128 := h 128 (by norm_num)
  have h2048 := h 2048 (by norm_num)
  have h3968 := h 3968 (by norm_num)
  unfold nonserviceCycleError
  rw [phaseChemicalRawError_expanded]
  norm_num [candidateN,candidateM,candidateTime,localAlpha,innerEnergy,outerEnergy,
    partitionError,recoveryError] at hpart hdeadline hodds ⊢
  norm_num [candidateM] at ht
  linarith only [ht,h896,h1024,h1920,h256,h384,hpart,hdeadline,hodds,h128,h2048,h3968]

end SerialTransferSelection
