import proofs.SerialTransferSelection.NonvacuousInstance

namespace SerialTransferSelection
open ResourceLimitedCompetition HeritableCompositions FiniteCopy

def smallerN : ℕ := 65536000000000000000000
def smallerM : ℕ := 4000000000

theorem exp_negative_64_bound : Real.exp (-64 : ℝ) ≤ 1/(2 : ℝ)^64 := by
  have h1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hp : (2 : ℝ)^64 ≤ (Real.exp 1)^64 := pow_le_pow_left₀ (by norm_num) h1 64
  have he : (Real.exp 1)^64=Real.exp 64 := by rw [← Real.exp_nat_mul]; norm_num
  rw [he] at hp
  rw [Real.exp_neg,inv_eq_one_div]
  exact one_div_le_one_div_of_le (by positivity) hp

theorem smaller_nonservice_error (p : ℝ) (hp : 1/100 ≤ p) :
    nonserviceCycleError smallerN smallerM candidateTime p (1/50) ≤ 2001/1000000 := by
  have hp' : 0 < p := by linarith
  have ht : 32/((1/50 : ℝ)^2*p*(smallerM : ℝ)) ≤ 1/500 := by
    have hd : (0 : ℝ) < (1/50)^2*p*smallerM := by unfold smallerM; positivity
    apply (div_le_iff₀ hd).mpr
    norm_num [smallerM]
    nlinarith only [hp]
  have h (x : ℝ) (hx : 128 ≤ x) : Real.exp (-x) ≤ 1/10^38 :=
    (exp_negative_uniform_bound x hx).trans (by norm_num)
  have h896 := h 896 (by norm_num)
  have h1024 := h 512 (by norm_num)
  have h1920 := h 960 (by norm_num)
  have h256 := h 128 (by norm_num)
  have h384 := h 192 (by norm_num)
  have hpart := h ((smallerN : ℝ)/(35*10^12)) (by norm_num [smallerN])
  have hdeadline := h ((smallerN : ℝ)/2500) (by norm_num [smallerN])
  have hodds := h (19*(smallerN : ℝ)/500000) (by norm_num [smallerN])
  have h128 := exp_negative_64_bound
  have h2048 := h 1024 (by norm_num)
  have h3968 := h 1984 (by norm_num)
  unfold nonserviceCycleError
  rw [phaseChemicalRawError_expanded]
  norm_num [smallerN,smallerM,candidateTime,localAlpha,innerEnergy,outerEnergy,
    partitionError,recoveryError] at hpart hdeadline hodds ⊢
  norm_num [smallerM] at ht
  linarith only [ht,h896,h1024,h1920,h256,h384,hpart,hdeadline,hodds,h128,h2048,h3968]


theorem original_sharp_error (JB JR : ℕ) (qb qr : ℝ)
    (hb : candidateTime*qb/JB < 1/1000)
    (hr : (candidateM : ℝ)*(5376*qr/JR) < 1/1000) :
    sourceCycleError candidateN candidateM JB JR qb qr candidateTime (1/2) (1/50)+
      sourceCycleError candidateN candidateM JB JR qb qr candidateTime (1/100) (1/50) < 2001/500000 := by
  rw [sourceCycleError_split,sourceCycleError_split]
  have h0 := candidate_nonservice_error (1/2) (by norm_num)
  have h1 := candidate_nonservice_error (1/100) le_rfl
  linarith only [h0,h1,hb,hr]

theorem smaller_sharp_error (JB JR : ℕ) (qb qr : ℝ)
    (hb : candidateTime*qb/JB < 1/1000)
    (hr : (smallerM : ℝ)*(5376*qr/JR) < 1/1000) :
    sourceCycleError smallerN smallerM JB JR qb qr candidateTime (1/2) (1/50)+
      sourceCycleError smallerN smallerM JB JR qb qr candidateTime (1/100) (1/50) < 4001/500000 := by
  rw [sourceCycleError_split,sourceCycleError_split]
  have h0 := smaller_nonservice_error (1/2) (by norm_num)
  have h1 := smaller_nonservice_error (1/100) le_rfl
  linarith only [h0,h1,hb,hr]

end SerialTransferSelection
