import proofs.SerialTransferSelection.BatchNutrientEndpoint
import proofs.SerialTransferSelection.BatchOddsProbability
import proofs.ResourceLimitedCompetition.EndpointOdds

namespace SerialTransferSelection
open ResourceLimitedCompetition HeritableCompositions FiniteCopy

/-- An endpoint size gain; the physical-law coverage theorem must supply both-type support. -/
theorem phase_size_gain_of_nonexceptional (N H0 L0 H L : ℕ) (hN : 0 < N)
    (hH0 : 0 < H0) (hL0 : 0 < L0) (hH : 0 < H) (hL : 0 < L)
    (hw : H+L=4*(H0+L0))
    (hn : ¬ Real.exp (19*(N : ℝ)/500000) ≤ oddsValue N H0 L0 H L) :
    (3/5)*Real.log 4-19/500 <
      Real.log H-Real.log L-(Real.log H0-Real.log L0) := by
  have hsum : 0 < (H0 : ℝ)+L0 := by positivity
  have htotal : Real.log ((H : ℝ)+L)-Real.log ((H0 : ℝ)+L0)=Real.log 4 := by
    have hwR : (H : ℝ)+L=4*((H0 : ℝ)+L0) := by exact_mod_cast hw
    rw [hwR,Real.log_mul (by norm_num) (ne_of_gt hsum)]
    ring
  have ht := lt_of_not_ge hn
  rw [oddsValue_exponential N H0 L0 H L hH hL,htotal] at ht
  have h := Real.exp_lt_exp.mp ht
  have hid : 19*(N : ℝ)/500000=((N : ℝ)/1000)*(19/500) := by ring
  rw [hid] at h
  have hpos : 0 < (N : ℝ)/1000 := by positivity
  have hg := (mul_lt_mul_iff_right₀ hpos).mp h
  linarith only [hg]

end SerialTransferSelection
