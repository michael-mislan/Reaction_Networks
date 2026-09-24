import proofs.HeritableCompositions.EnvelopeTail

namespace HeritableCompositions
open FiniteCopy

noncomputable def heredityExponent : ℝ := localAlpha*innerEnergy/2
noncomputable def generationPrefactor (γ : ℝ) : ℝ := 15+4032+10/(9*γ)

theorem heredity_error_eq (N : ℕ) : Real.exp (-(N : ℝ)*heredityExponent) =
    Real.exp (-((N : ℝ)*localAlpha*innerEnergy)/2) := by
  congr 1
  unfold heredityExponent
  ring

theorem heredityExponent_pos : 0 < heredityExponent := by
  norm_num [heredityExponent,localAlpha,innerEnergy,outerEnergy]

theorem deadline_after_recovery (γ : ℝ) (hγ : 0 < γ) (hγmax : γ ≤ 1/100000000000) :
    4032 < 10/(9*γ) := by
  apply (lt_div_iff₀ (by positivity : 0 < 9*γ)).mpr
  linarith only [hγmax]

noncomputable def secondDuration (γ : ℝ) (hγ : 0 < γ) (hγmax : γ ≤ 1/100000000000) : NNReal :=
  ⟨10/(9*γ)-4032,sub_nonneg.mpr (deadline_after_recovery γ hγ hγmax).le⟩

theorem first_phase_clock_budget (γ : ℝ) (hγmax : γ ≤ 1/100000000000) :
    (γ*4)*(4032 : NNReal) ≤ 2/5 := by
  norm_num
  linarith only [hγmax]

theorem second_phase_clock_budget (γ : ℝ) (hγ : 0 < γ) (hγmax : γ ≤ 1/100000000000) :
    1099/1000 ≤ (γ*(99/100))*(secondDuration γ hγ hγmax : ℝ) := by
  have hg : γ ≠ 0 := ne_of_gt hγ
  have he : (γ*(99/100))*(secondDuration γ hγ hγmax : ℝ) = 11/10-(γ*(99/100))*4032 := by
    change (γ*(99/100))*(10/(9*γ)-4032) = 11/10-(γ*(99/100))*4032
    field_simp
    ring
  rw [he]
  linarith only [hγmax]

theorem secondDuration_le_deadline (γ : ℝ) (hγ : 0 < γ) (hγmax : γ ≤ 1/100000000000) :
    (secondDuration γ hγ hγmax : ℝ) ≤ 10/(9*γ) := by
  change 10/(9*γ)-4032 ≤ 10/(9*γ)
  linarith

theorem clock_error_weaken (N : ℕ) :
    Real.exp (-(N : ℝ)/500) ≤ Real.exp (-(N : ℝ)*heredityExponent) := by
  apply Real.exp_le_exp.mpr
  norm_num [heredityExponent,localAlpha,innerEnergy,outerEnergy]
  nlinarith only [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]

theorem early_error_weaken (N : ℕ) :
    Real.exp (-(N : ℝ)/125) ≤ Real.exp (-(N : ℝ)*heredityExponent) := by
  apply Real.exp_le_exp.mpr
  norm_num [heredityExponent,localAlpha,innerEnergy,outerEnergy]
  nlinarith only [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]

theorem partition_error_weaken (N : ℕ) :
    Real.exp (-(N : ℝ)*(1/1000000)^2/35) ≤ Real.exp (-(N : ℝ)*heredityExponent) := by
  apply Real.exp_le_exp.mpr
  norm_num [heredityExponent,localAlpha,innerEnergy,outerEnergy]
  nlinarith only [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]

end HeritableCompositions
