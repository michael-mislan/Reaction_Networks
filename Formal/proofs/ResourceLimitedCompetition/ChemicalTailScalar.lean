import proofs.ResourceLimitedCompetition.BirthPotentials

namespace ResourceLimitedCompetition
open HeritableCompositions FiniteCopy

noncomputable def chemicalScale (N : ℕ) : ℝ := (N : ℝ)*localAlpha*innerEnergy

noncomputable def chemicalRawError (N : ℕ) (M t : ℝ) : ℝ :=
  7*M*Real.exp (-12*chemicalScale N)+
  (M*t/84)*chemicalScale N*Real.exp (-(31/2)*chemicalScale N)+
  M*Real.exp (2*chemicalScale N-(N : ℝ)/1000000000000000)+
  (M*t/84)*chemicalScale N*Real.exp (-(3/2)*chemicalScale N)+
  24*M*Real.exp (-(N : ℝ)*(1/1000000)^2/35)

noncomputable def chemicalErrorBound (N M : ℕ) (γ : ℝ) : ℝ :=
  (M : ℝ)*(32+4/(21*γ))*Real.exp (-chemicalScale N/2)

noncomputable def competitionError (N M : ℕ) (γ : ℝ) : ℝ :=
  chemicalErrorBound N M γ+Real.exp (-(19*(N : ℝ)/500000))+Real.exp (-(N : ℝ)/2500)

theorem chemicalScale_nonneg (N : ℕ) : 0 ≤ chemicalScale N := by
  unfold chemicalScale localAlpha innerEnergy outerEnergy
  positivity

theorem exponential_polynomial_absorption (u a : ℝ) (hu : 0 ≤ u) (ha : (3/2 : ℝ) ≤ a) :
    u*Real.exp (-a*u) ≤ Real.exp (-u/2) := by
  have he : u ≤ Real.exp u := by linarith only [Real.add_one_le_exp u]
  have h := mul_le_mul_of_nonneg_right he (Real.exp_pos (-a*u)).le
  rw [← Real.exp_add] at h
  apply h.trans (Real.exp_le_exp.mpr _)
  have hm := mul_le_mul_of_nonneg_right ha hu
  nlinarith only [hm]

theorem chemical_raw_envelope (N : ℕ) (M t : ℝ) (hM : 0 ≤ M) (ht : 0 ≤ t) :
    chemicalRawError N M t ≤ M*(32+t/42)*Real.exp (-chemicalScale N/2) := by
  have hu := chemicalScale_nonneg N
  have h1 := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
    (by linarith only [hu] : -12*chemicalScale N ≤ -chemicalScale N/2))
    (by positivity : 0 ≤ 7*M)
  have h2 := mul_le_mul_of_nonneg_left (exponential_polynomial_absorption (chemicalScale N) (31/2) hu (by norm_num))
    (by positivity : 0 ≤ M*t/84)
  have hs : 2*chemicalScale N-(N : ℝ)/1000000000000000 ≤ -chemicalScale N/2 := by
    unfold chemicalScale localAlpha innerEnergy outerEnergy
    have hn : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    nlinarith only [hn]
  have h3 := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hs) hM
  have h4 := mul_le_mul_of_nonneg_left (exponential_polynomial_absorption (chemicalScale N) (3/2) hu (by norm_num))
    (by positivity : 0 ≤ M*t/84)
  have hp : -(N : ℝ)*(1/1000000)^2/35 ≤ -chemicalScale N/2 := by
    unfold chemicalScale localAlpha innerEnergy outerEnergy
    have hn : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    nlinarith only [hn]
  have h5 := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hp) (by positivity : 0 ≤ 24*M)
  unfold chemicalRawError
  nlinarith only [h1,h2,h3,h4,h5]

theorem chemical_raw_deadline_bound (N M : ℕ) (γ : ℝ) (hγ : 0 < γ) :
    chemicalRawError N M (8/γ) ≤ chemicalErrorBound N M γ := by
  have h := chemical_raw_envelope N M (8/γ) (Nat.cast_nonneg _) (by positivity)
  convert h using 1
  unfold chemicalErrorBound
  congr 2
  ring

end ResourceLimitedCompetition
