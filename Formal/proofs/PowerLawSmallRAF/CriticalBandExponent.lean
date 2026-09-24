import proofs.PowerLawSmallRAF.CriticalProfile

namespace PowerLawSmallRAF

open Set

noncomputable section

/-- Limiting fraction of reaction channels contributed by degree marks whose
logarithmic rank lies in the top `c` fraction of molecule space. -/
def criticalTopBandMass (b c : ℝ) : ℝ :=
  if b = 0 then c * Real.log 2 / (Real.pi ^ 2 / 6)
  else (Real.exp (-b * (1 - c) * Real.log 2) -
      Real.exp (-b * Real.log 2)) / (b * (Real.pi ^ 2 / 6))

theorem criticalTopBandMass_zero (b : ℝ) :
    criticalTopBandMass b 0 = 0 := by
  simp [criticalTopBandMass]

theorem criticalTopBandMass_one (b : ℝ) :
    criticalTopBandMass b 1 = criticalLambda b := by
  rw [criticalTopBandMass, criticalLambda]
  split_ifs with hb
  · ring
  · simp

theorem hasDerivAt_criticalTopBandMass (b c : ℝ) :
    HasDerivAt (criticalTopBandMass b)
      (Real.log 2 * Real.exp (-b * (1 - c) * Real.log 2) /
        (Real.pi ^ 2 / 6)) c := by
  by_cases hb : b = 0
  · subst b
    rw [show criticalTopBandMass 0 = fun x =>
        x * Real.log 2 / (Real.pi ^ 2 / 6) by
      funext x
      simp [criticalTopBandMass]]
    convert ((hasDerivAt_id c).mul_const (Real.log 2)).div_const
      (Real.pi ^ 2 / 6) using 1
    all_goals simp
  · have hinner : HasDerivAt
        (fun x : ℝ => -b * (1 - x) * Real.log 2)
        (b * Real.log 2) c := by
      convert (((hasDerivAt_const c (1 : ℝ)).sub (hasDerivAt_id c)).const_mul
        (-b)).mul_const (Real.log 2) using 1
      all_goals ring
    have hexp := (Real.hasDerivAt_exp
      (-b * (1 - c) * Real.log 2)).comp c hinner
    have hquot := (hexp.sub_const (Real.exp (-b * Real.log 2))).div_const
      (b * (Real.pi ^ 2 / 6))
    rw [show criticalTopBandMass b = fun x =>
        (Real.exp (-b * (1 - x) * Real.log 2) -
          Real.exp (-b * Real.log 2)) /
            (b * (Real.pi ^ 2 / 6)) by
      funext x
      simp only [criticalTopBandMass, if_neg hb]]
    convert hquot using 1
    field_simp [hb]

theorem continuous_criticalTopBandMass (b : ℝ) :
    Continuous (criticalTopBandMass b) :=
  continuous_iff_continuousAt.2
    (fun c => (hasDerivAt_criticalTopBandMass b c).continuousAt)

theorem strictMono_criticalTopBandMass (b : ℝ) :
    StrictMono (criticalTopBandMass b) := by
  apply strictMono_of_deriv_pos
  intro c
  rw [(hasDerivAt_criticalTopBandMass b c).deriv]
  exact div_pos (mul_pos (Real.log_pos one_lt_two) (Real.exp_pos _)) (by positivity)

/-- Above the full-catalogue emergence threshold, the candidate degree-band
exponent is the unique `c ∈ (0,1)` whose catalytic mass equals `log 2`. -/
theorem existsUnique_criticalTopBandMass_eq_log_two
    (lam : ℝ) (hlam : Real.log 2 < lam) :
    ∃! c : ℝ, c ∈ Ioo 0 1 ∧
      criticalTopBandMass
        (criticalLambdaInv (⟨lam, (Real.log_pos one_lt_two).trans hlam⟩ : Ioi (0 : ℝ))) c =
          Real.log 2 := by
  let b := criticalLambdaInv
    (⟨lam, (Real.log_pos one_lt_two).trans hlam⟩ : Ioi (0 : ℝ))
  have hbval : criticalLambda b = lam := by
    exact criticalLambda_criticalLambdaInv _
  have hmem : Real.log 2 ∈
      Icc (criticalTopBandMass b 0) (criticalTopBandMass b 1) := by
    rw [criticalTopBandMass_zero, criticalTopBandMass_one, hbval]
    exact ⟨(Real.log_pos one_lt_two).le, hlam.le⟩
  obtain ⟨c, hc, hceq⟩ := intermediate_value_Icc
    (show (0 : ℝ) ≤ 1 by norm_num)
    (continuous_criticalTopBandMass b).continuousOn hmem
  have hc0 : 0 < c := by
    by_contra h
    have : c = 0 := le_antisymm (le_of_not_gt h) hc.1
    subst c
    rw [criticalTopBandMass_zero] at hceq
    exact (Real.log_pos one_lt_two).ne' hceq.symm
  have hc1 : c < 1 := by
    by_contra h
    have : c = 1 := le_antisymm hc.2 (le_of_not_gt h)
    subst c
    rw [criticalTopBandMass_one, hbval] at hceq
    exact hlam.ne hceq.symm
  refine ⟨c, ⟨⟨hc0, hc1⟩, hceq⟩, ?_⟩
  intro d hd
  exact (strictMono_criticalTopBandMass b).injective (hd.2.trans hceq.symm)

end

end PowerLawSmallRAF
