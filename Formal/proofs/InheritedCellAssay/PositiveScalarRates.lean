import proofs.InheritedCellAssay.PositiveBirthIntegral

namespace InheritedCellAssay.PositiveMoments

noncomputable def scalarBirth (M : MomentODE) (x : ℝ) : ℝ :=
  M.R (clock x)/((1+x)*totalMean M x)
noncomputable def scalarDeath (M : MomentODE) (x : ℝ) : ℝ :=
  3*M.S (clock x)/((1+x)*totalMean M x)
noncomputable def backwardMean (M : MomentODE) (u x : ℝ) : ℝ := totalMean M u/totalMean M x
noncomputable def backwardBirth (M : MomentODE) (u x : ℝ) : ℝ :=
  totalMean M u*∫ s in x..u, birthDensity M s

theorem clock_derivative (x : ℝ) (hx : 0 ≤ x) : HasDerivAt clock (10/(1+x)) x := by
  have h := (((hasDerivAt_id x).const_add 1).log (by dsimp; linarith : 1+id x ≠ 0)).const_mul 10
  convert h using 1
  simp [id_eq, div_eq_mul_inv]

theorem totalMean_derivative (M : MomentODE) (x : ℝ) (hx : 0 ≤ x) :
    HasDerivAt (totalMean M) ((M.R (clock x)-3*M.S (clock x))/(1+x)) x := by
  have h := ((M.derivS (clock x)).add (M.derivR (clock x))).comp x (clock_derivative x hx)
  convert h using 1
  ring

theorem backwardMean_derivative (M : MomentODE) (u x : ℝ) (hx : x ∈ Set.Icc 0 1) :
    HasDerivAt (backwardMean M u)
      (-(scalarBirth M x-scalarDeath M x)*backwardMean M u x) x := by
  have hm := ne_of_gt (totalMean_pos M x hx)
  have hy : 1+x ≠ 0 := by linarith [hx.1]
  have h := (hasDerivAt_const x (totalMean M u)).div (totalMean_derivative M x hx.1) hm
  convert h using 1
  unfold scalarBirth scalarDeath backwardMean
  field_simp [hm,hy]
  ring

theorem birthDensity_continuousAt (M : MomentODE) (x : ℝ) (hx : x ∈ Set.Icc 0 1) :
    ContinuousAt (birthDensity M) x := by
  have ht := (clock_derivative x hx.1).continuousAt
  have hs := (M.derivS (clock x)).continuousAt.comp ht
  have hr := (M.derivR (clock x)).continuousAt.comp ht
  apply ContinuousAt.div hr ((continuousAt_const.add continuousAt_id).mul ((hs.add hr).pow 2))
  change (1+x)*(totalMean M x)^2 ≠ 0
  have hm := totalMean_pos M x hx
  have hy : 0 < 1+x := by linarith [hx.1]
  positivity

theorem birthDensity_integrable (M : MomentODE) (x u : ℝ)
    (hx : x ∈ Set.Icc 0 1) (hu : u ∈ Set.Icc 0 1) :
    IntervalIntegrable (birthDensity M) MeasureTheory.volume x u := by
  have hsub : Set.uIcc x u ⊆ Set.Icc 0 1 := by
    intro y hy
    rcases le_total x u with h | h
    · rw [Set.uIcc_of_le h] at hy
      exact ⟨hx.1.trans hy.1,hy.2.trans hu.2⟩
    · rw [Set.uIcc_of_ge h] at hy
      exact ⟨hu.1.trans hy.1,hy.2.trans hx.2⟩
  exact ((birthDensity_continuous M).mono hsub).intervalIntegrable

theorem backwardBirth_derivative (M : MomentODE) (u x : ℝ)
    (hu : u ∈ Set.Icc 0 1) (hx : x ∈ Set.Icc 0 1) :
    HasDerivAt (backwardBirth M u) (-scalarBirth M x*backwardMean M u x) x := by
  have hS : Continuous M.S := continuous_iff_continuousAt.mpr (fun x => (M.derivS x).continuousAt)
  have hR : Continuous M.R := continuous_iff_continuousAt.mpr (fun x => (M.derivR x).continuousAt)
  have hmeas : Measurable (birthDensity M) := by
    unfold birthDensity totalMean clock
    fun_prop
  have h := (intervalIntegral.integral_hasDerivAt_left (birthDensity_integrable M x u hx hu)
    hmeas.stronglyMeasurable.stronglyMeasurableAtFilter (birthDensity_continuousAt M x hx)).const_mul
      (totalMean M u)
  convert h using 1
  unfold scalarBirth backwardMean birthDensity
  have hm : totalMean M x ≠ 0 := ne_of_gt (totalMean_pos M x hx)
  have hy : 1+x ≠ 0 := by linarith [hx.1]
  change -(M.R (clock x) / ((1+x)*totalMean M x)) *
    (totalMean M u / totalMean M x) =
    totalMean M u * -(M.R (clock x) / ((1+x)*(totalMean M x)^2))
  field_simp [hm,hy]

theorem scalar_rate_bounds (M : MomentODE) (x : ℝ) (hx : x ∈ Set.Icc 0 1) :
    scalarBirth M x ∈ Set.Icc 0 1 ∧ scalarDeath M x ∈ Set.Icc 0 3 := by
  have hs := M.nonnegS (clock x) (clock_bounds x hx).1
  have hr := M.nonnegR (clock x) (clock_bounds x hx).1
  have hm := totalMean_pos M x hx
  have hy : 0 < 1+x := by linarith [hx.1]
  have hd : 0 < (1+x)*totalMean M x := mul_pos hy hm
  have hh := mul_nonneg hx.1 hm.le
  unfold scalarBirth scalarDeath
  constructor
  · constructor
    · positivity
    · apply (div_le_one hd).mpr
      unfold totalMean at *
      nlinarith
  · constructor
    · positivity
    · apply (div_le_iff₀ hd).mpr
      unfold totalMean at *
      nlinarith

end InheritedCellAssay.PositiveMoments
