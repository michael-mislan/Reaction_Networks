import proofs.InheritedCellAssay.ScalarBackward
import proofs.InheritedCellAssay.ScalarCountIntegral
import Mathlib.Tactic.GCongr

namespace InheritedCellAssay.ScalarRateSource
open ScalarCount

/- The clock is x=exp(t/10)-1, on [0,1]. These are the source's
   mean-matched rates after that deterministic change of time. -/
noncomputable def den (x : ℝ) : ℝ := 5*(1+x)^4+19
noncomputable def birth (x : ℝ) : ℝ := 5*(1+x)^3/den x
noncomputable def death (x : ℝ) : ℝ := 57/((1+x)*den x)
noncomputable def meanRatio (x : ℝ) : ℝ := (99/8)*(1+x)^3/den x
noncomputable def rateMass (x : ℝ) : ℝ := (495/8)*(1+x)^6/(den x)^2
noncomputable def accumulatedBirth (x : ℝ) : ℝ := ∫ s in x..1, rateMass s

theorem den_pos (x : ℝ) : 0 < den x := by unfold den; positivity

theorem rateMass_continuous : Continuous rateMass := by
  unfold rateMass den
  fun_prop (disch := intro x; exact pow_ne_zero 2 (ne_of_gt (den_pos x)))

theorem meanRatio_continuous : Continuous meanRatio := by
  unfold meanRatio den
  fun_prop (disch := intro x; exact ne_of_gt (den_pos x))

theorem rateMass_eq (x : ℝ) : rateMass x = birth x*meanRatio x := by
  unfold rateMass birth meanRatio
  ring

theorem accumulatedBirth_derivative (x : ℝ) :
    HasDerivAt accumulatedBirth (-birth x*meanRatio x) x := by
  have h := intervalIntegral.integral_hasDerivAt_left
    (rateMass_continuous.intervalIntegrable x 1)
    (rateMass_continuous.stronglyMeasurableAtFilter _ _)
    rateMass_continuous.continuousAt
  change HasDerivAt accumulatedBirth (-rateMass x) x at h
  rw [rateMass_eq] at h
  simpa only [neg_mul] using h

theorem accumulatedBirth_continuous : Continuous accumulatedBirth :=
  continuous_iff_continuousAt.mpr (fun x => (accumulatedBirth_derivative x).continuousAt)

theorem meanRatio_derivative (x : ℝ) (hx : 0 ≤ x) :
    HasDerivAt meanRatio (-(birth x-death x)*meanRatio x) x := by
  have hy := (hasDerivAt_id x).const_add 1
  have hd := ((hy.pow 4).const_mul 5).add_const 19
  have h := ((hy.pow 3).const_mul (99/8)).div hd (ne_of_gt (den_pos x))
  dsimp only [Pi.pow_apply, id_eq] at h
  have hy0 : 1+x ≠ 0 := by linarith
  convert h using 1
  norm_num
  unfold meanRatio birth death den
  field_simp [hy0, ne_of_gt (den_pos x)]
  ring

theorem birth_bounds (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    birth x ∈ Set.Icc (0 : ℝ) 1 := by
  have hy : 0 ≤ 1+x := by linarith [hx.1]
  constructor
  · exact div_nonneg (by positivity) (den_pos x).le
  · apply (div_le_iff₀ (den_pos x)).mpr
    unfold den
    have h := mul_nonneg hx.1 (pow_nonneg hy 3)
    nlinarith

theorem death_bounds (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    death x ∈ Set.Icc (0 : ℝ) 3 := by
  have hy : 1 ≤ 1+x := by linarith [hx.1]
  have hD : 19 ≤ den x := by unfold den; nlinarith [sq_nonneg ((1+x)^2)]
  have hb : 19 ≤ (1+x)*den x := by
    calc
      19 = (1 : ℝ)*19 := by ring
      _ ≤ (1+x)*den x := mul_le_mul hy hD (by norm_num) (by linarith)
  unfold death
  constructor
  · exact div_nonneg (by norm_num) (by linarith)
  · apply (div_le_iff₀ (by linarith : 0 < (1+x)*den x)).mpr
    linarith

theorem meanRatio_bounds (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ meanRatio x ∧ meanRatio x ≤ 6 := by
  have hy : 0 ≤ 1+x := by linarith [hx.1]
  have hpow : (1+x)^3 ≤ (2 : ℝ)^3 := by gcongr; linarith [hx.2]
  constructor
  · unfold meanRatio
    positivity [den_pos x]
  · unfold meanRatio
    apply (div_le_iff₀ (den_pos x)).mpr
    unfold den
    nlinarith [pow_nonneg hy 4]

theorem accumulatedBirth_nonneg (x : ℝ) (hx : x ≤ 1) : 0 ≤ accumulatedBirth x := by
  apply intervalIntegral.integral_nonneg hx
  intro s _
  unfold rateMass
  positivity [den_pos s]

theorem candidate_bounds (x z : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hz : z ∈ Set.Icc (0 : ℝ) 1) :
    ScalarBackward.candidate meanRatio accumulatedBirth z x ∈ Set.Icc (-10 : ℝ) 10 := by
  obtain ⟨hm0, hm6⟩ := meanRatio_bounds x hx
  have ha := accumulatedBirth_nonneg x hx.2
  have hw : 0 ≤ 1-z := by linarith [hz.2]
  have hD : 1 ≤ 1+accumulatedBirth x*(1-z) := by nlinarith
  have hN : 0 ≤ meanRatio x*(1-z) := mul_nonneg hm0 hw
  have hNu : meanRatio x*(1-z) ≤ 6 := by nlinarith [hz.1]
  have hq0 : 0 ≤ meanRatio x*(1-z)/(1+accumulatedBirth x*(1-z)) :=
    div_nonneg hN (by linarith)
  have hq6 : meanRatio x*(1-z)/(1+accumulatedBirth x*(1-z)) ≤ 6 := by
    apply (div_le_iff₀ (by linarith : 0 < 1+accumulatedBirth x*(1-z))).mpr
    linarith
  unfold ScalarBackward.candidate
  constructor <;> linarith

theorem candidate_terminal (z : ℝ) :
    ScalarBackward.candidate meanRatio accumulatedBirth z 1 = z := by
  norm_num [ScalarBackward.candidate, accumulatedBirth, meanRatio, den]

end InheritedCellAssay.ScalarRateSource
