import proofs.InheritedCellAssay.ScalarIntegralLink

namespace InheritedCellAssay.ScalarRateSource
open ScalarCount

theorem parameter_birth_identity : (1+accumulatedBirth 0)*geometricParameter = 1 := by
  have hi := varianceIntegral_bounds.1
  have hd : 33*varianceIntegral+97 ≠ 0 := by linarith
  rw [accumulatedBirth_zero]
  unfold geometricParameter
  field_simp [hd]
  ring

theorem candidate_half : ScalarBackward.candidate meanRatio accumulatedBirth (1/2) 0 =
    proposedPGFHalf := by
  have ha := accumulatedBirth_nonneg 0 (by norm_num)
  have hp := geometricParameter_bounds.1
  have hid := parameter_birth_identity
  unfold ScalarBackward.candidate proposedPGFHalf
  norm_num [meanRatio, den]
  apply (div_eq_div_iff (by positivity : (1 : ℝ)+accumulatedBirth 0*(1/2) ≠ 0)
    (by linarith : geometricParameter+1 ≠ 0)).mpr
  nlinarith

theorem candidate_quarter : ScalarBackward.candidate meanRatio accumulatedBirth (1/4) 0 =
    proposedPGFQuarter := by
  have ha := accumulatedBirth_nonneg 0 (by norm_num)
  have hp := geometricParameter_bounds.1
  have hid := parameter_birth_identity
  unfold ScalarBackward.candidate proposedPGFQuarter
  norm_num [meanRatio, den]
  apply (div_eq_div_iff (by positivity : (1 : ℝ)+accumulatedBirth 0*(3/4) ≠ 0)
    (by linarith : geometricParameter+3 ≠ 0)).mpr
  nlinarith

theorem candidate_eighth : ScalarBackward.candidate meanRatio accumulatedBirth (1/8) 0 =
    proposedPGFEighth := by
  have ha := accumulatedBirth_nonneg 0 (by norm_num)
  have hp := geometricParameter_bounds.1
  have hid := parameter_birth_identity
  unfold ScalarBackward.candidate proposedPGFEighth
  norm_num [meanRatio, den]
  apply (div_eq_div_iff (by positivity : (1 : ℝ)+accumulatedBirth 0*(7/8) ≠ 0)
    (by linarith : geometricParameter+7 ≠ 0)).mpr
  nlinarith

/-- A normalized count law characterized by its single-founder branching
    backward equation. Establishing this characterization for a path-space
    implementation remains a distinct modeling bridge. -/
structure BackwardCountSource where
  weight : ℕ → ℝ
  nonneg : ∀ n, 0 ≤ weight n
  normalized : HasSum weight 1
  pgf : ℝ → ℝ → ℝ
  linked : ∀ z ∈ Set.Icc (0 : ℝ) 1,
    HasSum (fun n => weight n*z^n) (pgf z 0)
  continuous : ∀ z ∈ Set.Icc (0 : ℝ) 1, ContinuousOn (pgf z) (Set.Icc (0 : ℝ) 1)
  derivative : ∀ z ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Ioc (0 : ℝ) 1,
    HasDerivAt (pgf z) (ScalarBackward.field (birth t) (death t) (pgf z t)) t
  bounds : ∀ z ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Ioc (0 : ℝ) 1,
    pgf z t ∈ Set.Icc (0 : ℝ) 1
  terminal : ∀ z ∈ Set.Icc (0 : ℝ) 1, pgf z 1 = z

theorem source_pgf (S : BackwardCountSource) (z : ℝ) (hz : z ∈ Set.Icc (0 : ℝ) 1) :
    S.pgf z 0 = ScalarBackward.candidate meanRatio accumulatedBirth z 0 :=
  candidate_identification z hz (S.pgf z) (S.continuous z hz)
    (S.derivative z hz) (S.bounds z hz) (S.terminal z hz)

theorem scalar_source_coverage (S : BackwardCountSource) :
    19/20 < S.weight 0+S.weight 1+S.weight 2 := by
  apply scalar_coverage_of_three_pgf S.weight S.nonneg S.normalized
  · have h := S.linked (1/2) (by norm_num)
    rw [source_pgf S (1/2) (by norm_num), candidate_half] at h
    exact h
  · have h := S.linked (1/4) (by norm_num)
    rw [source_pgf S (1/4) (by norm_num), candidate_quarter] at h
    exact h
  · have h := S.linked (1/8) (by norm_num)
    rw [source_pgf S (1/8) (by norm_num), candidate_eighth] at h
    exact h

end InheritedCellAssay.ScalarRateSource
