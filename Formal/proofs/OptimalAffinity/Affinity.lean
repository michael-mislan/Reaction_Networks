import proofs.OptimalAffinity.GlobalMaximum

namespace OptimalAffinity

noncomputable def affinityExp (N : Network) (x y : ℝ) : ℝ :=
  (forwardFlux N 0 x y / reverseFlux N 0 x y) *
  (forwardFlux N 1 x y / reverseFlux N 1 x y)

noncomputable def seedRatio (N : Network) : ℝ := (beta N : ℝ) / alpha N

theorem oa2x2_optimumOneWayFluxes :
    forwardFlux oa2x2 0 1 1 = 3 ∧ reverseFlux oa2x2 0 1 1 = 2 ∧
    forwardFlux oa2x2 1 1 1 = 7 ∧ reverseFlux oa2x2 1 1 1 = 6 := by
  norm_num [forwardFlux, reverseFlux, oa2x2]

theorem oa2x2_localAffinitySigns :
    1 < forwardFlux oa2x2 0 1 1 / reverseFlux oa2x2 0 1 1 ∧
    1 < forwardFlux oa2x2 1 1 1 / reverseFlux oa2x2 1 1 1 := by
  norm_num [forwardFlux, reverseFlux, oa2x2]

theorem oa2x2_optimalAffinityExp : affinityExp oa2x2 1 1 = 7 / 4 := by
  norm_num [affinityExp, forwardFlux, reverseFlux, oa2x2]

theorem oa2x2_seedRatio : seedRatio oa2x2 = 2 := by
  norm_num [seedRatio, alpha, beta, oa2x2]

theorem oa2x2_affinityViolation : affinityExp oa2x2 1 1 < seedRatio oa2x2 := by
  rw [oa2x2_optimalAffinityExp, oa2x2_seedRatio]
  norm_num

theorem oa2x2_logAffinityViolation : Real.log (7 / 4 : ℝ) < Real.log 2 := by
  exact Real.strictMonoOn_log (by norm_num) (by norm_num) (by norm_num)

end OptimalAffinity
