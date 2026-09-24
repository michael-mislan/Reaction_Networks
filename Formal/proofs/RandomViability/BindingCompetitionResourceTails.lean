import proofs.RandomViability.BindingCompetitionResources

namespace RandomViability.Binding
noncomputable section
open Classical FiniteCopy
open scoped BigOperators NNReal

theorem competition_resource_potential_generator (N : Counts) (V eps k r delta : ℝ) :
    competitionGenerator N V eps k r delta (resourcePotential V) =
      literalGenerator N V eps k r (resourcePotential V) := by
  have h := competition_resource_generator N V eps k r delta (fun u w =>
    Real.exp ((1/100)*(u-(11/10)*V))+Real.exp ((-1/100)*(u-(9/10)*V))+
    Real.exp ((1/100)*(w-(11/10)*V))+Real.exp ((-1/100)*(w-(9/10)*V)))
  simpa only [resourcePotential,upperUnitPotential,lowerUnitPotential,unitObs,
    ↓reduceIte] using h

theorem competition_resource_foster (V : ℕ) (eps k r delta : ℝ) (hV : 0 < (V:ℝ))
    (heps : 0 ≤ eps) (heps1 : eps ≤ 1) (hk : 0 ≤ k) (hk1 : k ≤ 1/8)
    (hr : 0 ≤ r) (hr1 : r ≤ 22) (hd : 0 ≤ delta) (X : CompetitionCounts V) :
    (competitionModel V eps k r delta hV heps hk hr hd).generator
      (fun Z => resourcePotential V (boxCounts (competitionCounts Z))) X ≤ 4*resourceSource V := by
  by_cases h : competitionEnabled X
  · rw [competition_model_inside V eps k r delta hV heps hk hr hd X _ h,
      competition_resource_potential_generator]
    have hh := stopped_resource_foster V eps k r hV heps heps1 hk hk1 hr hr1
      (competitionCounts X)
    rw [stopped_generator_inside V eps k r hV heps hk hr _ _ h.2] at hh
    exact hh
  · simp only [FiniteJumpModel.generator,competitionModel,if_neg h,zero_mul,
      Finset.sum_const_zero]
    unfold resourceSource
    positivity

/-- The physical counts are retained at resource and return failure. The bound
is for resource failure in this continuing-until-failure count law. -/
theorem competition_resource_probability (V : ℕ) (eps k r delta : ℝ)
    (hV : 0 < (V:ℝ)) (heps : 0 ≤ eps) (heps1 : eps ≤ 1)
    (hk : 0 ≤ k) (hk1 : k ≤ 1/8) (hr : 0 ≤ r) (hr1 : r ≤ 22) (hd : 0 ≤ delta)
    (q t : ℝ≥0) (hq : 0 < (q:ℝ))
    (hbound : ∀ X, (competitionModel V eps k r delta hV heps hk hr hd).total X ≤ q)
    (X : CompetitionCounts V) :
    ((competitionModel V eps k r delta hV heps hk hr hd).uniformize q hq hbound).poissonized
      (q*t) (FiniteKernel.eventIndicator {Z | ¬resourceGood (boxCounts (competitionCounts Z)) V}) X ≤
      resourcePotential V (boxCounts (competitionCounts X))+(t:ℝ)*(4*resourceSource V) := by
  have h := (competitionModel V eps k r delta hV heps hk hr hd).uniformized_event_bound q t hq hbound
    {Z | ¬resourceGood (boxCounts (competitionCounts Z)) V}
    (fun Z => resourcePotential V (boxCounts (competitionCounts Z)))
    1 (4*resourceSource V) (fun Z => resourcePotential_nonneg V (boxCounts (competitionCounts Z)))
    (fun Z hZ => resourcePotential_exit V (boxCounts (competitionCounts Z)) hZ)
    (competition_resource_foster V eps k r delta hV heps heps1 hk hk1 hr hr1 hd) X
  simpa only [one_mul] using h

end
end RandomViability.Binding
