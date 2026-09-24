import proofs.RandomViability.BindingCompetitionReturn
import proofs.RandomViability.BindingCompetitionTrackedEntry

namespace RandomViability.Binding
noncomputable section
open Classical FiniteCopy
open scoped BigOperators NNReal

def competitionTrackedReturnPotential {V : ℕ} (X : CompetitionCounts V) : ℝ :=
  if competitionPhase X=0 then Real.exp (-(V:ℝ)/62500)
  else competitionReturnPotential V (boxCounts (competitionCounts X))

theorem competition_tracked_return_nonneg {V : ℕ} (X : CompetitionCounts V) :
    0 ≤ competitionTrackedReturnPotential X := by
  unfold competitionTrackedReturnPotential competitionReturnPotential
  split_ifs <;> positivity

theorem competition_tracked_return_exit {V : ℕ} (X : CompetitionCounts V) (h : competitionPhase X=2) :
    1 ≤ competitionTrackedReturnPotential X := by
  have hv := X.property.2.2 h
  have hp : competitionPhase X≠0 := by omega
  simp only [competitionTrackedReturnPotential,if_neg hp]
  exact competition_return_exit V (boxCounts (competitionCounts X)) hv

theorem competition_return_before_entry {V : ℕ} (X : CompetitionCounts V)
    (j : CompetitionChannel) (hp : competitionPhase X=0) :
    competitionTrackedReturnPotential (competitionTrackedNext X j) ≤ competitionTrackedReturnPotential X := by
  have hp2 : competitionPhase X≠2 := by omega
  simp only [competitionTrackedReturnPotential,competitionTrackedNext_phase X j hp2,
    competitionTrackedNext_counts X j hp2,scaledPhaseStep,hp,if_true]
  by_cases hY : (V:ℝ)/2500 ≤ weightedCount (boxCounts
      (boxNext V (competitionCounts X) (competitionBase j)))
  · simp only [if_pos hY]
    norm_num
    exact competition_return_small V _ hY
  · simp [hY]

theorem competition_return_after_entry {V : ℕ} (X : CompetitionCounts V)
    (j : CompetitionChannel) (hp : competitionPhase X=1) :
    competitionTrackedReturnPotential (competitionTrackedNext X j) =
      competitionReturnPotential V (boxCounts (boxNext V (competitionCounts X) (competitionBase j))) := by
  have hp2 : competitionPhase X≠2 := by omega
  simp only [competitionTrackedReturnPotential,competitionTrackedNext_phase X j hp2,
    competitionTrackedNext_counts X j hp2,scaledPhaseStep,hp]
  split_ifs <;> norm_num at *
  omega

theorem competition_tracked_return_foster (V : ℕ) (eps k r delta : ℝ)
    (hV : 0 < (V:ℝ)) (heps : 0 ≤ eps) (heps1 : eps ≤ 1/1000000)
    (hk : 0 ≤ k) (hk1 : k ≤ 1/8) (hr : 18 ≤ r) (hr1 : r ≤ 22)
    (hd : 0 ≤ delta) (hd1 : delta ≤ 3/5) (X : CompetitionCounts V) :
    (competitionModel V eps k r delta hV heps hk (by linarith) hd).generator
      competitionTrackedReturnPotential X ≤ competitionReturnSource V := by
  by_cases h : competitionEnabled X
  · by_cases hp : competitionPhase X=0
    · have hh : (competitionModel V eps k r delta hV heps hk (by linarith) hd).generator
          competitionTrackedReturnPotential X ≤ 0 := by
        unfold FiniteJumpModel.generator
        apply Finset.sum_nonpos
        intro j _
        exact mul_nonpos_of_nonneg_of_nonpos
          ((competitionModel V eps k r delta hV heps hk (by linarith) hd).nonneg X j)
          (sub_nonpos.mpr (competition_return_before_entry X j hp))
      exact hh.trans (by unfold competitionReturnSource; positivity)
    · have hp1 : competitionPhase X=1 := by have hh := h.1; omega
      have he : (competitionModel V eps k r delta hV heps hk (by linarith) hd).generator
          competitionTrackedReturnPotential X =
          competitionGenerator (boxCounts (competitionCounts X)) V eps k r delta (competitionReturnPotential V) := by
        simp only [FiniteJumpModel.generator,competitionModel,if_pos h,competitionGenerator]
        apply Finset.sum_congr rfl
        intro j _
        rw [competition_return_after_entry X j hp1,boxNext_exact V (competitionCounts X)
          (competitionBase j) h.2]
        simp only [competitionTrackedReturnPotential,if_neg hp,competitionNext]
      rw [he]
      exact competition_return_foster _ V eps k r delta hV heps heps1 hk hk1 hr hr1 hd hd1 h.2
  · simp only [FiniteJumpModel.generator,competitionModel,if_neg h,zero_mul,Finset.sum_const_zero]
    unfold competitionReturnSource
    positivity

theorem competition_tracked_return_probability (V : ℕ) (eps k r delta : ℝ)
    (hV : 0 < (V:ℝ)) (heps : 0 ≤ eps) (heps1 : eps ≤ 1/1000000)
    (hk : 0 ≤ k) (hk1 : k ≤ 1/8) (hr : 18 ≤ r) (hr1 : r ≤ 22)
    (hd : 0 ≤ delta) (hd1 : delta ≤ 3/5) (q t : ℝ≥0) (hq : 0 < (q:ℝ))
    (hbound : ∀ X, (competitionModel V eps k r delta hV heps hk (by linarith) hd).total X ≤ q)
    (X : CompetitionCounts V) (hp : competitionPhase X=0) :
    ((competitionModel V eps k r delta hV heps hk (by linarith) hd).uniformize q hq hbound).poissonized (q*t)
      (FiniteKernel.eventIndicator {Z | competitionPhase Z=2}) X ≤
      Real.exp (-(V:ℝ)/62500)+(t:ℝ)*competitionReturnSource V := by
  have h := (competitionModel V eps k r delta hV heps hk (by linarith) hd).uniformized_event_bound q t hq hbound
    {Z | competitionPhase Z=2} competitionTrackedReturnPotential 1 (competitionReturnSource V)
    competition_tracked_return_nonneg (fun Z hZ => competition_tracked_return_exit Z hZ)
    (competition_tracked_return_foster V eps k r delta hV heps heps1 hk hk1 hr hr1 hd hd1) X
  simpa only [one_mul,competitionTrackedReturnPotential,if_pos hp] using h

end
end RandomViability.Binding
