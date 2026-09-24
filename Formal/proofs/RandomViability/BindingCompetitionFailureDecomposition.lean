import proofs.RandomViability.BindingCompetitionWindowDistribution

namespace RandomViability.Binding
noncomputable section
open Classical FiniteCopy
open scoped BigOperators NNReal
variable {V C : ℕ}

def competitionNoEntry (X : CompetitionCounts V) : ℝ :=
  FiniteKernel.eventIndicator {Z | competitionPhase Z=0 ∧ resourceGood (boxCounts (competitionCounts Z)) V} X

theorem competition_noentry_nonneg (X : CompetitionCounts V) : 0 ≤ competitionNoEntry X := by
  unfold competitionNoEntry FiniteKernel.eventIndicator
  split_ifs <;> norm_num

theorem competition_noentry_le_one (X : CompetitionCounts V) : competitionNoEntry X ≤ 1 := by
  unfold competitionNoEntry FiniteKernel.eventIndicator
  split_ifs <;> norm_num

theorem competition_noentry_generator (eps k r delta : ℝ) (hV : 0 < (V:ℝ))
    (heps : 0 ≤ eps) (hk : 0 ≤ k) (hr : 0 ≤ r) (hd : 0 ≤ delta)
    (X : CompetitionCounts V) :
    (competitionModel V eps k r delta hV heps hk hr hd).generator competitionNoEntry X ≤ 0 := by
  by_cases hen : competitionEnabled X
  · by_cases hp : competitionPhase X=0
    · have hx : competitionNoEntry X=1 := by simp [competitionNoEntry,FiniteKernel.eventIndicator,hp,hen.2]
      unfold FiniteJumpModel.generator
      apply Finset.sum_nonpos
      intro j _
      exact mul_nonpos_of_nonneg_of_nonpos
        ((competitionModel V eps k r delta hV heps hk hr hd).nonneg X j)
        (by rw [hx]; exact sub_nonpos.mpr (competition_noentry_le_one _))
    · have hn (j : CompetitionChannel) := competition_next_nezero X j hp
      simp [FiniteJumpModel.generator,competitionModel,competitionNoEntry,FiniteKernel.eventIndicator,hp,hn]
  · simp [FiniteJumpModel.generator,competitionModel,hen]

def competitionOperatingFailure (X : CompetitionMonitorState V C) : ℝ :=
  FiniteKernel.eventIndicator {Z | ¬(competitionWindowGood Z.1 ∧ Z.2=true)} X

theorem competition_failure_decomposition (X : CompetitionMonitorState V C) :
    competitionOperatingFailure X ≤ competitionNoEntry X.1.1+
      resourcePotential V (boxCounts (competitionCounts X.1.1))+
      competitionTrackedReturnPotential X.1.1+competitionMonitorBad X := by
  have hn := competition_noentry_nonneg X.1.1
  have hr := resourcePotential_nonneg V (boxCounts (competitionCounts X.1.1))
  have ht := competition_tracked_return_nonneg X.1.1
  have hm := competitionMonitorBad_nonneg X
  have hle : competitionOperatingFailure X ≤ 1 := by
    unfold competitionOperatingFailure FiniteKernel.eventIndicator
    split_ifs <;> norm_num
  by_cases hg : resourceGood (boxCounts (competitionCounts X.1.1)) V
  · by_cases hp : competitionPhase X.1.1=0
    · have hh : competitionNoEntry X.1.1=1 := by simp [competitionNoEntry,FiniteKernel.eventIndicator,hp,hg]
      linarith
    · by_cases hp2 : competitionPhase X.1.1=2
      · have hh := competition_tracked_return_exit X.1.1 hp2
        linarith
      · have hp1 : competitionPhase X.1.1=1 := by omega
        have hgood : competitionWindowGood X.1 := ⟨⟨hp2,hg⟩,hp1⟩
        cases hb : X.2 with
        | false =>
          have hh : competitionMonitorBad X=1 := by simp [competitionMonitorBad,FiniteKernel.eventIndicator,hgood,hb]
          linarith
        | true =>
          have hh : competitionOperatingFailure X=0 := by
            simp [competitionOperatingFailure,FiniteKernel.eventIndicator,hgood,hb]
          linarith
  · have hh := resourcePotential_exit V (boxCounts (competitionCounts X.1.1)) hg
    linarith

theorem competition_monitor_noentry_bound (eps k r delta : ℝ) (hV : 0 < (V:ℝ))
    (heps : 0 ≤ eps) (hk : 0 ≤ k) (hr : 0 ≤ r) (hd : 0 ≤ delta)
    (q : ℝ≥0) (hq : 0 < (q:ℝ))
    (hbound : ∀ X, (competitionWindowModel V C eps k r delta hV heps hk hr hd).total X ≤ q)
    (n : ℕ) (X : CompetitionMonitorState V C) :
    competitionMonitorSteps
      ((competitionWindowModel V C eps k r delta hV heps hk hr hd).uniformize q hq hbound) q n
      (fun Z => competitionNoEntry Z.1.1) X ≤ competitionNoEntry X.1.1 := by
  have hh := competition_monitor_source_foster eps k r delta hV heps hk hr hd q hq hbound
    competitionNoEntry competition_noentry_nonneg 0 le_rfl
    (competition_noentry_generator eps k r delta hV heps hk hr hd) n X
  simpa only [mul_zero,add_zero] using hh

end
end RandomViability.Binding
