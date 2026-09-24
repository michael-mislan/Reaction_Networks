import proofs.RandomViability.BindingCompetitionTrackedEntry

namespace RandomViability.Binding
noncomputable section
open Classical FiniteCopy
open scoped BigOperators NNReal

theorem competition_no_entry_indicator (V : ℕ) :
    FiniteKernel.eventIndicator {X : CompetitionCounts V | competitionPhase X=0 ∧
      resourceGood (boxCounts (competitionCounts X)) V} =
      competitionEntryLift (FiniteKernel.eventIndicator {N | entryActive V ((V:ℝ)/2500) N}) := by
  funext X
  by_cases hp : competitionPhase X=0
  · have hY : weightedCount (boxCounts (competitionCounts X)) < (V:ℝ)/2500 := X.property.1 hp
    simp [FiniteKernel.eventIndicator,competitionEntryLift,hp,entryActive,hY]
  · simp [FiniteKernel.eventIndicator,competitionEntryLift,hp]

theorem competition_entry_poissonized (V : ℕ) (eps k r delta : ℝ)
    (hV : 0 < (V:ℝ)) (heps : 0 ≤ eps) (hk : 0 ≤ k) (hr : 0 ≤ r) (hd : 0 ≤ delta)
    (q t : ℝ≥0) (hq : 0 < (q:ℝ))
    (hb : ∀ X, (competitionModel V eps k r delta hV heps hk hr hd).total X ≤ q)
    (he : ∀ N, (competitionEntryModel V ((V:ℝ)/2500) eps k r delta hV heps hk hr hd).total N ≤ q)
    (X : CompetitionCounts V) (hp : competitionPhase X=0) :
    ((competitionModel V eps k r delta hV heps hk hr hd).uniformize q hq hb).poissonized t
      (FiniteKernel.eventIndicator {Z | competitionPhase Z=0 ∧ resourceGood (boxCounts (competitionCounts Z)) V}) X =
    ((competitionEntryModel V ((V:ℝ)/2500) eps k r delta hV heps hk hr hd).uniformize q hq he).poissonized t
      (FiniteKernel.eventIndicator {N | entryActive V ((V:ℝ)/2500) N}) (competitionCounts X) := by
  rw [competition_no_entry_indicator]
  have hf (N : BoxCounts V) (h : ¬entryActive V ((V:ℝ)/2500) N) :
      FiniteKernel.eventIndicator {N | entryActive V ((V:ℝ)/2500) N} N=0 := by
    simp [FiniteKernel.eventIndicator,h]
  unfold FiniteKernel.poissonized
  apply tsum_congr
  intro n
  rw [competition_lift_steps V eps k r delta hV heps hk hr hd q hq hb he _ hf]
  simp [competitionEntryLift,hp]

theorem competition_tracked_entry_deadline (V q : ℕ) (eps k r delta : ℝ)
    (hV : 0 < (V:ℝ)) (heps : 0 ≤ eps) (heps1 : eps ≤ 1/1000000)
    (hk : 0 ≤ k) (hk1 : k ≤ 1/8) (hr : 18 ≤ r) (hr1 : r ≤ 22)
    (hd : 0 ≤ delta) (hd1 : delta ≤ 3/5) (hq : 0 < q)
    (hb : ∀ X, (competitionModel V eps k r delta hV heps hk (by linarith) hd).total X ≤ q)
    (he : ∀ N, (competitionEntryModel V ((V:ℝ)/2500) eps k r delta hV heps hk (by linarith) hd).total N ≤ q)
    (X : CompetitionCounts V) (hp : competitionPhase X=0) :
    ((competitionModel V eps k r delta hV heps hk (by linarith) hd).uniformize q
      (by exact_mod_cast hq) hb).poissonized ((q:ℝ≥0)*500)
      (FiniteKernel.eventIndicator {Z | competitionPhase Z=0 ∧ resourceGood (boxCounts (competitionCounts Z)) V}) X ≤
      Real.exp ((V:ℝ)/2500/40000-399*((14/25)*eps*V*(2/25)))+Real.exp (-(q:ℝ)/500000) := by
  have h := competition_entry_poissonized V eps k r delta hV heps hk (by linarith) hd q
    ((q:ℝ≥0)*500) (by exact_mod_cast hq) hb he X hp
  norm_num only [NNReal.coe_natCast] at h
  rw [h]
  exact competition_entry_deadline V q ((V:ℝ)/2500) eps k r delta hV heps heps1 hk hk1
    hr hr1 hd hd1 (by linarith) hq he _

theorem competition_entry_exponent (V : ℝ) :
    V/2500/40000-399*((14/25)*(1/500000000)*V*(2/25)) = -(8047/312500000000)*V := by
  ring

end
end RandomViability.Binding
