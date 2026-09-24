import proofs.RandomViability.BindingCompetitionEntryProbability

namespace RandomViability.Binding
noncomputable section
open Classical FiniteCopy
open scoped BigOperators NNReal

def competitionEntryLift {V : ℕ} (f : BoxCounts V → ℝ) (X : CompetitionCounts V) : ℝ :=
  if competitionPhase X=0 then f (competitionCounts X) else 0

theorem competitionTrackedNext_phase {V : ℕ} (X : CompetitionCounts V)
    (j : CompetitionChannel) (h : competitionPhase X≠2) :
    competitionPhase (competitionTrackedNext X j) =
      scaledPhaseStep V (competitionPhase X)
        (weightedCount (boxCounts (boxNext V (competitionCounts X) (competitionBase j)))) := by
  unfold competitionTrackedNext
  rw [if_neg h]
  rfl

theorem competition_next_nezero {V : ℕ} (X : CompetitionCounts V)
    (j : CompetitionChannel) (h : competitionPhase X≠0) :
    competitionPhase (competitionTrackedNext X j) ≠ 0 := by
  by_cases h2 : competitionPhase X=2
  · simpa only [competitionTrackedNext,if_pos h2] using h
  · rw [competitionTrackedNext_phase X j h2]
    unfold scaledPhaseStep
    rw [if_neg h]
    split_ifs <;> decide

theorem competition_lift_next {V : ℕ} (f : BoxCounts V → ℝ)
    (hf : ∀ N, ¬entryActive V ((V:ℝ)/2500) N → f N=0)
    (X : CompetitionCounts V) (j : CompetitionChannel) (hp : competitionPhase X=0) :
    competitionEntryLift f (competitionTrackedNext X j) =
      f (boxNext V (competitionCounts X) (competitionBase j)) := by
  have hp2 : competitionPhase X≠2 := by omega
  simp only [competitionEntryLift,competitionTrackedNext_phase X j hp2,
    competitionTrackedNext_counts X j hp2,scaledPhaseStep,hp,if_true]
  by_cases hY : (V:ℝ)/2500≤weightedCount (boxCounts
      (boxNext V (competitionCounts X) (competitionBase j)))
  · have hn : ¬entryActive V ((V:ℝ)/2500)
        (boxNext V (competitionCounts X) (competitionBase j)) := by
      intro h
      exact (not_lt_of_ge hY) h.2
    simp [hY,hf _ hn]
  · simp [hY]

section Transport
variable (V : ℕ) (eps k r delta : ℝ) (hV : 0 < (V:ℝ))
    (heps : 0 ≤ eps) (hk : 0 ≤ k) (hr : 0 ≤ r) (hd : 0 ≤ delta)

theorem competition_lift_generator (f : BoxCounts V → ℝ)
    (hf : ∀ N, ¬entryActive V ((V:ℝ)/2500) N → f N=0) (X : CompetitionCounts V) :
    (competitionModel V eps k r delta hV heps hk hr hd).generator (competitionEntryLift f) X =
      competitionEntryLift ((competitionEntryModel V ((V:ℝ)/2500) eps k r delta
        hV heps hk hr hd).generator f) X := by
  by_cases hp : competitionPhase X=0
  · by_cases hg : resourceGood (boxCounts (competitionCounts X)) V
    · have hen : competitionEnabled X := ⟨by omega,hg⟩
      have hea : entryActive V ((V:ℝ)/2500) (competitionCounts X) := ⟨hg,X.property.1 hp⟩
      simp only [competitionEntryLift,if_pos hp]
      simp only [FiniteJumpModel.generator,competitionModel,competitionEntryModel,
        if_pos hen,if_pos hea]
      apply Finset.sum_congr rfl
      intro j _
      rw [competition_lift_next f hf X j hp]
      simp only [competitionEntryLift,if_pos hp]
    · have hen : ¬competitionEnabled X := fun h => hg h.2
      have hea : ¬entryActive V ((V:ℝ)/2500) (competitionCounts X) := fun h => hg h.1
      simp [competitionEntryLift,hp,FiniteJumpModel.generator,competitionModel,
        competitionEntryModel,hen,hea]
  · have hn (j : CompetitionChannel) := competition_next_nezero X j hp
    simp [FiniteJumpModel.generator,competitionModel,competitionEntryLift,hp,hn]

variable (q : ℝ) (hq : 0 < q)
    (hb : ∀ X, (competitionModel V eps k r delta hV heps hk hr hd).total X ≤ q)
    (he : ∀ N, (competitionEntryModel V ((V:ℝ)/2500) eps k r delta hV heps hk hr hd).total N ≤ q)

theorem competition_entry_step_outside (f : BoxCounts V → ℝ)
    (N : BoxCounts V) (h : ¬entryActive V ((V:ℝ)/2500) N) :
    ((competitionEntryModel V ((V:ℝ)/2500) eps k r delta hV heps hk hr hd).uniformize q hq he).step f N = f N := by
  simp [FiniteJumpModel.uniformize_step,FiniteJumpModel.generator,competitionEntryModel,h]

theorem competition_entry_steps_zero (f : BoxCounts V → ℝ)
    (hf : ∀ N, ¬entryActive V ((V:ℝ)/2500) N → f N=0) (n : ℕ)
    (N : BoxCounts V) (h : ¬entryActive V ((V:ℝ)/2500) N) :
    ((competitionEntryModel V ((V:ℝ)/2500) eps k r delta hV heps hk hr hd).uniformize q hq he).steps n f N = 0 := by
  induction n with
  | zero => exact hf N h
  | succ n ih =>
    rw [FiniteKernel.steps,competition_entry_step_outside V eps k r delta hV heps hk hr hd q hq he _ N h]
    exact ih

theorem competition_lift_step (f : BoxCounts V → ℝ)
    (hf : ∀ N, ¬entryActive V ((V:ℝ)/2500) N → f N=0) (X : CompetitionCounts V) :
    ((competitionModel V eps k r delta hV heps hk hr hd).uniformize q hq hb).step (competitionEntryLift f) X =
      competitionEntryLift (((competitionEntryModel V ((V:ℝ)/2500) eps k r delta
        hV heps hk hr hd).uniformize q hq he).step f) X := by
  rw [FiniteJumpModel.uniformize_step,
    competition_lift_generator V eps k r delta hV heps hk hr hd f hf]
  by_cases hp : competitionPhase X=0
  · simp only [competitionEntryLift,if_pos hp,FiniteJumpModel.uniformize_step]
  · simp only [competitionEntryLift,if_neg hp,zero_div,add_zero]

theorem competition_lift_steps (f : BoxCounts V → ℝ)
    (hf : ∀ N, ¬entryActive V ((V:ℝ)/2500) N → f N=0) (n : ℕ) (X : CompetitionCounts V) :
    ((competitionModel V eps k r delta hV heps hk hr hd).uniformize q hq hb).steps n (competitionEntryLift f) X =
      competitionEntryLift (((competitionEntryModel V ((V:ℝ)/2500) eps k r delta
        hV heps hk hr hd).uniformize q hq he).steps n f) X := by
  induction n generalizing X with
  | zero => rfl
  | succ n ih =>
    rw [FiniteKernel.steps,show
      ((competitionModel V eps k r delta hV heps hk hr hd).uniformize q hq hb).steps n (competitionEntryLift f) =
      competitionEntryLift (((competitionEntryModel V ((V:ℝ)/2500) eps k r delta
        hV heps hk hr hd).uniformize q hq he).steps n f) from funext ih]
    exact competition_lift_step V eps k r delta hV heps hk hr hd q hq hb he _
      (competition_entry_steps_zero V eps k r delta hV heps hk hr hd q hq he f hf n) X

end Transport
end
end RandomViability.Binding
