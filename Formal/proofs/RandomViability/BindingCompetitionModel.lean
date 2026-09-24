import proofs.RandomViability.BindingCompetitionBookkeeping
import proofs.RandomViability.BindingCompetitionExponential

namespace RandomViability.Binding
noncomputable section
open Classical FiniteCopy
open scoped BigOperators

def scaledPhaseValid (V : ℕ) (Y : ℝ) (p : Fin 3) : Prop :=
  (p=0 → Y<(V:ℝ)/2500) ∧ (p=1 → (V:ℝ)/5000≤Y) ∧
    (p=2 → Y≤(V:ℝ)/5000)

abbrev CompetitionCounts (V : ℕ) := {p : BoxCounts V × Fin 3 //
  scaledPhaseValid V (weightedCount (boxCounts p.1)) p.2}

def competitionCounts {V : ℕ} (X : CompetitionCounts V) : BoxCounts V := X.val.1
def competitionPhase {V : ℕ} (X : CompetitionCounts V) : Fin 3 := X.val.2

def scaledPhaseStep (V : ℕ) (p : Fin 3) (Y : ℝ) : Fin 3 :=
  if p=0 then (if (V:ℝ)/2500≤Y then 1 else 0)
  else (if Y<(V:ℝ)/5000 then 2 else 1)

theorem scaledPhaseStep_valid (V : ℕ) (p : Fin 3) (Y : ℝ) :
    scaledPhaseValid V Y (scaledPhaseStep V p Y) := by
  have hV : 0 ≤ (V:ℝ) := Nat.cast_nonneg _
  by_cases hp : p=0
  · by_cases hY : (V:ℝ)/2500≤Y
    · simp [scaledPhaseStep,hp,hY,scaledPhaseValid]
      linarith
    · simp [scaledPhaseStep,hp,hY,scaledPhaseValid]
      linarith
  · by_cases hY : Y<(V:ℝ)/5000
    · simp [scaledPhaseStep,hp,hY,scaledPhaseValid]
      linarith
    · simp [scaledPhaseStep,hp,hY,scaledPhaseValid]
      linarith

def competitionTrackedNext {V : ℕ} (X : CompetitionCounts V)
    (j : CompetitionChannel) : CompetitionCounts V :=
  if competitionPhase X=2 then X else
    ⟨(boxNext V (competitionCounts X) (competitionBase j),
      scaledPhaseStep V (competitionPhase X)
        (weightedCount (boxCounts (boxNext V (competitionCounts X) (competitionBase j))))),
      scaledPhaseStep_valid _ _ _⟩

def competitionEnabled {V : ℕ} (X : CompetitionCounts V) : Prop :=
  competitionPhase X≠2 ∧ resourceGood (boxCounts (competitionCounts X)) V

def competitionModel (V : ℕ) (eps k r delta : ℝ) (hV : 0 < (V:ℝ))
    (heps : 0 ≤ eps) (hk : 0 ≤ k) (hr : 0 ≤ r) (hd : 0 ≤ delta) :
    FiniteJumpModel (CompetitionCounts V) CompetitionChannel where
  next := competitionTrackedNext
  rate X j := if competitionEnabled X then
    competitionRate (boxCounts (competitionCounts X)) V eps k r delta j else 0
  nonneg X j := by
    split_ifs
    · exact competitionRate_nonneg _ _ _ _ _ _ hV heps hk hr hd j
    · rfl

theorem competitionTrackedNext_counts {V : ℕ} (X : CompetitionCounts V)
    (j : CompetitionChannel) (h : competitionPhase X≠2) :
    competitionCounts (competitionTrackedNext X j) =
      boxNext V (competitionCounts X) (competitionBase j) := by
  simp [competitionTrackedNext,h,competitionCounts]

theorem competition_model_inside (V : ℕ) (eps k r delta : ℝ) (hV : 0 < (V:ℝ))
    (heps : 0 ≤ eps) (hk : 0 ≤ k) (hr : 0 ≤ r) (hd : 0 ≤ delta)
    (X : CompetitionCounts V) (f : Counts → ℝ) (h : competitionEnabled X) :
    (competitionModel V eps k r delta hV heps hk hr hd).generator
      (fun Z => f (boxCounts (competitionCounts Z))) X =
    competitionGenerator (boxCounts (competitionCounts X)) V eps k r delta f := by
  simp only [FiniteJumpModel.generator,competitionModel,if_pos h,competitionGenerator]
  apply Finset.sum_congr rfl
  intro j _
  rw [competitionTrackedNext_counts X j h.1,boxNext_exact V (competitionCounts X)
    (competitionBase j) h.2]
  rfl

theorem competition_model_total (V : ℕ) (eps k r delta : ℝ) (hV : 0 < (V:ℝ))
    (heps : 0 ≤ eps) (heps1 : eps ≤ 1) (hk : 0 ≤ k) (hk1 : k ≤ 1/8)
    (hr : 0 ≤ r) (hr1 : r ≤ 22) (hd : 0 ≤ delta) (hd1 : delta ≤ 3/5)
    (X : CompetitionCounts V) :
    (competitionModel V eps k r delta hV heps hk hr hd).total X ≤ 3000*V := by
  by_cases h : competitionEnabled X
  · simp only [FiniteJumpModel.total,competitionModel,if_pos h]
    apply competition_total_rate_bound _ _ _ _ _ _ hV heps heps1 hk hk1 hr hr1 hd hd1
    intro i
    have hi := resource_count_cap (boxCounts (competitionCounts X)) V h.2 i
    nlinarith [Nat.cast_nonneg (α := ℝ) V]
  · simp [FiniteJumpModel.total,competitionModel,h]

end
end RandomViability.Binding
