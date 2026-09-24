import proofs.RandomViability.BindingResourceProbability
import proofs.RandomViability.BindingReturnPotential

namespace RandomViability.Binding
noncomputable section
open Classical FiniteCopy
open scoped BigOperators

/-- Phase0: not entered; phase1: entered and above the residence floor;
phase2: first return failure, whose physical counts are retained. -/
def phaseValid (Y : ℝ) (p : Fin 3) : Prop :=
  (p=0 → Y<40000) ∧ (p=1 → 20000≤Y) ∧ (p=2 → Y≤20000)

abbrev TrackedCounts := {p : BoxCounts 100000000 × Fin 3 //
  phaseValid (weightedCount (boxCounts p.1)) p.2}

def trackedCounts (X : TrackedCounts) : BoxCounts 100000000 := X.val.1
def trackedPhase (X : TrackedCounts) : Fin 3 := X.val.2

def phaseStep (p : Fin 3) (Y : ℝ) : Fin 3 :=
  if p=0 then (if 40000≤Y then 1 else 0) else (if Y<20000 then 2 else 1)

theorem phaseStep_valid (p : Fin 3) (Y : ℝ) : phaseValid Y (phaseStep p Y) := by
  by_cases hp : p=0
  · by_cases hY : 40000≤Y
    · simp [phaseStep,hp,hY,phaseValid]
      linarith
    · simp [phaseStep,hp,hY,phaseValid]
      linarith
  · by_cases hY : Y<20000
    · simp [phaseStep,hp,hY,phaseValid]
      linarith
    · simp [phaseStep,hp,hY,phaseValid]
      linarith

def trackedNext (X : TrackedCounts) (j : Fin 18) : TrackedCounts :=
  if trackedPhase X=2 then X else
    ⟨(boxNext 100000000 (trackedCounts X) j,
      phaseStep (trackedPhase X) (weightedCount (boxCounts (boxNext 100000000 (trackedCounts X) j)))),
      phaseStep_valid _ _⟩

theorem trackedNext_counts (X : TrackedCounts) (j : Fin 18) (h : trackedPhase X≠2) :
    trackedCounts (trackedNext X j) = boxNext 100000000 (trackedCounts X) j := by
  simp [trackedNext,h,trackedCounts]

theorem trackedNext_phase (X : TrackedCounts) (j : Fin 18) (h : trackedPhase X≠2) :
    trackedPhase (trackedNext X j) =
      phaseStep (trackedPhase X) (weightedCount (boxCounts (boxNext 100000000 (trackedCounts X) j))) := by
  unfold trackedNext
  rw [if_neg h]
  rfl

def trackingEnabled (X : TrackedCounts) : Prop :=
  trackedPhase X≠2 ∧ resourceGood (boxCounts (trackedCounts X)) 100000000

def trackedModel (eps k r : ℝ) (heps : 0 ≤ eps) (hk : 0 ≤ k) (hr : 0 ≤ r) :
    FiniteJumpModel TrackedCounts (Fin 18) where
  next := trackedNext
  rate X j := if trackingEnabled X then countRate (boxCounts (trackedCounts X)) 100000000 eps k r j else 0
  nonneg X j := by
    split_ifs
    · exact countRate_nonneg _ _ _ _ _ (by norm_num) heps hk hr j
    · rfl

theorem tracked_total_bound (eps k r : ℝ) (heps : 0 ≤ eps) (heps1 : eps ≤ 1)
    (hk : 0 ≤ k) (hk1 : k ≤ 1/8) (hr : 0 ≤ r) (hr1 : r ≤ 22) (X : TrackedCounts) :
    (trackedModel eps k r heps hk hr).total X ≤ 300000000000 := by
  by_cases h : trackingEnabled X
  · simp only [FiniteJumpModel.total,trackedModel,if_pos h]
    have hb := total_rate_bound (boxCounts (trackedCounts X)) 100000000 eps k r (by norm_num)
      heps heps1 hk hk1 hr hr1 (by
        intro i
        have hi := resource_count_cap (boxCounts (trackedCounts X)) 100000000 h.2 i
        norm_num at hi ⊢
        linarith)
    norm_num at hb
    exact hb
  · simp [FiniteJumpModel.total,trackedModel,h]

def trackedInitial : TrackedCounts := ⟨(foodInitial 100000000,0),by
  norm_num [phaseValid,foodInitial,boxCounts,weightedCount,weighted]⟩

theorem tracked_generator_inside (eps k r : ℝ) (heps : 0 ≤ eps) (hk : 0 ≤ k) (hr : 0 ≤ r)
    (X : TrackedCounts) (f : Counts → ℝ) (h : trackingEnabled X) :
    (trackedModel eps k r heps hk hr).generator (fun Z => f (boxCounts (trackedCounts Z))) X =
      literalGenerator (boxCounts (trackedCounts X)) 100000000 eps k r f := by
  simp only [FiniteJumpModel.generator,trackedModel,if_pos h,literalGenerator]
  apply Finset.sum_congr rfl
  intro j _
  rw [trackedNext_counts X j h.1,boxNext_exact 100000000 (trackedCounts X) j h.2]

theorem tracked_generator_outside (eps k r : ℝ) (heps : 0 ≤ eps) (hk : 0 ≤ k) (hr : 0 ≤ r)
    (X : TrackedCounts) (f : TrackedCounts → ℝ) (h : ¬trackingEnabled X) :
    (trackedModel eps k r heps hk hr).generator f X = 0 := by
  simp [FiniteJumpModel.generator,trackedModel,h]

end
end RandomViability.Binding
