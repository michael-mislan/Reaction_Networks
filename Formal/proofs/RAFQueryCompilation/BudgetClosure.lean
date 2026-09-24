import proofs.RAFQueryCompilation.BudgetReplay
import proofs.RAFQueryCompilation.ChargedClosure

namespace RAFQueryCompilation
open RAF
variable {M R : Type*} [DecidableEq M] [DecidableEq R]

def terminalCap (e i o p : ℕ) : ℕ :=
  1+e*((i+1)*(p+1))+2*(p+e*o+1)^2

/-- Unbudgeted reference with a metadata-derived terminal reservation. -/
def cappedClosure (Q : CRS M R) (A : Finset R) (order : List R) (i o : ℕ) :
    Option (Finset M) × ℕ :=
  let replay := chargedReplayFrom Q A order Q.food
  (if closureStep Q A replay.1 = replay.1 then some replay.1 else none,
    Q.food.card+replay.2+terminalCap A.card i o replay.1.card)

def budgetClosure (Q : CRS M R) (A : Finset R) (order : List R)
    (i o budget : ℕ) : Option (Finset M) × ℕ :=
  if Q.food.card ≤ budget then
    let replay := budgetReplayFrom Q A order Q.food (budget-Q.food.card)
    match replay.1 with
    | none => (none,Q.food.card+replay.2)
    | some pool =>
      let fee := Q.food.card+replay.2+terminalCap A.card i o pool.card
      if fee ≤ budget then
        (if closureStep Q A pool = pool then some pool else none,fee)
      else (none,Q.food.card+replay.2)
  else (none,0)

theorem cappedClosure_refines (Q : CRS M R) (A : Finset R) (order : List R) (i o : ℕ) :
    (cappedClosure Q A order i o).1 = checkClosure Q A order := by
  simp only [cappedClosure, chargedReplay_refines, checkClosure, replaySchedule]

theorem cappedClosure_covers_charge (Q : CRS M R) (A : Finset R) (order : List R)
    (i o : ℕ) (hi : ∀ r ∈ A, (Q.inputs r).card ≤ i)
    (ho : ∀ r ∈ A, (Q.outputs r).card ≤ o) :
    (chargedClosure Q A order).2 ≤ (cappedClosure Q A order i o).2 := by
  have ht := closureTerminalCharge_le Q A (chargedReplayFrom Q A order Q.food).1
    A.card i o (chargedReplayFrom Q A order Q.food).1.card (Nat.le_refl _)
    (Nat.le_refl _) hi ho
  dsimp only [chargedClosure, cappedClosure, terminalCap]
  exact Nat.add_le_add_left ht _

theorem budgetClosure_bound (Q : CRS M R) (A : Finset R) (order : List R)
    (i o budget : ℕ) : (budgetClosure Q A order i o budget).2 ≤ budget := by
  have hr := budgetReplay_bound Q A order Q.food (budget-Q.food.card)
  by_cases hf : Q.food.card ≤ budget
  · simp only [budgetClosure, if_pos hf]
    cases h : (budgetReplayFrom Q A order Q.food (budget-Q.food.card)).1 with
    | none => simp only []; omega
    | some pool =>
      simp only []
      split_ifs <;> simp_all only
      omega
  · simp [budgetClosure, hf]

theorem budgetClosure_refines (Q : CRS M R) (A : Finset R) (order : List R)
    (i o budget : ℕ) {pool : Finset M}
    (h : (budgetClosure Q A order i o budget).1 = some pool) :
    checkClosure Q A order = some pool := by
  dsimp only [budgetClosure] at h
  split at h
  · cases hr : (budgetReplayFrom Q A order Q.food (budget-Q.food.card)).1 with
    | none => simp [hr] at h
    | some out =>
      simp only [hr] at h
      split at h
      · have hp := budgetReplay_refines Q A order Q.food (budget-Q.food.card) hr
        simpa only [checkClosure, replaySchedule, ← hp] using h
      · simp at h
  · simp at h

theorem budgetClosure_complete (Q : CRS M R) (A : Finset R) (order : List R)
    (i o budget : ℕ) (h : (cappedClosure Q A order i o).2 ≤ budget) :
    budgetClosure Q A order i o budget = cappedClosure Q A order i o := by
  have hf : Q.food.card ≤ budget := by dsimp only [cappedClosure] at h; omega
  have hr : (chargedReplayFrom Q A order Q.food).2 ≤ budget-Q.food.card := by
    dsimp only [cappedClosure] at h
    omega
  have he := budgetReplay_complete Q A order Q.food (budget-Q.food.card) hr
  dsimp only [budgetClosure]
  rw [if_pos hf, he]
  dsimp only
  exact if_pos h

end RAFQueryCompilation
