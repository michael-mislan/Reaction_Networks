import proofs.RAFQueryCompilation.PruningWork

namespace RAFQueryCompilation
open RAF
variable {M R : Type*} [DecidableEq M] [DecidableEq R]

structure PruningMeter (R : Type*) where
  answer : Option (Finset R)
  rounds : ℕ
  rowBudget : ℕ
  replayEntries : ℕ

/-- Executes the checker once and returns its branch-following work counters.
The row field is a scan budget, not a unit-cost assumption for finite sets. -/
def meterPruning (Q : CRS M R) (C : Catalysis M R) [∀ x r, Decidable (C x r)] :
    Finset R → List (List R) → PruningMeter R
  | _, [] => ⟨none, 0, 0, 0⟩
  | A, order :: rest =>
    match checkClosure Q A order with
    | none => ⟨none, 1, A.card, order.length⟩
    | some pool =>
      let T := pruneWithPool Q C A pool
      if T = A then ⟨some A, 1, A.card, order.length⟩ else
        let tail := meterPruning Q C T rest
        ⟨tail.answer, 1 + tail.rounds, A.card + tail.rowBudget,
          order.length + tail.replayEntries⟩

theorem meterPruning_refines (Q : CRS M R) (C : Catalysis M R)
    [∀ x r, Decidable (C x r)] (cert : List (List R)) (A : Finset R) :
    (meterPruning Q C A cert).answer = checkPruning Q C A cert ∧
    (meterPruning Q C A cert).rounds = pruningRounds Q C A cert ∧
    (meterPruning Q C A cert).rowBudget = pruningRows Q C A cert := by
  induction cert generalizing A with
  | nil => simp [meterPruning, checkPruning, pruningRounds, pruningRows]
  | cons order rest ih =>
    cases hc : checkClosure Q A order with
    | none => simp [meterPruning, checkPruning, pruningRounds, pruningRows, hc]
    | some pool =>
      by_cases he : pruneWithPool Q C A pool = A
      · simp [meterPruning, checkPruning, pruningRounds, pruningRows, hc, he]
      · rcases ih (pruneWithPool Q C A pool) with ⟨ha, hr, hw⟩
        simp [meterPruning, checkPruning, pruningRounds, pruningRows, hc, he, ha, hr, hw]

theorem meterPruning_entries_le (Q : CRS M R) (C : Catalysis M R)
    [∀ x r, Decidable (C x r)] (cert : List (List R)) (A : Finset R) :
    (meterPruning Q C A cert).replayEntries ≤ cert.flatten.length := by
  induction cert generalizing A with
  | nil => simp [meterPruning]
  | cons order rest ih =>
    cases hc : checkClosure Q A order with
    | none => simp [meterPruning, hc]
    | some pool =>
      by_cases he : pruneWithPool Q C A pool = A
      · simp [meterPruning, hc, he]
      · simpa only [meterPruning, hc, if_neg he, List.flatten_cons, List.length_append]
          using Nat.add_le_add_left (ih (pruneWithPool Q C A pool)) order.length

theorem meterPruning_bounds (Q : CRS M R) (C : Catalysis M R)
    [∀ x r, Decidable (C x r)] (cert : List (List R)) (A : Finset R) :
    (meterPruning Q C A cert).rounds ≤ A.card + 1 ∧
    (meterPruning Q C A cert).rowBudget ≤ A.card * (A.card + 1) ∧
    (meterPruning Q C A cert).replayEntries ≤ cert.flatten.length := by
  rcases meterPruning_refines Q C cert A with ⟨_, hr, hw⟩
  exact ⟨hr ▸ pruningRounds_le Q C cert A,
    hw ▸ pruningRows_le Q C cert A, meterPruning_entries_le Q C cert A⟩

end RAFQueryCompilation
