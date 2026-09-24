import proofs.RAFQueryCompilation.PruningCertificate

namespace RAFQueryCompilation
open RAF
variable {M R : Type*} [DecidableEq M] [DecidableEq R]

/-- Counts the rounds actually entered, including a rejected or terminal round.
It follows the same tests and recursive calls as `checkPruning`. -/
def pruningRounds (Q : CRS M R) (C : Catalysis M R) [∀ x r, Decidable (C x r)] :
    Finset R → List (List R) → ℕ
  | _, [] => 0
  | A, order :: rest =>
    match checkClosure Q A order with
    | none => 1
    | some pool =>
      let T := pruneWithPool Q C A pool
      if T = A then 1 else 1 + pruningRounds Q C T rest

theorem pruningRounds_le (Q : CRS M R) (C : Catalysis M R)
    [∀ x r, Decidable (C x r)] (cert : List (List R)) (A : Finset R) :
    pruningRounds Q C A cert ≤ A.card + 1 := by
  induction cert generalizing A with
  | nil => simp [pruningRounds]
  | cons order rest ih =>
    cases hc : checkClosure Q A order with
    | none => simp [pruningRounds, hc]
    | some pool =>
      have hs : pruneWithPool Q C A pool ⊆ A := Finset.filter_subset _ _
      by_cases he : pruneWithPool Q C A pool = A
      · simp [pruningRounds, hc, he]
      · have hlt : (pruneWithPool Q C A pool).card < A.card :=
          Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hs, he⟩)
        have hi := ih (pruneWithPool Q C A pool)
        simp only [pruningRounds, hc, if_neg he]
        omega

/-- One active-set scan budget per entered round. Closure closedness and pruning
each use such a scan; membership, incidence and copying costs are separate. -/
def pruningRows (Q : CRS M R) (C : Catalysis M R) [∀ x r, Decidable (C x r)] :
    Finset R → List (List R) → ℕ
  | _, [] => 0
  | A, order :: rest =>
    match checkClosure Q A order with
    | none => A.card
    | some pool =>
      let T := pruneWithPool Q C A pool
      if T = A then A.card else A.card + pruningRows Q C T rest

theorem pruningRows_le_rounds (Q : CRS M R) (C : Catalysis M R)
    [∀ x r, Decidable (C x r)] (cert : List (List R)) (A : Finset R) :
    pruningRows Q C A cert ≤ A.card * pruningRounds Q C A cert := by
  induction cert generalizing A with
  | nil => simp [pruningRows, pruningRounds]
  | cons order rest ih =>
    cases hc : checkClosure Q A order with
    | none => simp [pruningRows, pruningRounds, hc]
    | some pool =>
      by_cases he : pruneWithPool Q C A pool = A
      · simp [pruningRows, pruningRounds, hc, he]
      · have hs : (pruneWithPool Q C A pool).card ≤ A.card :=
          Finset.card_le_card (Finset.filter_subset _ _)
        have hi := (ih (pruneWithPool Q C A pool)).trans
          (Nat.mul_le_mul_right (pruningRounds Q C (pruneWithPool Q C A pool) rest) hs)
        simp only [pruningRows, pruningRounds, hc, if_neg he]
        nlinarith

theorem pruningRows_le (Q : CRS M R) (C : Catalysis M R)
    [∀ x r, Decidable (C x r)] (cert : List (List R)) (A : Finset R) :
    pruningRows Q C A cert ≤ A.card * (A.card + 1) :=
  (pruningRows_le_rounds Q C cert A).trans
    (Nat.mul_le_mul_left A.card (pruningRounds_le Q C cert A))

end RAFQueryCompilation
