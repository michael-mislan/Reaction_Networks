import proofs.RAFQueryCompilation.ClosureCertificate

namespace RAFQueryCompilation
open RAF RAF.Frankl
variable {M R : Type*} [DecidableEq M] [Fintype M] [DecidableEq R]

def pruneWithPool (Q : CRS M R) (C : Catalysis M R) [∀ x r, Decidable (C x r)]
    (S : Finset R) (pool : Finset M) : Finset R :=
  S.filter (fun r => Q.inputs r ⊆ pool ∧ ∃ x ∈ pool, C x r)

theorem evaluate_of_fixed (Q : CRS M R) (C : Catalysis M R)
    [∀ x r, Decidable (C x r)] (A : Finset R) (h : executablePrune Q C A = A) :
    evaluate Q C A = A := by
  apply Finset.Subset.antisymm (evaluate_subset Q C A)
  apply supported_subset_evaluate Q C (Finset.Subset.refl _)
  exact fixed_supported Q C (by rwa [executablePrune_eq] at h)

theorem evaluate_prune (Q : CRS M R) (C : Catalysis M R)
    [∀ x r, Decidable (C x r)] (A : Finset R) :
    evaluate Q C (executablePrune Q C A) = evaluate Q C A := by
  apply Finset.Subset.antisymm
  · apply evaluate_mono Q C
    rw [executablePrune_eq]
    exact prune_subset Q C A
  · apply supported_subset_evaluate Q C
    · rw [executablePrune_eq, ← evaluate_fixed Q C A]
      exact prune_mono Q C (evaluate_subset Q C A)
    · exact fixed_supported Q C (evaluate_fixed Q C A)

/-- Each pruning round carries a food-closure firing order. A fixed round is mandatory. -/
def checkPruning (Q : CRS M R) (C : Catalysis M R) [∀ x r, Decidable (C x r)] :
    Finset R → List (List R) → Option (Finset R)
  | _, [] => none
  | A, order :: rest =>
    match checkClosure Q A order with
    | none => none
    | some pool =>
      let T := pruneWithPool Q C A pool
      if T = A then some A else checkPruning Q C T rest

theorem checkPruning_sound (Q : CRS M R) (C : Catalysis M R)
    [∀ x r, Decidable (C x r)] (cert : List (List R)) (A : Finset R)
    {answer : Finset R} (h : checkPruning Q C A cert = some answer) :
    answer = evaluate Q C A := by
  induction cert generalizing A with
  | nil => simp [checkPruning] at h
  | cons order rest ih =>
    cases hc : checkClosure Q A order with
    | none => simp [checkPruning, hc] at h
    | some pool =>
      have hp := checkClosure_sound Q A order hc
      subst pool
      simp only [checkPruning, hc] at h
      change (if executablePrune Q C A = A then some A else
        checkPruning Q C (executablePrune Q C A) rest) = some answer at h
      split at h
      next hf =>
        have ha := Option.some.inj h
        rw [← ha]
        exact (evaluate_of_fixed Q C A hf).symm
      next => exact (ih _ h).trans (evaluate_prune Q C A)

end RAFQueryCompilation
