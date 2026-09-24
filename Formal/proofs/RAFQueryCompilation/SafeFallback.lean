import proofs.RAFQueryCompilation.MaskCertificate

namespace RAFQueryCompilation
open RAF
variable {M R : Type*} [DecidableEq M] [Fintype M] [DecidableEq R]

/-- An aborted proposal or a rejected certificate uses fresh evaluation.
The proposal generator may apply any discovery budget; it has no proof authority. -/
def safeEvaluate (Q : CRS M R) (C : Catalysis M R) [∀ x r, Decidable (C x r)]
    (succ : R → Finset R) (needs : R → Finset M)
    (oldAnswer B D : Finset R) (oldMask availableMask : R → Bool)
    (counts : M → ℕ) (proposal : Option (Finset R × List (List R))) : Finset R :=
  match proposal with
  | none => evaluate Q C B
  | some (E,cert) =>
    match checkMaskedLocal Q C succ needs oldMask availableMask D E counts cert with
    | none => evaluate Q C B
    | some L => (oldAnswer \ E) ∪ L

theorem safeEvaluate_correct (Q : CRS M R) (C : Catalysis M R)
    [∀ x r, Decidable (C x r)] (succ : R → Finset R) (needs : R → Finset M)
    (hi : IndexSound Q C succ) (hn : NeedsSound Q C needs)
    (A B D : Finset R) (oldMask availableMask : R → Bool) (counts : M → ℕ)
    (ho : ∀ r, oldMask r = true ↔ r ∈ evaluate Q C A)
    (ha : ∀ r, availableMask r = true ↔ r ∈ B)
    (hc : ∀ x, counts x = producerCount Q (evaluate Q C A) x)
    (hedits : ∀ r, (r ∈ A ↔ r ∈ B) ∨ r ∈ D)
    (proposal : Option (Finset R × List (List R))) :
    safeEvaluate Q C succ needs (evaluate Q C A) B D oldMask availableMask counts proposal =
      evaluate Q C B := by
  cases proposal with
  | none => rfl
  | some proposal =>
    rcases proposal with ⟨E,cert⟩
    dsimp only [safeEvaluate]
    cases h : checkMaskedLocal Q C succ needs oldMask availableMask D E counts cert with
    | none => rfl
    | some L =>
      exact (checkMaskedLocal_sound Q C succ needs hi hn A B D E counts cert
        oldMask availableMask ho ha hc hedits h).symm

end RAFQueryCompilation
