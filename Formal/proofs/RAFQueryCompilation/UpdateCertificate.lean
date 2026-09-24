import proofs.RAFQueryCompilation.PruningCertificate

namespace RAFQueryCompilation
open RAF
variable {M R : Type*} [DecidableEq M] [Fintype M] [DecidableEq R] [Fintype R]

def checkUpdate (Q : CRS M R) (C : Catalysis M R) [∀ x r, Decidable (C x r)]
    (oldAnswer B D : Finset R) (certificate : List (List R)) : Option (Finset R) :=
  let E := dependencyCone Q C D
  match checkPruning (withFood Q (cachedFood Q C oldAnswer E)) C (B ∩ E) certificate with
  | none => none
  | some localAnswer => some ((oldAnswer \ E) ∪ localAnswer)

/-- Accepted local solver evidence certifies the whole-network updated maximum. -/
theorem checkUpdate_sound (Q : CRS M R) (C : Catalysis M R)
    [∀ x r, Decidable (C x r)] (A B D : Finset R) (certificate : List (List R))
    (hc : ∀ r, (r ∈ A ↔ r ∈ B) ∨ r ∈ D) {answer : Finset R}
    (h : checkUpdate Q C (evaluate Q C A) B D certificate = some answer) :
    answer = evaluate Q C B := by
  dsimp only [checkUpdate] at h
  cases hp : checkPruning
      (withFood Q (cachedFood Q C (evaluate Q C A) (dependencyCone Q C D))) C
      (B ∩ dependencyCone Q C D) certificate with
  | none => simp only [hp] at h; contradiction
  | some localAnswer =>
    simp only [hp] at h
    have hl := checkPruning_sound _ C certificate _ hp
    have ha := Option.some.inj h
    rw [← ha, hl]
    exact compiledUpdate_correct Q C A B D hc

end RAFQueryCompilation
