import proofs.RAFQueryCompilation.StateTransition
import proofs.RAFQueryCompilation.MeteredPruning

namespace RAFQueryCompilation
open RAF
variable {M R : Type*} [DecidableEq M] [DecidableEq R]

def meterLocal (Q : CRS M R) (C : Catalysis M R)
    [∀ x r, Decidable (C x r)] (succ : R → Finset R) (needs : R → Finset M)
    (oldMask availableMask : R → Bool) (D E : Finset R)
    (counts : M → ℕ) (certificate : List (List R)) : PruningMeter R :=
  if checkRegion succ D E then
    meterPruning (withFood Q (maskFood Q needs E oldMask counts)) C
      (maskRegion E availableMask) certificate
  else ⟨none, 0, 0, 0⟩

theorem meterLocal_refines [Fintype M] (Q : CRS M R) (C : Catalysis M R)
    [∀ x r, Decidable (C x r)] (succ : R → Finset R) (needs : R → Finset M)
    (oldMask availableMask : R → Bool) (D E : Finset R)
    (counts : M → ℕ) (certificate : List (List R)) :
    (meterLocal Q C succ needs oldMask availableMask D E counts certificate).answer =
      checkMaskedLocal Q C succ needs oldMask availableMask D E counts certificate := by
  simp only [meterLocal, checkMaskedLocal]
  split
  · exact (meterPruning_refines _ _ _ _).1
  · rfl

theorem meterLocal_bounds (Q : CRS M R) (C : Catalysis M R)
    [∀ x r, Decidable (C x r)] (succ : R → Finset R) (needs : R → Finset M)
    (oldMask availableMask : R → Bool) (D E : Finset R)
    (counts : M → ℕ) (certificate : List (List R)) :
    let result := meterLocal Q C succ needs oldMask availableMask D E counts certificate
    result.rounds ≤ E.card + 1 ∧ result.rowBudget ≤ E.card * (E.card + 1) ∧
      result.replayEntries ≤ certificate.flatten.length := by
  simp only [meterLocal]
  split
  · rcases meterPruning_bounds (withFood Q (maskFood Q needs E oldMask counts)) C
        certificate (maskRegion E availableMask) with ⟨hr,hw,he⟩
    have hs : (maskRegion E availableMask).card ≤ E.card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    refine ⟨by omega, ?_, he⟩
    exact hw.trans (Nat.mul_le_mul hs (Nat.add_le_add_right hs 1))
  · simp

end RAFQueryCompilation
