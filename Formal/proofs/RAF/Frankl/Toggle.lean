import proofs.RAF.Core.Seed
import proofs.RAF.Frankl.Semantics

namespace RAF.Frankl

open RAF

variable {M R : Type*} [DecidableEq M] [DecidableEq R]

/-- A reaction is universally addable when inserting it into any RAF that
omits it again gives a RAF. -/
def UniversallyAddable (Q : CRS M R) (C : Catalysis M R) (r : R) : Prop :=
  ∀ S : Finset R, IsRAF Q C S → r ∉ S → IsRAF Q C (insert r S)

theorem frequency_eq_filter_card
    (Q : CRS M R) (C : Catalysis M R) [Fintype R] (r : R) :
    frequency Q C r = ((rafFamily Q C).filter fun S => r ∈ S).card := by
  classical
  unfold frequency
  congr 1
  ext S
  simp

/-- The add-one map is an injection from RAFs omitting a universally addable
reaction into RAFs containing it. -/
theorem universallyAddable_card_omitting_le_frequency
    (Q : CRS M R) (C : Catalysis M R) [Fintype R]
    {r : R} (hadd : UniversallyAddable Q C r) :
    ((rafFamily Q C).filter fun S => r ∉ S).card ≤ frequency Q C r := by
  classical
  let omitted := (rafFamily Q C).filter fun S => r ∉ S
  let present := (rafFamily Q C).filter fun S => r ∈ S
  have hmap : Set.MapsTo (fun S : Finset R => insert r S) omitted present := by
    intro S hS
    simp [omitted] at hS
    have hnew : IsRAF Q C (insert r S) := hadd S hS.1 hS.2
    simp [present, hnew]
  have hinj : (omitted : Set (Finset R)).InjOn (fun S => insert r S) := by
    intro A hA B hB hEq
    simp [omitted] at hA hB
    have hErase := congrArg (fun S : Finset R => S.erase r) hEq
    simpa [hA.2, hB.2] using hErase
  have hcard : omitted.card ≤ present.card :=
    Finset.card_le_card_of_injOn _ hmap hinj
  rw [frequency_eq_filter_card]
  simpa [omitted, present] using hcard

/-- A universally addable reaction occurs in at least half of all nonempty
RAFs. -/
theorem universallyAddable_implies_abundant
    (Q : CRS M R) (C : Catalysis M R) [Fintype R]
    {r : R} (hadd : UniversallyAddable Q C r) :
    (rafFamily Q C).card ≤ 2 * frequency Q C r := by
  classical
  have homit := universallyAddable_card_omitting_le_frequency Q C hadd
  rw [frequency_eq_filter_card] at homit ⊢
  calc
    (rafFamily Q C).card =
        ((rafFamily Q C).filter fun S => r ∈ S).card +
        ((rafFamily Q C).filter fun S => r ∉ S).card := by
          symm
          exact Finset.card_filter_add_card_filter_not
            (s := rafFamily Q C) (p := fun S => r ∈ S)
    _ ≤ ((rafFamily Q C).filter fun S => r ∈ S).card +
        ((rafFamily Q C).filter fun S => r ∈ S).card :=
          Nat.add_le_add_left homit _
    _ = 2 * ((rafFamily Q C).filter fun S => r ∈ S).card := by omega

theorem exists_universallyAddable_implies_steelRAFHalf
    (Q : CRS M R) (C : Catalysis M R) [Fintype R]
    (hadd : ∃ r : R, UniversallyAddable Q C r) : SteelRAFHalf Q C := by
  rintro _
  obtain ⟨r, hr⟩ := hadd
  exact ⟨r, universallyAddable_implies_abundant Q C hr⟩

end RAF.Frankl
