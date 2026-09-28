import proofs.RAFInteriorRealizability.Main

/-!
Seed reduction for the sharp three-element RAF-family threshold.
A seed is an element whose singleton belongs to the antimatroid shell.
-/

namespace RAFInteriorRealizability

universe u

variable {E : Type u} [DecidableEq E]

/-- Every nonempty feasible set of an accessible family contains a feasible
singleton. This is the seed reduction used in the finite obstruction. -/
theorem AntimatroidData.exists_seed_in
    (A : AntimatroidData E) (S : Finset E)
    (hS : S ∈ A.family) (hne : S.Nonempty) :
    ∃ e ∈ S, ({e} : Finset E) ∈ A.family := by
  refine Finset.strongInductionOn S ?_ hS hne
  intro S ih hS hne
  obtain ⟨e, heS, hErase⟩ := A.accessible hS hne
  by_cases hEmpty : S.erase e = ∅
  · have hSingleton : S = {e} := by
      calc
        S = insert e (S.erase e) := (Finset.insert_erase heS).symm
        _ = {e} := by simp [hEmpty]
    exact ⟨e, heS, by simpa [hSingleton] using hS⟩
  · have hneErase : (S.erase e).Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hEmpty
    obtain ⟨x, hx, hSeed⟩ :=
      ih (S.erase e) (Finset.erase_ssubset heS) hErase hneErase
    exact ⟨x, (Finset.mem_erase.mp hx).2, hSeed⟩

/-- Any set made entirely of feasible singletons is feasible, by finite
union closure. -/
theorem AntimatroidData.mem_of_singletons_mem
    (A : AntimatroidData E) (S : Finset E)
    (hSeeds : ∀ e ∈ S, ({e} : Finset E) ∈ A.family) :
    S ∈ A.family := by
  induction S using Finset.induction_on with
  | empty => exact A.empty_mem
  | @insert e S he ih =>
      have hSeed : ({e} : Finset E) ∈ A.family :=
        hSeeds e (by simp)
      have hRest : ∀ x ∈ S, ({x} : Finset E) ∈ A.family := by
        intro x hx
        exact hSeeds x (by simp [hx])
      simpa using A.union_mem hSeed (ih hRest)

end RAFInteriorRealizability
