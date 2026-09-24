import proofs.RAFInteriorRealizability.PredSupport

namespace RAFInteriorRealizability

open RAF RAF.Frankl

universe u v

variable {M : Type u} {E : Type v} [DecidableEq M]
  [Fintype E] [DecidableEq E]

/-- A finite antimatroid, in the accessible union-closed presentation used by
food generation. -/
structure AntimatroidData (E : Type v) [DecidableEq E]
    extends UnionClosedData E where
  accessible : ∀ {S}, S ∈ family → S.Nonempty →
    ∃ e ∈ S, S.erase e ∈ family

noncomputable def foodGeneratedFamily (Q : CRS M E) : Finset (Finset E) := by
  classical
  exact Finset.univ.powerset.filter (FoodGenerated Q)

omit [DecidableEq E] in
@[simp] theorem mem_foodGeneratedFamily (Q : CRS M E) (S : Finset E) :
    S ∈ foodGeneratedFamily Q ↔ FoodGenerated Q S := by
  classical
  simp [foodGeneratedFamily]

noncomputable def foodGeneratedAntimatroid (Q : CRS M E) : AntimatroidData E where
  family := foodGeneratedFamily Q
  empty_mem := by simp
  union_mem := by
    intro S T hS hT
    rw [mem_foodGeneratedFamily] at hS hT ⊢
    exact foodGenerated_union Q hS hT
  accessible := by
    intro S hS hne
    have hfg : FoodGenerated Q S := (mem_foodGeneratedFamily Q S).1 hS
    obtain ⟨e, he, herase⟩ := foodGenerated_accessible Q hne hfg
    exact ⟨e, he, (mem_foodGeneratedFamily Q (S.erase e)).2 herase⟩

theorem fixedFamily_iff_foodGenerated_and_predSupported
    (Q : CRS M E) (C : Catalysis M E) (S : Finset E) :
    S ∈ fixedFamily Q C ↔
      S ∈ (foodGeneratedAntimatroid Q).family ∧
        PredSupported (extractedPredecessors Q C) S := by
  rw [mem_fixedFamily]
  simp only [foodGeneratedAntimatroid]
  rw [mem_foodGeneratedFamily]
  by_cases hS : S = ∅
  · subst S
    simp [PredSupported]
  · rw [isRAF_iff_foodGenerated_and_productGraph,
      productGraphCatalyzed_iff_predSupported]
    have hne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS
    simp [hS, hne]

/-- Bundled necessity direction for one literal source system. -/
theorem literalRealization_has_foodSupport
    (Q : CRS M E) (C : Catalysis M E) :
    ∃ A : AntimatroidData E, ∃ P : E → Finset E,
      ∀ S : Finset E,
        S ∈ fixedFamily Q C ↔ S ∈ A.family ∧ PredSupported P S := by
  exact ⟨foodGeneratedAntimatroid Q, extractedPredecessors Q C,
    fixedFamily_iff_foodGenerated_and_predSupported Q C⟩

end RAFInteriorRealizability
