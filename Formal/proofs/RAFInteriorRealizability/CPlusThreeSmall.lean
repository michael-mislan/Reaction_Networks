import proofs.RAFInteriorRealizability.CPlusThreeFourSeed

/-!
Small positive certificates for the empty-or-at-least-three fixed family.
-/

namespace RAFInteriorRealizability

universe u

/-- The interior operator whose fixed family is the empty set together with
all sets of cardinality at least three. -/
noncomputable def cplusThreeOperator (E : Type u) [Fintype E] [DecidableEq E] :
    InteriorOperator E := by
  classical
  refine {
    family := Finset.univ.filter (fun S : Finset E => S = ∅ ∨ 3 ≤ S.card)
    empty_mem := by simp
    union_mem := ?_
  }
  intro S T hS hT
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS hT ⊢
  rcases hS with hEmpty | hLarge
  · simp [hEmpty, hT]
  · right
    have hCard := Finset.card_le_card (Finset.subset_union_left : S ⊆ S ∪ T)
    omega

@[simp] theorem mem_cplusThreeOperator
    {E : Type u} [Fintype E] [DecidableEq E] (S : Finset E) :
    S ∈ (cplusThreeOperator E).family ↔ S = ∅ ∨ 3 ≤ S.card := by
  simp [cplusThreeOperator]

/-- The full powerset is an antimatroid. -/
noncomputable def fullAntimatroid (E : Type*) [Fintype E] [DecidableEq E] :
    AntimatroidData E := by
  classical
  refine {
    family := Finset.univ
    empty_mem := by simp
    union_mem := by simp
    accessible := ?_
  }
  intro S _ hne
  obtain ⟨e, he⟩ := hne
  exact ⟨e, he, by simp⟩

/-- On at most two vertices, the empty predecessor relation supports only the empty set. -/
theorem cplusThree_card_le_two_certificate
    {E : Type u} [Fintype E] [DecidableEq E]
    (hcard : Fintype.card E ≤ 2) (S : Finset E) :
    (S = ∅ ∨ 3 ≤ S.card) ↔
      S ∈ (fullAntimatroid E).family ∧
        PredSupported (fun _ => ∅) S := by
  have hSCard : S.card ≤ Fintype.card E := by
    simpa using Finset.card_le_card (Finset.subset_univ S)
  constructor
  · intro h
    rcases h with hEmpty | hLarge
    · subst S
      simp [PredSupported, fullAntimatroid]
    · omega
  · intro h
    by_cases hEmpty : S = ∅
    · exact Or.inl hEmpty
    · obtain ⟨e, he⟩ := Finset.nonempty_iff_ne_empty.mpr hEmpty
      obtain ⟨u, hu, hPred⟩ := h.2 e he
      simp at hPred

/-- The target operator is realizable on any ground set of size at most two. -/
theorem cplusThree_card_le_two_realizable
    {E : Type u} [Fintype E] [DecidableEq E]
    (hcard : Fintype.card E ≤ 2) :
    SameGroundRAFRealizable (cplusThreeOperator E) := by
  apply (rafInteriorOperator_realizable_iff (cplusThreeOperator E)).2
  exact ⟨fullAntimatroid E, fun _ => ∅, fun S =>
    (mem_cplusThreeOperator S).trans (cplusThree_card_le_two_certificate hcard S)⟩

/-- A directed three-cycle, with the predecessor of each vertex explicit. -/
def threeCyclePredecessors (e : Fin 3) : Finset (Fin 3) :=
  if e = 0 then {2} else if e = 1 then {0} else {1}

/-- On three vertices, the three-cycle supports exactly the empty and full sets. -/
theorem cplusThree_fin3_certificate (S : Finset (Fin 3)) :
    (S = ∅ ∨ 3 ≤ S.card) ↔
      S ∈ (fullAntimatroid (Fin 3)).family ∧
        PredSupported threeCyclePredecessors S := by
  simp only [fullAntimatroid, Finset.mem_univ, true_and]
  fin_cases S <;> simp [PredSupported, threeCyclePredecessors] <;> decide

theorem cplusThree_fin3_realizable :
    SameGroundRAFRealizable (cplusThreeOperator (Fin 3)) := by
  apply (rafInteriorOperator_realizable_iff (cplusThreeOperator (Fin 3))).2
  exact ⟨fullAntimatroid (Fin 3), threeCyclePredecessors, fun S =>
    (mem_cplusThreeOperator S).trans (cplusThree_fin3_certificate S)⟩

/-- Explicit four-vertex antimatroid found by a bounded finite-model search. -/
def fourAntimatroid : AntimatroidData (Fin 4) where
  family := {∅, {0}, {1}, {0, 1}, {0, 2}, {1, 2},
    {0, 1, 2}, {0, 1, 3}, {0, 2, 3}, {1, 2, 3}, {0, 1, 2, 3}}
  empty_mem := by decide
  union_mem := by decide
  accessible := by decide

/-- The predecessor relation paired with `fourAntimatroid`. -/
def fourPredecessors (e : Fin 4) : Finset (Fin 4) :=
  if e = 0 then {1, 3}
  else if e = 1 then {2, 3}
  else if e = 2 then {0, 3}
  else {0, 1}

/-- The explicit certificate realizes the empty-or-at-least-three family on four vertices. -/
theorem cplusThree_fin4_certificate (S : Finset (Fin 4)) :
    (S = ∅ ∨ 3 ≤ S.card) ↔
      S ∈ fourAntimatroid.family ∧ PredSupported fourPredecessors S := by
  fin_cases S <;> simp [fourAntimatroid, PredSupported, fourPredecessors] <;> decide

theorem cplusThree_fin4_realizable :
    SameGroundRAFRealizable (cplusThreeOperator (Fin 4)) := by
  apply (rafInteriorOperator_realizable_iff (cplusThreeOperator (Fin 4))).2
  exact ⟨fourAntimatroid, fourPredecessors, fun S =>
    (mem_cplusThreeOperator S).trans (cplusThree_fin4_certificate S)⟩

end RAFInteriorRealizability
