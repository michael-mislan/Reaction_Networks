import proofs.RAFInteriorRealizability.CPlusThreeSmall

/-!
Transport of finite food-support certificates across a relabeling of the
reaction ground set.
-/

namespace RAFInteriorRealizability

universe u v

variable {E : Type u} {F : Type v}
variable [Fintype E] [DecidableEq E] [Fintype F] [DecidableEq F]

/-- Pull an antimatroid back along a finite equivalence. -/
noncomputable def AntimatroidData.pullback
    (A : AntimatroidData F) (e : E ≃ F) : AntimatroidData E := by
  classical
  refine {
    family := Finset.univ.filter (fun S : Finset E => S.image e ∈ A.family)
    empty_mem := by simpa using A.empty_mem
    union_mem := ?_
    accessible := ?_
  }
  · intro S T hS hT
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS hT ⊢
    simpa [Finset.image_union] using A.union_mem hS hT
  · intro S hS hne
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS ⊢
    obtain ⟨y, hy, hErase⟩ := A.accessible hS (hne.image e)
    obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp hy
    refine ⟨x, hx, ?_⟩
    subst y
    simpa [Finset.image_erase e.injective] using hErase

omit [Fintype F] in
theorem AntimatroidData.mem_pullback_iff
    (A : AntimatroidData F) (e : E ≃ F) (S : Finset E) :
    S ∈ (A.pullback e).family ↔ S.image e ∈ A.family := by
  classical
  simp [AntimatroidData.pullback]

/-- Pull a predecessor relation back across the same relabeling. -/
def pullbackPredecessors (P : F → Finset F) (e : E ≃ F) :
    E → Finset E := fun x => (P (e x)).image e.symm

omit [Fintype E] [Fintype F] in
theorem predSupported_pullback_iff
    (P : F → Finset F) (e : E ≃ F) (S : Finset E) :
    PredSupported (pullbackPredecessors P e) S ↔
      PredSupported P (S.image e) := by
  constructor
  · intro h y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨u, hu, hpred⟩ := h x hx
    obtain ⟨v, hv, hvu⟩ := Finset.mem_image.mp hpred
    have hvEq : v = e u := by
      apply e.symm.injective
      simpa [pullbackPredecessors] using hvu
    exact ⟨e u, Finset.mem_image.mpr ⟨u, hu, rfl⟩, hvEq ▸ hv⟩
  · intro h x hx
    obtain ⟨y, hy, hpred⟩ := h (e x) (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hy
    refine ⟨u, hu, ?_⟩
    exact Finset.mem_image.mpr ⟨e u, hpred, by simp⟩

omit [Fintype F] in
/-- A certificate for the empty-or-at-least-three family survives relabeling. -/
theorem cplusThree_certificate_pullback
    (A : AntimatroidData F) (P : F → Finset F) (e : E ≃ F)
    (h : ∀ T : Finset F,
      (T = ∅ ∨ 3 ≤ T.card) ↔ T ∈ A.family ∧ PredSupported P T)
    (S : Finset E) :
    (S = ∅ ∨ 3 ≤ S.card) ↔
      S ∈ (A.pullback e).family ∧
        PredSupported (pullbackPredecessors P e) S := by
  have hCard : (S.image e).card = S.card :=
    Finset.card_image_of_injective S e.injective
  have hEmpty : S.image e = ∅ ↔ S = ∅ := by simp
  simpa only [hCard, hEmpty, AntimatroidData.mem_pullback_iff,
    predSupported_pullback_iff] using h (S.image e)

/-- Realizability for every three-element reaction ground set. -/
theorem cplusThree_card_eq_three_realizable
    (hcard : Fintype.card E = 3) :
    SameGroundRAFRealizable (cplusThreeOperator E) := by
  let e : E ≃ Fin 3 := Fintype.equivFinOfCardEq hcard
  apply (rafInteriorOperator_realizable_iff (cplusThreeOperator E)).2
  refine ⟨(fullAntimatroid (Fin 3)).pullback e,
    pullbackPredecessors threeCyclePredecessors e, ?_⟩
  intro S
  exact (mem_cplusThreeOperator S).trans
    (cplusThree_certificate_pullback
      (fullAntimatroid (Fin 3)) threeCyclePredecessors e
      cplusThree_fin3_certificate S)

/-- Realizability for every four-element reaction ground set. -/
theorem cplusThree_card_eq_four_realizable
    (hcard : Fintype.card E = 4) :
    SameGroundRAFRealizable (cplusThreeOperator E) := by
  let e : E ≃ Fin 4 := Fintype.equivFinOfCardEq hcard
  apply (rafInteriorOperator_realizable_iff (cplusThreeOperator E)).2
  refine ⟨fourAntimatroid.pullback e,
    pullbackPredecessors fourPredecessors e, ?_⟩
  intro S
  exact (mem_cplusThreeOperator S).trans
    (cplusThree_certificate_pullback
      fourAntimatroid fourPredecessors e
      cplusThree_fin4_certificate S)

/-- Complete positive direction of the sharp three-element threshold. -/
theorem cplusThree_card_le_four_realizable
    (hcard : Fintype.card E ≤ 4) :
    SameGroundRAFRealizable (cplusThreeOperator E) := by
  by_cases hSmall : Fintype.card E ≤ 2
  · exact cplusThree_card_le_two_realizable hSmall
  · by_cases hThree : Fintype.card E = 3
    · exact cplusThree_card_eq_three_realizable hThree
    · have hFour : Fintype.card E = 4 := by omega
      exact cplusThree_card_eq_four_realizable hFour

end RAFInteriorRealizability
