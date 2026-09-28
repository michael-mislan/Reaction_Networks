import proofs.RAFInteriorRealizability.CPlusThreeSeeds

/-!
Restriction of the antimatroid and predecessor certificate to a smaller
reaction ground set. This lets a five-element obstruction imply all larger
ground-set obstructions.
-/

namespace RAFInteriorRealizability

universe u

variable {E : Type u} [DecidableEq E]

/-- Feasibility restricted to a selected subground remains an antimatroid. -/
noncomputable def AntimatroidData.restrict
    (A : AntimatroidData E) (Y : Finset E) : AntimatroidData {e // e ∈ Y} := by
  classical
  refine {
    family := Finset.univ.filter
      (fun T : Finset {e // e ∈ Y} => T.image Subtype.val ∈ A.family)
    empty_mem := ?_
    union_mem := ?_
    accessible := ?_
  }
  · simpa using A.empty_mem
  · intro S T hS hT
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS hT ⊢
    simpa [Finset.image_union] using A.union_mem hS hT
  · intro S hS hne
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS ⊢
    have hImageNe : (S.image Subtype.val).Nonempty := hne.image _
    obtain ⟨e, heImage, hErase⟩ := A.accessible hS hImageNe
    obtain ⟨x, hx, hxe⟩ := Finset.mem_image.mp heImage
    refine ⟨x, hx, ?_⟩
    subst e
    simpa [Finset.image_erase Subtype.val_injective] using hErase

/-- The restricted family has exactly the memberships inherited from the
original family. -/
theorem AntimatroidData.mem_restrict_iff
    (A : AntimatroidData E) (Y : Finset E)
    (T : Finset {e // e ∈ Y}) :
    T ∈ (A.restrict Y).family ↔ T.image Subtype.val ∈ A.family := by
  classical
  simp [AntimatroidData.restrict]

/-- The predecessor relation induced on a selected subground. -/
def restrictPredecessors (P : E → Finset E) (Y : Finset E) :
    {e // e ∈ Y} → Finset {e // e ∈ Y} :=
  fun e => Finset.univ.filter (fun u => u.val ∈ P e.val)

/-- Predecessor support is unchanged when both the selected set and its
predecessors are viewed inside the original ground type. -/
theorem predSupported_restrict_iff
    (P : E → Finset E) (Y : Finset E) (T : Finset {e // e ∈ Y}) :
    PredSupported (restrictPredecessors P Y) T ↔
      PredSupported P (T.image Subtype.val) := by
  classical
  constructor
  · intro h e he
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨u, hu, hux⟩ := h x hx
    exact ⟨u.val, Finset.mem_image.mpr ⟨u, hu, rfl⟩,
      by simpa [restrictPredecessors] using hux⟩
  · intro h e he
    obtain ⟨u, hu, hue⟩ :=
      h e.val (Finset.mem_image.mpr ⟨e, he, rfl⟩)
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
    exact ⟨v, hv, by simpa [restrictPredecessors] using hue⟩

/-- A certificate for the empty-or-at-least-three family restricts to every
smaller reaction ground set. In particular, an obstruction on five elements
rules out all larger finite ground sets. -/
theorem cplusThree_certificate_restrict
    (A : AntimatroidData E) (P : E → Finset E) (Y : Finset E)
    (h : ∀ S : Finset E,
      (S = ∅ ∨ 3 ≤ S.card) ↔ S ∈ A.family ∧ PredSupported P S)
    (T : Finset {e // e ∈ Y}) :
    (T = ∅ ∨ 3 ≤ T.card) ↔
      T ∈ (A.restrict Y).family ∧
        PredSupported (restrictPredecessors P Y) T := by
  have hCard : (T.image Subtype.val).card = T.card :=
    Finset.card_image_of_injective T Subtype.val_injective
  have hEmpty : T.image Subtype.val = ∅ ↔ T = ∅ := by simp
  simpa only [hCard, hEmpty, AntimatroidData.mem_restrict_iff,
    predSupported_restrict_iff] using h (T.image Subtype.val)

end RAFInteriorRealizability
