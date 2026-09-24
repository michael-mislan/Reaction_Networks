import proofs.RAF.Concrete.PolymerCRS

namespace HordijkSteelThreshold

open RAF.Polymer RAF.Concrete

/-- The factor opposite a food factor. Reaction identities are not quotiented. -/
def foodChunkOther {n : Nat} (L : Nat) (r : Reaction n) : Molecule n :=
  if molLength (reactionLeft r) ≤ L then reactionRight r else reactionLeft r

/-- Unary graph closure along the retained reversible reaction edges. -/
def foodChunkGraphStep {n : Nat} (L : Nat) (S : Finset (Reaction n))
    (A : Finset (Molecule n)) : Finset (Molecule n) :=
  A ∪ S.biUnion (fun r =>
    (if foodChunkOther L r ∈ A then {reactionProduct r} else ∅) ∪
    (if reactionProduct r ∈ A then {foodChunkOther L r} else ∅))

/-- With a supplied food factor on each retained reaction, the exact reversible
source step equals graph reachability. No catalytic independence is assumed. -/
theorem revClosureStep_eq_foodChunkGraphStep {n L : Nat}
    (S : Finset (Reaction n)) (A : Finset (Molecule n))
    (hfood : binaryFood n L ⊆ A)
    (hshort : ∀ r ∈ S, molLength (reactionLeft r) ≤ L ∨
      molLength (reactionRight r) ≤ L) :
    revClosureStep (binaryPolymerCRS n L) S A = foodChunkGraphStep L S A := by
  classical
  have hlocal (r : Reaction n) (hr : r ∈ S) :
      A ∪ ((if RevEnabledLhs (binaryPolymerCRS n L) A r then
          {reactionProduct r} else ∅) ∪
        (if RevEnabledRhs (binaryPolymerCRS n L) A r then
          {reactionLeft r, reactionRight r} else ∅)) =
      A ∪ ((if foodChunkOther L r ∈ A then {reactionProduct r} else ∅) ∪
        (if reactionProduct r ∈ A then {foodChunkOther L r} else ∅)) := by
    by_cases hl : molLength (reactionLeft r) ≤ L
    · have ha : reactionLeft r ∈ A := hfood (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl⟩)
      ext x
      simp only [foodChunkOther, if_pos hl, RevEnabledLhs, RevEnabledRhs,
        binaryPolymerCRS, Finset.insert_subset_iff, Finset.singleton_subset_iff,
        ha, true_and]
      split_ifs <;> simp_all
    · have hrlen := (hshort r hr).resolve_left hl
      have ha : reactionRight r ∈ A := hfood (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrlen⟩)
      ext x
      simp only [foodChunkOther, if_neg hl, RevEnabledLhs, RevEnabledRhs,
        binaryPolymerCRS, Finset.insert_subset_iff, Finset.singleton_subset_iff,
        ha, and_true]
      split_ifs <;> simp_all
  ext x
  simp only [revClosureStep, foodChunkGraphStep, Finset.mem_union, Finset.mem_biUnion]
  constructor
  · rintro (hx | ⟨r, hr, hx⟩)
    · exact Or.inl hx
    · have hm := Finset.mem_union_right A (Finset.mem_union.mpr hx)
      change x ∈ A ∪ ((if RevEnabledLhs (binaryPolymerCRS n L) A r then
        {reactionProduct r} else ∅) ∪
        (if RevEnabledRhs (binaryPolymerCRS n L) A r then
        {reactionLeft r, reactionRight r} else ∅)) at hm
      rw [hlocal r hr] at hm
      rcases Finset.mem_union.mp hm with h | h
      · exact Or.inl h
      · exact Or.inr ⟨r, hr, Finset.mem_union.mp h⟩
  · rintro (hx | ⟨r, hr, hx⟩)
    · exact Or.inl hx
    · have hm := Finset.mem_union_right A (Finset.mem_union.mpr hx)
      rw [← hlocal r hr] at hm
      rcases Finset.mem_union.mp hm with h | h
      · exact Or.inl h
      · exact Or.inr ⟨r, hr, Finset.mem_union.mp h⟩

def foodChunkGraphAt {n : Nat} (L : Nat) (S : Finset (Reaction n)) :
    Nat → Finset (Molecule n)
  | 0 => binaryFood n L
  | k + 1 => foodChunkGraphStep L S (foodChunkGraphAt L S k)

theorem food_subset_foodChunkGraphAt {n L : Nat} (S : Finset (Reaction n))
    (k : Nat) : binaryFood n L ⊆ foodChunkGraphAt L S k := by
  induction k with
  | zero => exact Finset.Subset.refl _
  | succ k ih => exact ih.trans Finset.subset_union_left

/-- Equality at every finite generation stage, not merely an endpoint count. -/
theorem revClosureAt_eq_foodChunkGraphAt {n L : Nat}
    (S : Finset (Reaction n))
    (hshort : ∀ r ∈ S, molLength (reactionLeft r) ≤ L ∨
      molLength (reactionRight r) ≤ L) (k : Nat) :
    revClosureAt (binaryPolymerCRS n L) S k = foodChunkGraphAt L S k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [revClosureAt, ih, revClosureStep_eq_foodChunkGraphStep S _
      (food_subset_foodChunkGraphAt S k) hshort]
    rfl

end HordijkSteelThreshold
