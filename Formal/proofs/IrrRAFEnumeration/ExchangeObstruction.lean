import proofs.IrrRAFEnumeration.FiniteDuality

namespace IrrRAFEnumeration

/-- A star edge contains its center and one private leaf. -/
def starEdge {n : Nat} (i : Fin (n + 1)) : Finset (Option (Fin (n + 1))) :=
  {none, some i}

def starFamily (n : Nat) : Finset (Finset (Option (Fin (n + 1)))) :=
  Finset.univ.image starEdge

def starLeaves (n : Nat) : Finset (Option (Fin (n + 1))) :=
  Finset.univ.image some

@[simp] theorem some_mem_starLeaves {n : Nat} (i : Fin (n + 1)) :
    some i ∈ starLeaves n := by
  simp [starLeaves]

@[simp] theorem none_not_mem_starLeaves {n : Nat} :
    (none : Option (Fin (n + 1))) ∉ starLeaves n := by
  simp [starLeaves]

/-- A set hits every star edge exactly when it contains the center or contains
every leaf. -/
theorem hits_starFamily_iff {n : Nat} (A : Finset (Option (Fin (n + 1)))) :
    Hits (starFamily n) A ↔
      none ∈ A ∨ ∀ i : Fin (n + 1), some i ∈ A := by
  classical
  constructor
  · intro h
    by_cases hc : none ∈ A
    · exact Or.inl hc
    · apply Or.inr
      intro i
      have hedge : starEdge i ∈ starFamily n :=
        Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
      obtain ⟨x, hxA, hxE⟩ := Finset.not_disjoint_iff.mp (h _ hedge)
      simp only [starEdge, Finset.mem_insert, Finset.mem_singleton] at hxE
      rcases hxE with rfl | rfl
      · exact (hc hxA).elim
      · exact hxA
  · rintro (hc | hall)
    · intro E hE
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hE
      exact Finset.not_disjoint_iff.mpr ⟨none, hc, by simp [starEdge]⟩
    · intro E hE
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hE
      exact Finset.not_disjoint_iff.mpr
        ⟨some i, hall i, by simp [starEdge]⟩

theorem starCenter_minimal {n : Nat} :
    Minimal (Hits (starFamily n))
      ({none} : Finset (Option (Fin (n + 1)))) := by
  classical
  constructor
  · exact (hits_starFamily_iff {none}).mpr (Or.inl (by simp))
  · intro K hK hsub x hx
    have hxnone : x = none := by simpa using hx
    subst x
    rcases (hits_starFamily_iff K).mp hK with hc | hall
    · exact hc
    · have hleaf : some (0 : Fin (n + 1)) ∈ K := hall 0
      have := hsub hleaf
      simp at this

theorem starLeaves_minimal {n : Nat} :
    Minimal (Hits (starFamily n)) (starLeaves n) := by
  classical
  constructor
  · exact (hits_starFamily_iff (starLeaves n)).mpr (Or.inr some_mem_starLeaves)
  · intro K hK hsub x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    rcases (hits_starFamily_iff K).mp hK with hc | hall
    · exact (none_not_mem_starLeaves (n := n) (hsub hc)).elim
    · exact hall i

/-- Avoiding the center forces all leaves at once: no proper partial exchange
from the center solution toward the leaf solution remains a transversal. -/
theorem star_leaf_subset_hits_iff_eq {n : Nat}
    (A : Finset (Option (Fin (n + 1)))) (hA : A ⊆ starLeaves n) :
    Hits (starFamily n) A ↔ A = starLeaves n := by
  constructor
  · intro hHits
    rcases (hits_starFamily_iff A).mp hHits with hc | hall
    · exact (none_not_mem_starLeaves (n := n) (hA hc)).elim
    · apply Finset.Subset.antisymm hA
      intro x hx
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
      exact hall i
  · rintro rfl
    exact starLeaves_minimal.1

theorem starLeaves_card (n : Nat) :
    (starLeaves n).card = n + 1 := by
  classical
  rw [starLeaves, Finset.card_image_iff.mpr]
  · simp
  · intro i _ j _ h
    exact Option.some.inj h

end IrrRAFEnumeration
