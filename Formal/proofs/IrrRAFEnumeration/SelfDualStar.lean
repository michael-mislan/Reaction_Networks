import proofs.IrrRAFEnumeration.ExchangeObstruction

namespace IrrRAFEnumeration

/-- Add the all-leaves edge to a star with at least two leaves. -/
def selfDualStarFamily (n : Nat) :
    Finset (Finset (Option (Fin (n + 2)))) :=
  insert (starLeaves (n + 1)) (starFamily (n + 1))

theorem hits_selfDualStar_iff {n : Nat}
    (A : Finset (Option (Fin (n + 2)))) :
    Hits (selfDualStarFamily n) A ↔
      (none ∈ A ∧ ∃ i : Fin (n + 2), some i ∈ A) ∨
      ∀ i : Fin (n + 2), some i ∈ A := by
  classical
  constructor
  · intro hA
    have hStar : Hits (starFamily (n + 1)) A := by
      intro E hE
      exact hA E (by simp [selfDualStarFamily, hE])
    have hLeaves : ¬ Disjoint A (starLeaves (n + 1)) :=
      hA _ (by simp [selfDualStarFamily])
    rcases (hits_starFamily_iff A).mp hStar with hcenter | hall
    · obtain ⟨y, hyA, hyLeaves⟩ := Finset.not_disjoint_iff.mp hLeaves
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hyLeaves
      exact Or.inl ⟨hcenter, ⟨i, hyA⟩⟩
    · exact Or.inr hall
  · rintro (⟨hcenter, i, hiA⟩ | hall) E hE
    · simp only [selfDualStarFamily, Finset.mem_insert] at hE
      rcases hE with rfl | hE
      · exact Finset.not_disjoint_iff.mpr
          ⟨some i, hiA, some_mem_starLeaves i⟩
      · obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hE
        exact Finset.not_disjoint_iff.mpr
          ⟨none, hcenter, by simp [starEdge]⟩
    · simp only [selfDualStarFamily, Finset.mem_insert] at hE
      rcases hE with rfl | hE
      · let i : Fin (n + 2) := ⟨0, by omega⟩
        exact Finset.not_disjoint_iff.mpr
          ⟨some i, hall i, some_mem_starLeaves i⟩
      · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hE
        exact Finset.not_disjoint_iff.mpr
          ⟨some i, hall i, by simp [starEdge]⟩

theorem selfDualStarEdge_minimal {n : Nat} (i : Fin (n + 2)) :
    Minimal (Hits (selfDualStarFamily n)) (starEdge i) := by
  classical
  constructor
  · apply (hits_selfDualStar_iff (starEdge i)).mpr
    exact Or.inl ⟨by simp [starEdge], ⟨i, by simp [starEdge]⟩⟩
  · intro B hB hsub
    rcases (hits_selfDualStar_iff B).mp hB with ⟨hcenter, j, hjB⟩ | hall
    · have hji : j = i := by
        have := hsub hjB
        simpa [starEdge] using this
      intro z hz
      simp only [starEdge, Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hcenter
      · exact hji ▸ hjB
    · intro z hz
      simp only [starEdge, Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · obtain ⟨j, hji⟩ := Fintype.exists_ne_of_one_lt_card (by simp) i
        have hjEdge := hsub (hall j)
        have : j = i := by simpa [starEdge] using hjEdge
        exact (hji this).elim
      · exact hall i

theorem selfDualStarLeaves_minimal {n : Nat} :
    Minimal (Hits (selfDualStarFamily n)) (starLeaves (n + 1)) := by
  classical
  constructor
  · exact (hits_selfDualStar_iff _).mpr (Or.inr some_mem_starLeaves)
  · intro B hB hsub
    have hStar : Hits (starFamily (n + 1)) B := by
      intro E hE
      exact hB E (by simp [selfDualStarFamily, hE])
    have hEq : B = starLeaves (n + 1) :=
      (star_leaf_subset_hits_iff_eq B hsub).mp hStar
    exact hEq ▸ Finset.Subset.rfl

/-- This family is self-blocking. -/
theorem selfDualStar_blocker_eq (n : Nat) :
    blocker (selfDualStarFamily n) = selfDualStarFamily n := by
  classical
  ext T
  rw [mem_blocker]
  constructor
  · intro hT
    rcases (hits_selfDualStar_iff T).mp hT.1 with ⟨hc, i, hi⟩ | hall
    · have hedgeSub : starEdge i ⊆ T := by
        intro z hz
        simp only [starEdge, Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact hc
        · exact hi
      have hTsub := hT.2 (selfDualStarEdge_minimal i).1 hedgeSub
      have hEq : T = starEdge i := Finset.Subset.antisymm hTsub hedgeSub
      subst T
      simp [selfDualStarFamily, starFamily]
    · have hLeavesSub : starLeaves (n + 1) ⊆ T := by
        intro z hz
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
        exact hall i
      have hTsub := hT.2 selfDualStarLeaves_minimal.1 hLeavesSub
      have hEq : T = starLeaves (n + 1) :=
        Finset.Subset.antisymm hTsub hLeavesSub
      subst T
      simp [selfDualStarFamily]
  · intro hT
    simp only [selfDualStarFamily, Finset.mem_insert] at hT
    rcases hT with rfl | hT
    · exact selfDualStarLeaves_minimal
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hT
      exact selfDualStarEdge_minimal i

theorem starLeaves_self_intersection_card (n : Nat) :
    ((starLeaves (n + 1)) ∩ starLeaves (n + 1)).card = n + 2 := by
  rw [Finset.inter_self, starLeaves_card]

theorem starEdge_injective {m : Nat} :
    Function.Injective (starEdge (n := m)) := by
  intro i j hij
  have hi := Finset.ext_iff.mp hij (some i)
  simpa [starEdge] using hi

theorem starFamily_card (m : Nat) :
    (starFamily m).card = m + 1 := by
  classical
  rw [starFamily,
    Finset.card_image_iff.mpr fun i _ j _ h => starEdge_injective h,
    Finset.card_univ, Fintype.card_fin]

/-- The self-blocking family itself has only linear displayed size. -/
theorem selfDualStarFamily_card (n : Nat) :
    (selfDualStarFamily n).card = n + 3 := by
  classical
  have hnot : starLeaves (n + 1) ∉ starFamily (n + 1) := by
    intro hmem
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hmem
    obtain ⟨j, hji⟩ := Fintype.exists_ne_of_one_lt_card (by simp) i
    have hj : some j ∈ starLeaves (n + 1) := some_mem_starLeaves j
    rw [← hi] at hj
    have : j = i := by simpa [starEdge] using hj
    exact hji this
  simp [selfDualStarFamily, hnot, starFamily_card]

end IrrRAFEnumeration
