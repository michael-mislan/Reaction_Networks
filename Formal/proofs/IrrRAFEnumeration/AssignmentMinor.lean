import proofs.IrrRAFEnumeration.FullCover

namespace IrrRAFEnumeration

variable {α : Type*} [DecidableEq α]

/-- The unminimized family left by assigning every point of `projected` on
the projection side and every point of `filtered` on the filtering side. -/
def rawAssignmentMinor (F : Finset (Finset α))
    (projected filtered : Finset α) : Finset (Finset α) :=
  (F.filter fun E => Disjoint E filtered).image fun E => E \ projected

theorem mem_rawAssignmentMinor_iff
    (T : Finset α) (F : Finset (Finset α)) (A B : Finset α) :
    T ∈ rawAssignmentMinor F A B ↔
      ∃ E ∈ F, Disjoint E B ∧ E \ A = T := by
  simp [rawAssignmentMinor, and_assoc]

/-- Consecutive assignment restrictions collapse to their accumulated
assignment.  The sole nontrivial side condition says that a point projected
earlier is never filtered later, exactly as in a recursion path whose active
universe only shrinks. -/
theorem rawAssignmentMinor_compose
    (F : Finset (Finset α)) (A B C D : Finset α)
    (hAD : Disjoint A D) :
    rawAssignmentMinor (rawAssignmentMinor F A B) C D =
      rawAssignmentMinor F (A ∪ C) (B ∪ D) := by
  classical
  ext T
  rw [mem_rawAssignmentMinor_iff, mem_rawAssignmentMinor_iff]
  constructor
  · rintro ⟨E', hE', hE'D, hE'T⟩
    rw [mem_rawAssignmentMinor_iff] at hE'
    obtain ⟨E, hEF, hEB, rfl⟩ := hE'
    refine ⟨E, hEF, ?_, ?_⟩
    · rw [Finset.disjoint_union_right]
      refine ⟨hEB, ?_⟩
      rw [Finset.disjoint_left] at hAD hE'D ⊢
      intro x hxE hxD
      by_cases hxA : x ∈ A
      · exact hAD hxA hxD
      · exact hE'D (Finset.mem_sdiff.mpr ⟨hxE, hxA⟩) hxD
    · ext x
      simpa only [Finset.mem_sdiff, Finset.mem_union, not_or, and_assoc] using
        Finset.ext_iff.mp hE'T x
  · rintro ⟨E, hEF, hEBD, hET⟩
    rw [Finset.disjoint_union_right] at hEBD
    refine ⟨E \ A, ?_, ?_, ?_⟩
    · rw [mem_rawAssignmentMinor_iff]
      exact ⟨E, hEF, hEBD.1, rfl⟩
    · exact hEBD.2.mono Finset.sdiff_subset Finset.Subset.rfl
    · ext x
      simpa only [Finset.mem_sdiff, Finset.mem_union, not_or, and_assoc] using
        Finset.ext_iff.mp hET x

end IrrRAFEnumeration
