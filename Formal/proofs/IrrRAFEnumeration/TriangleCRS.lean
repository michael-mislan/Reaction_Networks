import proofs.IrrRAFEnumeration.ResidualStateExplosion
import proofs.IrrRAFEnumeration.RAFCompletion
import proofs.RAF.Frankl.ElementaryHorn

namespace IrrRAFEnumeration

open RAF RAF.Frankl

/-- An elementary CRS with three reactions in each independent component. -/
def memoryCRS (k : Nat) : CRS (Fin k × Option Bool) (Fin k × Option Bool) where
  inputs _ := ∅
  outputs r := {r}
  food := ∅

/-- Within each component every reaction is catalyzed by either of the other
two reactions. -/
def memoryCatalysis {k : Nat} :
    Catalysis (Fin k × Option Bool) (Fin k × Option Bool) :=
  fun x r => x.1 = r.1 ∧ x.2 ≠ r.2

theorem memoryCRS_elementary (k : Nat) : Elementary (memoryCRS k) := by
  intro r
  simp [SeedReaction, Enabled, memoryCRS]

theorem memory_isRAF_iff {k : Nat} (S : Finset (Fin k × Option Bool)) :
    IsRAF (memoryCRS k) memoryCatalysis S ↔
      S.Nonempty ∧ ∀ r ∈ S, ∃ u ∈ S, u.1 = r.1 ∧ u.2 ≠ r.2 := by
  classical
  rw [isRAF_iff_foodGenerated_and_productGraph]
  constructor
  · rintro ⟨hne, -, hgraph⟩
    refine ⟨hne, ?_⟩
    intro r hr
    rcases hgraph r hr with hfood | ⟨u, hu, x, hx, hcat⟩
    · simp [memoryCRS] at hfood
    · have hxu : x = u := by simpa [memoryCRS] using hx
      exact ⟨u, hu, by simpa [hxu] using hcat⟩
  · rintro ⟨hne, hsupport⟩
    refine ⟨hne, elementary_foodGenerated (memoryCRS k)
      (memoryCRS_elementary k) S, ?_⟩
    intro r hr
    obtain ⟨u, hu, hsame, hdiff⟩ := hsupport r hr
    exact Or.inr ⟨u, hu, u, by simp [memoryCRS], hsame, hdiff⟩

theorem memory_pair_isRAF {k : Nat} (r u : Fin k × Option Bool)
    (hsame : u.1 = r.1) (hdiff : u.2 ≠ r.2) :
    IsRAF (memoryCRS k) memoryCatalysis {r, u} := by
  rw [memory_isRAF_iff]
  refine ⟨by simp, ?_⟩
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl
  · exact ⟨u, by simp, hsame, hdiff⟩
  · exact ⟨r, by simp, hsame.symm, by exact fun h => hdiff h.symm⟩

theorem pair_mem_choiceMemoryFamily {k : Nat}
    (r u : Fin k × Option Bool) (hsame : u.1 = r.1) (hdiff : u.2 ≠ r.2) :
    {r, u} ∈ choiceMemoryFamily k := by
  classical
  rcases r with ⟨i, a⟩
  rcases u with ⟨j, b⟩
  simp only at hsame
  subst j
  rcases a with _ | a <;> rcases b with _ | b
  · exact (hdiff rfl).elim
  · apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    exact ⟨(i, b), by simp, by simp [memoryHighEdge, Finset.pair_comm]⟩
  · apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    exact ⟨(i, a), by simp, rfl⟩
  · cases a <;> cases b
    · exact (hdiff rfl).elim
    · apply Finset.mem_union_left
      apply Finset.mem_image.mpr
      exact ⟨i, Finset.mem_univ _, rfl⟩
    · apply Finset.mem_union_left
      apply Finset.mem_image.mpr
      exact ⟨i, Finset.mem_univ _, by simp [memoryLowEdge, Finset.pair_comm]⟩
    · exact (hdiff rfl).elim

theorem memory_pair_irreducible {k : Nat}
    (r u : Fin k × Option Bool) (hsame : u.1 = r.1) (hdiff : u.2 ≠ r.2) :
    MinRAFApprox.SetCoverSource.IsIrreducibleRAF
      (memoryCRS k) memoryCatalysis {r, u} := by
  classical
  refine ⟨memory_pair_isRAF r u hsame hdiff, ?_⟩
  intro B hB hBsub
  obtain ⟨x, hxB⟩ := (memory_isRAF_iff B).mp hB |>.1
  obtain ⟨y, hyB, -, hxy⟩ := (memory_isRAF_iff B).mp hB |>.2 x hxB
  have hxpair := hBsub hxB
  have hypair := hBsub hyB
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxpair hypair
  rcases hxpair with rfl | rfl
  · have hyu : y = u := by
      rcases hypair with hyr | hyu
      · exact (hxy (congrArg Prod.snd hyr)).elim
      · exact hyu
    subst y
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hxB
    · exact hyB
  · have hyr : y = r := by
      rcases hypair with hyr | hyu
      · exact hyr
      · exact (hxy (congrArg Prod.snd hyu)).elim
    subst y
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hyB
    · exact hxB

/-- The compact memory CRS has exactly the three two-reaction irrRAFs in each
component. -/
theorem memory_irrRAFFamily_eq (k : Nat) :
    irrRAFFamily (memoryCRS k) memoryCatalysis = choiceMemoryFamily k := by
  classical
  ext S
  rw [mem_irrRAFFamily]
  constructor
  · rintro ⟨hraf, hmin⟩
    obtain ⟨r, hr⟩ := (memory_isRAF_iff S).mp hraf |>.1
    obtain ⟨u, hu, hsame, hdiff⟩ :=
      (memory_isRAF_iff S).mp hraf |>.2 r hr
    have hpairsub : {r, u} ⊆ S := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hr
      · exact hu
    have hSpair : S ⊆ {r, u} :=
      hmin {r, u} (memory_pair_isRAF r u hsame hdiff) hpairsub
    rw [Finset.Subset.antisymm hSpair hpairsub]
    exact pair_mem_choiceMemoryFamily r u hsame hdiff
  · intro hS
    rcases Finset.mem_union.mp hS with hLow | hHigh
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hLow
      exact memory_pair_irreducible _ _ (by simp) (by simp)
    · obtain ⟨⟨i, b⟩, -, rfl⟩ := Finset.mem_image.mp hHigh
      exact memory_pair_irreducible _ _ (by simp) (by simp)

/-- The residual irrRAF family of the compact CRS after a binary deletion
history.  This is the native RAF version of `memoryResidual`. -/
noncomputable def memoryCRSResidual {k : Nat} (f : Fin k → Bool) :
    Finset (Finset (Fin k × Option Bool)) :=
  (irrRAFFamily (memoryCRS k) memoryCatalysis).filter fun E =>
    Disjoint E (memoryDeletion f)

theorem memoryCRSResidual_eq {k : Nat} (f : Fin k → Bool) :
    memoryCRSResidual f = memoryResidual f := by
  rw [memoryCRSResidual, memoryResidual, memory_irrRAFFamily_eq]

noncomputable def memoryCRSResidualFamily (k : Nat) :
    Finset (Finset (Finset (Fin k × Option Bool))) :=
  Finset.univ.image memoryCRSResidual

/-- A CRS with `3k` reactions and only `3k` irrRAFs has `2^k` distinct
residual irrRAF states under these canonical deletion histories. -/
theorem memoryCRSResidualFamily_card (k : Nat) :
    (memoryCRSResidualFamily k).card = 2 ^ k := by
  classical
  have hfamily : memoryCRSResidualFamily k = memoryResidualFamily k := by
    unfold memoryCRSResidualFamily memoryResidualFamily
    congr 1
    funext f
    exact memoryCRSResidual_eq f
  rw [hfamily]
  exact memoryResidualFamily_card k

end IrrRAFEnumeration
