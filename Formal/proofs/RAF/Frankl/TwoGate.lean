import proofs.RAF.Frankl.CoreAbundance

namespace RAF.Frankl

open RAF
open scoped Classical

variable {M R : Type*} [DecidableEq M] [Fintype R] [DecidableEq R]

/-- A two-reaction transversal of all nonempty RAFs contains an abundant
reaction. The extra one in the bound accounts for the empty fixed point. -/
theorem two_hit_rafFixedFrankl (Q : CRS M R) (C : Catalysis M R) (a b : R)
    (hhit : ∀ S : Finset R, IsRAF Q C S → a ∈ S ∨ b ∈ S) :
    RAFFixedFrankl Q C := by
  classical
  intro hne
  let F := rafFamily Q C
  let A := F.filter (fun S => a ∈ S)
  let B := F.filter (fun S => b ∈ S)
  have hu : A ∪ B = F := by
    ext S
    simp only [A,B,Finset.mem_union,Finset.mem_filter]
    constructor
    · rintro (h | h) <;> exact h.1
    · intro hs
      rcases hhit S ((mem_rafFamily Q C S).mp hs) with ha | hb
      · exact Or.inl ⟨hs,ha⟩
      · exact Or.inr ⟨hs,hb⟩
  have hc := Finset.card_union_add_card_inter A B
  rw [hu] at hc
  have hp : 0 < F.card := Finset.card_pos.mpr hne
  have hbound : F.card + 1 ≤ 2 * A.card ∨ F.card + 1 ≤ 2 * B.card := by
    by_cases ha : A.Nonempty
    · by_cases hb : B.Nonempty
      · obtain ⟨S,hs⟩ := ha
        obtain ⟨T,ht⟩ := hb
        have hs' : S ∈ F ∧ a ∈ S := Finset.mem_filter.mp hs
        have ht' : T ∈ F ∧ b ∈ T := Finset.mem_filter.mp ht
        have hraf := isRAF_union Q C ((mem_rafFamily Q C S).mp hs'.1)
          ((mem_rafFamily Q C T).mp ht'.1)
        have hi : (A ∩ B).Nonempty := by
          refine ⟨S ∪ T,Finset.mem_inter.mpr ⟨?_,?_⟩⟩
          · exact Finset.mem_filter.mpr ⟨(mem_rafFamily Q C _).mpr hraf,
              Finset.mem_union_left T hs'.2⟩
          · exact Finset.mem_filter.mpr ⟨(mem_rafFamily Q C _).mpr hraf,
              Finset.mem_union_right S ht'.2⟩
        have hip := Finset.card_pos.mpr hi
        omega
      · have hz : B.card = 0 := Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hb)
        have hi : (A ∩ B).card ≤ B.card := Finset.card_le_card Finset.inter_subset_right
        omega
    · have hz : A.card = 0 := Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp ha)
      have hi : (A ∩ B).card ≤ A.card := Finset.card_le_card Finset.inter_subset_left
      omega
  rcases hbound with ha | hb
  · refine ⟨a,?_⟩
    have he : A.card = frequency Q C a := by
      unfold A F frequency
      congr 1
      ext S
      simp only [Finset.mem_filter]
    rwa [he] at ha
  · refine ⟨b,?_⟩
    have he : B.card = frequency Q C b := by
      unfold B F frequency
      congr 1
      ext S
      simp only [Finset.mem_filter]
    rwa [he] at hb

/-- Empty-inclusive RAF abundance with at most two non-food-ready reactions.
The reactions `a` and `b` need not be distinct. -/
theorem two_nonfood_rafFixedFrankl (Q : CRS M R) (C : Catalysis M R) (a b : R)
    (hE : ∀ r, r ≠ a → r ≠ b → SeedReaction Q r) : RAFFixedFrankl Q C := by
  classical
  by_cases hcore : ∃ U : Finset R, IsRAF Q C U ∧ a ∉ U ∧ b ∉ U
  · obtain ⟨U,hu,ha,hb⟩ := hcore
    apply elementary_core_rafFixedFrankl Q C U hu
    intro r hr
    exact hE r (fun heq => ha (heq ▸ hr)) (fun heq => hb (heq ▸ hr))
  · apply two_hit_rafFixedFrankl Q C a b
    intro S hs
    by_contra hn
    push Not at hn
    exact hcore ⟨S,hs,hn⟩

end RAF.Frankl
