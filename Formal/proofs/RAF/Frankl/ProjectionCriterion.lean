import proofs.RAF.Frankl.CoreAbundance
import proofs.RAFQueryCompilation.Pruning

namespace RAF.Frankl

open RAF RAFQueryCompilation
open scoped Classical

variable {M R : Type*} [DecidableEq M] [Fintype R] [DecidableEq R]

/-- Internal producers of any catalyst of the selected head. -/
noncomputable def internalPredecessors (Q : CRS M R) (C : Catalysis M R)
    (E : Finset R) (r : R) : Finset R :=
  E.filter fun p => ∃ x ∈ Q.outputs p, C x r

/-- Projection is assessed in the original literal source, with availability
restricted by intersection and with the empty fixed point retained. -/
def ProjectionPreserving (Q : CRS M R) (C : Catalysis M R) (E : Finset R) : Prop :=
  ∀ W ∈ fixedFamily Q C, W ∩ E ∈ fixedFamily Q C

theorem elementary_projection_iff_support (Q : CRS M R) (C : Catalysis M R)
    (E W : Finset R) (hE : ∀ r ∈ E, SeedReaction Q r) :
    W ∩ E ∈ fixedFamily Q C ↔
      ∀ r ∈ W ∩ E, extensionSupport Q C (W ∩ E) r := by
  rw [fixedFamily_iff_food_support]
  have hf : FoodGenerated Q (W ∩ E) := fun r hr =>
    ⟨0, hE r (Finset.mem_inter.mp hr).2⟩
  exact ⟨fun h => h.2, fun h => ⟨hf,h⟩⟩

omit [Fintype R] in
theorem projection_support_iff (Q : CRS M R) (C : Catalysis M R)
    (E W : Finset R) (r : R) :
    extensionSupport Q C (W ∩ E) r ↔
      (∃ x ∈ Q.food, C x r) ∨ ∃ p ∈ W, p ∈ internalPredecessors Q C E r := by
  simp only [extensionSupport, internalPredecessors, Finset.mem_filter,
    Finset.mem_inter]
  constructor
  · rintro (hf | ⟨p,⟨hw,he⟩,hc⟩)
    · exact Or.inl hf
    · exact Or.inr ⟨p,hw,he,hc⟩
  · rintro (hf | ⟨p,hw,he,hc⟩)
    · exact Or.inl hf
    · exact Or.inr ⟨p,⟨hw,he⟩,hc⟩

/-- Exact projection criterion using the inherited executable maxRAF algorithm. -/
theorem projection_iff_deletion_queries [Fintype M]
    (Q : CRS M R) (C : Catalysis M R) [∀ x r, Decidable (C x r)]
    (E : Finset R) (hE : ∀ r ∈ E, SeedReaction Q r) :
    ProjectionPreserving Q C E ↔
      ∀ r ∈ E, (¬ ∃ x ∈ Q.food, C x r) →
        r ∉ evaluate Q C (Finset.univ \ internalPredecessors Q C E r) := by
  constructor
  · intro hp r hr hfood hmem
    obtain ⟨W,hw,hraf,hrw⟩ := (evaluate_mem_iff Q C _ r).mp hmem
    have hs := (elementary_projection_iff_support Q C E W hE).mp
      (hp W ((mem_fixedFamily Q C W).mpr (Or.inr hraf))) r
      (Finset.mem_inter.mpr ⟨hrw,hr⟩)
    rcases (projection_support_iff Q C E W r).mp hs with hf | ⟨p,hpw,hpp⟩
    · exact hfood hf
    · exact (Finset.mem_sdiff.mp (hw hpw)).2 hpp
  · intro hq W hw
    apply (elementary_projection_iff_support Q C E W hE).mpr
    intro r hr
    apply (projection_support_iff Q C E W r).mpr
    by_cases hf : ∃ x ∈ Q.food, C x r
    · exact Or.inl hf
    · right
      by_contra hn
      have hsub : W ⊆ Finset.univ \ internalPredecessors Q C E r := by
        intro p hp
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ p, fun hpp => hn ⟨p,hp,hpp⟩⟩
      have hraf : IsRAF Q C W := by
        rcases (mem_fixedFamily Q C W).mp hw with he | he
        · have := (Finset.mem_inter.mp hr).1
          simp [he] at this
        · exact he
      exact hq r (Finset.mem_inter.mp hr).2 hf
        ((evaluate_mem_iff Q C _ r).mpr ⟨W,hsub,hraf,(Finset.mem_inter.mp hr).1⟩)

/-- A failed query returns the actual nonempty global RAF with invalid projection. -/
theorem failed_query_witness [Fintype M]
    (Q : CRS M R) (C : Catalysis M R) [∀ x r, Decidable (C x r)]
    (E : Finset R) (hE : ∀ r ∈ E, SeedReaction Q r)
    (r : R) (hr : r ∈ E) (hf : ¬ ∃ x ∈ Q.food, C x r)
    (hq : r ∈ evaluate Q C (Finset.univ \ internalPredecessors Q C E r)) :
    let W := evaluate Q C (Finset.univ \ internalPredecessors Q C E r)
    IsRAF Q C W ∧ W ∩ E ∉ fixedFamily Q C := by
  dsimp
  refine ⟨(isRAF_iff_nonempty_prune_eq Q C _).mpr
    ⟨⟨r,hq⟩,evaluate_fixed Q C _⟩, ?_⟩
  intro hp
  have hs := (elementary_projection_iff_support Q C E _ hE).mp hp r
    (Finset.mem_inter.mpr ⟨hq,hr⟩)
  rcases (projection_support_iff Q C E _ r).mp hs with hc | ⟨p,hp,hpred⟩
  · exact hf hc
  · exact (Finset.mem_sdiff.mp (evaluate_subset Q C _ hp)).2 hpred

/-- No exterior production of a catalyst needed by a non-food-catalyzed core
head is a sufficient condition. Inactive reactions are not removed. -/
theorem projection_of_no_incoming_support
    (Q : CRS M R) (C : Catalysis M R) (E : Finset R)
    (hE : ∀ r ∈ E, SeedReaction Q r)
    (hno : ∀ r ∈ E, (¬ ∃ x ∈ Q.food, C x r) →
      ∀ p, (∃ x ∈ Q.outputs p, C x r) → p ∈ E) :
    ProjectionPreserving Q C E := by
  intro W hw
  apply (elementary_projection_iff_support Q C E W hE).mpr
  intro r hr
  have hs := (fixedFamily_iff_food_support Q C W).mp hw |>.2 r
    (Finset.mem_inter.mp hr).1
  by_cases hf : ∃ x ∈ Q.food, C x r
  · exact Or.inl hf
  · rcases hs with hc | ⟨p,hp,hc⟩
    · exact (hf hc).elim
    · exact Or.inr ⟨p,Finset.mem_inter.mpr ⟨hp,hno r
        (Finset.mem_inter.mp hr).2 hf p hc⟩,hc⟩

/-- The isolated elementary maxRAF supplies the abundance candidate set.
No projection query hypothesis is necessary for this guarantee. -/
theorem elementary_maxRAF_exists_abundant [Fintype M]
    (Q : CRS M R) (C : Catalysis M R) [∀ x r, Decidable (C x r)]
    (E : Finset R) (hE : ∀ r ∈ E, SeedReaction Q r)
    (hne : (evaluate Q C E).Nonempty) :
    ∃ r ∈ evaluate Q C E, (fixedFamily Q C).card ≤
      2 * ((fixedFamily Q C).filter (fun W => r ∈ W)).card := by
  have hu : IsRAF Q C (evaluate Q C E) :=
    (isRAF_iff_nonempty_prune_eq Q C _).mpr ⟨hne,evaluate_fixed Q C E⟩
  exact elementary_core_exists_abundant Q C (evaluate Q C E) hu
    (fun r hr => hE r (evaluate_subset Q C E hr))

end RAF.Frankl
