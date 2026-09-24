import proofs.RAFInteriorRealizability.Realizable

namespace RAFInteriorRealizability

open RAF RAF.Frankl

universe u v

variable {M : Type u} {E : Type v} [DecidableEq M]
  [Fintype E] [DecidableEq E]

/-- Static predecessor support on a selected reaction set. -/
def PredSupported (P : E → Finset E) (S : Finset E) : Prop :=
  ∀ e ∈ S, ∃ u ∈ S, u ∈ P e

/-- Predecessors extracted from literal catalysis.  Product catalysts give the
ordinary directed edges; a food catalyst is represented by a self-loop. -/
noncomputable def extractedPredecessors (Q : CRS M E) (C : Catalysis M E)
    (e : E) : Finset E := by
  classical
  exact Finset.univ.filter fun u =>
    (∃ x ∈ Q.outputs u, C x e) ∨
    (u = e ∧ ∃ x ∈ Q.food, C x e)

@[simp] theorem mem_extractedPredecessors (Q : CRS M E) (C : Catalysis M E)
    (u e : E) :
    u ∈ extractedPredecessors Q C e ↔
      (∃ x ∈ Q.outputs u, C x e) ∨
      (u = e ∧ ∃ x ∈ Q.food, C x e) := by
  classical
  simp [extractedPredecessors]

theorem productGraphCatalyzed_iff_predSupported
    (Q : CRS M E) (C : Catalysis M E) (S : Finset E) :
    ProductGraphCatalyzed Q C S ↔
      PredSupported (extractedPredecessors Q C) S := by
  constructor
  · intro h e he
    rcases h e he with hfood | ⟨u, hu, hout⟩
    · exact ⟨e, he, (mem_extractedPredecessors Q C e e).2
        (Or.inr ⟨rfl, hfood⟩)⟩
    · exact ⟨u, hu, (mem_extractedPredecessors Q C u e).2 (Or.inl hout)⟩
  · intro h e he
    obtain ⟨u, hu, hpred⟩ := h e he
    rcases (mem_extractedPredecessors Q C u e).1 hpred with hout | ⟨rfl, hfood⟩
    · exact Or.inr ⟨u, hu, hout⟩
    · exact Or.inl hfood

end RAFInteriorRealizability
