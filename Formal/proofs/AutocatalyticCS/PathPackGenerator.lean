import proofs.AutocatalyticCS.PathParity

/-!
The finite anchored matching generator.  Its states are ambient reactant
subgraphs; the filter retains precisely containing matchings whose exchange
with the anchor has the strictly verified external bipartite path-pack
profile.  This presentation is deliberately extensional: later DFS or
branch-and-bound implementations may refine the enumeration without changing
the correctness interface.
-/

open scoped symmDiff

namespace AutocatalyticCS
namespace SimpleGraph

open _root_.SimpleGraph

variable {X R : Type*} [Fintype X] [Fintype R]

noncomputable instance finiteSubgraph {V : Type*} [Finite V]
    (A : _root_.SimpleGraph V) : Finite A.Subgraph :=
  Finite.of_injective (fun H : A.Subgraph => (H.verts, H.Adj)) (by
    intro H K h
    have hv : H.verts = K.verts := congrArg Prod.fst h
    have ha : H.Adj = K.Adj := congrArg Prod.snd h
    ext
    · rw [hv]
    · rw [ha])

noncomputable def anchoredMatchingGenerator
    {A : _root_.SimpleGraph (X ⊕ R)} (M : A.Subgraph) : Finset A.Subgraph := by
  classical
  letI : Finite A.Subgraph := finiteSubgraph A
  letI := Fintype.ofFinite A.Subgraph
  exact Finset.univ.filter fun M' =>
    M'.IsMatching ∧ M.verts ⊆ M'.verts ∧
      IsExternalBipartitePathPack (M.spanningCoe ∆ M'.spanningCoe)
        M.spanningCoe M.verts

theorem mem_anchoredMatchingGenerator_iff
    {A : _root_.SimpleGraph (X ⊕ R)} {M M' : A.Subgraph} :
    M' ∈ anchoredMatchingGenerator M ↔
      M'.IsMatching ∧ M.verts ⊆ M'.verts ∧
        IsExternalBipartitePathPack (M.spanningCoe ∆ M'.spanningCoe)
          M.spanningCoe M.verts := by
  classical
  simp [anchoredMatchingGenerator]

/-- Generator completeness for the structural theorem: every containing
matching around a unique anchor is emitted. -/
theorem mem_anchoredMatchingGenerator_of_unique
    {A : _root_.SimpleGraph (X ⊕ R)} {M M' : A.Subgraph}
    (hunique : Subgraph.IsUniqueMatching M) (hM' : M'.IsMatching)
    (hverts : M.verts ⊆ M'.verts)
    (hbip : A.IsBipartiteWith {v | v.isLeft} {v | v.isRight}) :
    M' ∈ anchoredMatchingGenerator M := by
  rw [mem_anchoredMatchingGenerator_iff]
  exact ⟨hM', hverts,
    exchange_isExternalBipartitePathPack_of_unique_left
      hunique hM' hverts hbip⟩

end SimpleGraph
end AutocatalyticCS
