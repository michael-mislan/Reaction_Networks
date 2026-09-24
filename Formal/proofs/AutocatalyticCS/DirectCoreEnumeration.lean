import proofs.AutocatalyticCS.SourcePathExtraction
import proofs.AutocatalyticCS.FiniteMinimality

/-!
The terminal direct-enumeration theorem.  Unlike `coreAnchorEnum`, this
implementation never ranges over an ambient candidate universe: it flattens
only the concrete source-derived path-pack candidates of the supplied ordinary
core anchors and then applies one proof-carrying exact core test.
-/

namespace AutocatalyticCS

variable {X R : Type*} [Fintype X] [Fintype R]
variable [DecidableEq X] [DecidableEq R]
variable {Q : ReactionNetwork X R}

/-- Direct ordinary-core anchored output.  `toFinset` gives extensional edge-set
semantics and exactly-once output; candidate discovery itself is exclusively
the source-level alternating-path DFS. -/
def directSourceCoreEnum (Q : ReactionNetwork X R)
    (anchors : List (IndexedMatching Q))
    (speciesOrder : List X) (reactionOrder : List R)
    (coreTest : Finset (X × R) → Bool) : Finset (Finset (X × R)) :=
  ((anchors.flatMap fun anchor =>
      sourceCandidateEdgeFinsets Q anchor speciesOrder reactionOrder).filter
        coreTest).toFinset

theorem mem_directSourceCoreEnum_iff
    (anchors : List (IndexedMatching Q))
    (speciesOrder : List X) (reactionOrder : List R)
    (coreTest : Finset (X × R) → Bool) (edges : Finset (X × R)) :
    edges ∈ directSourceCoreEnum Q anchors speciesOrder reactionOrder coreTest ↔
      coreTest edges = true ∧
        ∃ anchor ∈ anchors,
          edges ∈ sourceCandidateEdgeFinsets Q anchor
            speciesOrder reactionOrder := by
  simp [directSourceCoreEnum, and_comm]

/-- Exact direct extraction from a complete ordinary-core list.

`ordinary_complete` is exactly the promised completeness of the input list,
stated extensionally on matching edge sets.  Finite descent finds a contained
ordinary core; uniqueness of that anchor opens the alternating-path theorem;
and the concrete source DFS then emits the target edge set.  Soundness is the
exact Boolean core test. -/
theorem directSourceCoreEnum_exact
    (anchors : List (IndexedMatching Q))
    (speciesOrder : List X) (hspecies : ∀ x, x ∈ speciesOrder)
    (reactionOrder : List R) (hreactions : ∀ r, r ∈ reactionOrder)
    (ordinaryGood csCore : Finset (X × R) → Prop)
    (coreTest : Finset (X × R) → Bool)
    (coreTest_exact : ∀ edges, coreTest edges = true ↔ csCore edges)
    (ordinary_complete : ∀ edges,
      edges ∈ (anchors.map IndexedMatching.edgeFinset).toFinset ↔
        IsCore ordinaryGood edges)
    (csCore_underlying_autocatalytic : ∀ edges,
      csCore edges → ordinaryGood edges)
    (csCore_representable : ∀ edges, csCore edges →
      ∃ target : IndexedMatching Q, target.edgeFinset = edges)
    (unique_anchors : ∀ anchor ∈ anchors,
      SimpleGraph.Subgraph.IsUniqueMatching anchor.subgraph) :
    ∀ edges, edges ∈ directSourceCoreEnum Q anchors speciesOrder
      reactionOrder coreTest ↔ csCore edges := by
  intro edges
  rw [mem_directSourceCoreEnum_iff]
  constructor
  · rintro ⟨htest, -⟩
    exact (coreTest_exact edges).1 htest
  · intro hcore
    obtain ⟨target, htarget⟩ := csCore_representable edges hcore
    obtain ⟨ordinaryEdges, hordinary_le, hordinary_core⟩ :=
      exists_core_le ordinaryGood (csCore_underlying_autocatalytic edges hcore)
    have hordinary_mem : ordinaryEdges ∈
        (anchors.map IndexedMatching.edgeFinset).toFinset :=
      (ordinary_complete ordinaryEdges).2 hordinary_core
    rw [List.mem_toFinset, List.mem_map] at hordinary_mem
    rcases hordinary_mem with ⟨anchor, hanchor, hanchorEdges⟩
    have hsubset : anchor.edgeFinset ⊆ target.edgeFinset := by
      rw [hanchorEdges, htarget]
      exact hordinary_le
    have hcontains : anchor.VertexContained target :=
      IndexedMatching.vertexContained_of_edgeFinset_subset hsubset
    have hemits : target.edgeFinset ∈
        sourceCandidateEdgeFinsets Q anchor speciesOrder reactionOrder :=
      target_edgeFinset_mem_sourceCandidateEdgeFinsets
        (unique_anchors anchor hanchor) hcontains
        speciesOrder hspecies reactionOrder hreactions
    refine ⟨(coreTest_exact edges).2 hcore, anchor, hanchor, ?_⟩
    simpa [htarget] using hemits

end AutocatalyticCS
