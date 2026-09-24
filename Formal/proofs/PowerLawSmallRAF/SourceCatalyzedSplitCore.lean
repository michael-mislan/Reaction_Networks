import proofs.PowerLawSmallRAF.SourceSelfGeneratingFibreRAF
import proofs.HordijkSteelThreshold.MarkedCoreAdapter

namespace PowerLawSmallRAF

open RAF RAF.Polymer RAF.Concrete HordijkSteelThreshold

/-- Every nonfood word has at least one literal split-position ligation channel
catalyzed somewhere in the source configuration. -/
def SourceCatalyzedSplitCore {n : Nat}
    (config : SourceMoleculeFibreConfig n) : Prop :=
  ∀ x : Molecule n, 2 < molLength x →
    ∃ r : Reaction n, reactionProduct r = x ∧
      ∃ y : Molecule n, r ∈ config y

theorem sourceCatalyzedSplitCore_isMarkedMoleculeCore {n : Nat}
    {config : SourceMoleculeFibreConfig n}
    (hcore : SourceCatalyzedSplitCore config) :
    IsMarkedMoleculeCore 2 (sourceCatalysisOfConfig config)
      (Finset.univ : Finset (Molecule n)) := by
  constructor
  · exact Finset.subset_univ _
  · intro x hx hlen
    obtain ⟨r, hprod, y, hy⟩ := hcore x hlen
    exact ⟨r, hprod, Finset.mem_univ _, Finset.mem_univ _,
      y, Finset.mem_univ _, hy⟩

/-- The catalyzed-split macro event produces an actual source reversible RAF
of at most the complete reaction-catalogue size. -/
theorem exists_source_revRAF_of_catalyzedSplitCore {n : Nat}
    (hn : 3 ≤ n) {config : SourceMoleculeFibreConfig n}
    (hcore : SourceCatalyzedSplitCore config) :
    ∃ S : Finset (Reaction n),
      S.card ≤ sourceReactionCount n ∧
      IsRevRAF (binaryPolymerCRS n 2) (sourceCatalysisOfConfig config) S := by
  let k : Fin n := ⟨2, by omega⟩
  let w : Word (k.val + 1) := ⟨0, by simp [k]⟩
  let x : Molecule n := ⟨k, w⟩
  have hnontrivial : ∃ z ∈ (Finset.univ : Finset (Molecule n)),
      2 < molLength z := by
    refine ⟨x, Finset.mem_univ x, ?_⟩
    simp [x, k, molLength]
  let S := markedCoreReactions (sourceCatalysisOfConfig config)
    (Finset.univ : Finset (Molecule n))
  have hraf : IsRevRAF (binaryPolymerCRS n 2)
      (sourceCatalysisOfConfig config) S :=
    markedCoreReactions_isRevRAF
      (sourceCatalyzedSplitCore_isMarkedMoleculeCore hcore) hnontrivial
  refine ⟨S, ?_, hraf⟩
  calc
    S.card ≤ (Finset.univ : Finset (Reaction n)).card :=
      Finset.card_le_card (Finset.subset_univ S)
    _ = Fintype.card (Reaction n) := Finset.card_univ
    _ = sourceReactionCount n := card_binaryReaction_eq_sourceReactionCount
      (by omega)

end PowerLawSmallRAF
