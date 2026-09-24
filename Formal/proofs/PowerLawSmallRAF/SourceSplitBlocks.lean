import proofs.PowerLawSmallRAF.SourceCatalyzedSplitCore
import proofs.PowerLawSmallRAF.SourcePowerLawTraceProbability

namespace PowerLawSmallRAF

open RAF RAF.Polymer RAF.Concrete

/-- The complete literal split-position block having product `x`. -/
def sourceSplitBlock {n : Nat} (x : Molecule n) : Finset (Reaction n) :=
  Finset.univ.map
    ⟨fun s : Fin x.1.val => ⟨x.1, (x.2, s)⟩,
      fun _ _ h => by simpa using h⟩

@[simp] theorem card_sourceSplitBlock {n : Nat} (x : Molecule n) :
    (sourceSplitBlock x).card = molLength x - 1 := by
  rw [sourceSplitBlock, Finset.card_map, Finset.card_univ,
    Fintype.card_fin]
  simp [molLength]

theorem mem_sourceSplitBlock_iff {n : Nat} (x : Molecule n)
    (r : Reaction n) :
    r ∈ sourceSplitBlock x ↔ reactionProduct r = x := by
  constructor
  · intro hr
    rw [sourceSplitBlock, Finset.mem_map] at hr
    obtain ⟨s, _, rfl⟩ := hr
    rfl
  · intro hr
    rw [sourceSplitBlock, Finset.mem_map]
    subst x
    exact ⟨r.2.2, Finset.mem_univ _, rfl⟩

theorem sourceSplitBlock_disjoint {n : Nat} {x z : Molecule n}
    (hxz : x ≠ z) : Disjoint (sourceSplitBlock x) (sourceSplitBlock z) := by
  rw [Finset.disjoint_left]
  intro r hrx hrz
  apply hxz
  exact (mem_sourceSplitBlock_iff x r).mp hrx |>.symm.trans
    ((mem_sourceSplitBlock_iff z r).mp hrz)

/-- Because product words label disjoint reaction fibres, block cardinalities
add without overlap. -/
theorem card_biUnion_sourceSplitBlock {n : Nat}
    (T : Finset (Molecule n)) :
    (T.biUnion sourceSplitBlock).card =
      ∑ x ∈ T, (molLength x - 1) := by
  have hpair : (T : Set (Molecule n)).PairwiseDisjoint sourceSplitBlock := by
    intro x hx z hz hxz
    exact sourceSplitBlock_disjoint hxz
  rw [Finset.card_biUnion hpair]
  apply Finset.sum_congr rfl
  intro x hx
  exact card_sourceSplitBlock x

theorem sourceCatalyzedSplitCore_iff_blocks {n : Nat}
    (config : SourceMoleculeFibreConfig n) :
    SourceCatalyzedSplitCore config ↔
      ∀ x : Molecule n, 2 < molLength x →
        ∃ r ∈ sourceSplitBlock x, ∃ y : Molecule n, r ∈ config y := by
  constructor
  · intro h x hx
    obtain ⟨r, hrx, y, hy⟩ := h x hx
    exact ⟨r, (mem_sourceSplitBlock_iff x r).2 hrx, y, hy⟩
  · intro h x hx
    obtain ⟨r, hrx, y, hy⟩ := h x hx
    exact ⟨r, (mem_sourceSplitBlock_iff x r).1 hrx, y, hy⟩

/-- Exact source mass that every molecule fibre misses one product's entire
split block.  This is the atomic bad event in the PL59 product formula. -/
theorem source_splitBlock_jointMiss_mass {n : Nat}
    (a : ℝ) (ha : 1 < a) (hn : 4 ≤ n) (x : Molecule n) :
    (∑ config : SourceMoleculeFibreConfig n,
      if ∀ y : Molecule n, Disjoint (config y) (sourceSplitBlock x) then
        sourcePowerLawConfigWeight a n config else 0) =
      coverageMissProfile (cappedZipfDegreeMass a (sourceReactionCount n))
          (sourceReactionCount n) (molLength x - 1) ^
        sourceMoleculeCount n := by
  have hcard : (Finset.univ : Finset (Molecule n)).card =
      sourceMoleculeCount n := by
    rw [Finset.card_univ, card_binaryMolecule_eq_sourceMoleculeCount]
  have hevent (config : SourceMoleculeFibreConfig n) :
      (∀ y : Molecule n, Disjoint (config y) (sourceSplitBlock x)) ↔
      (∀ y : ↥(Finset.univ : Finset (Molecule n)),
        Disjoint (config y) (sourceSplitBlock x)) := by
    constructor
    · intro h y
      exact h y
    · intro h y
      exact h ⟨y, Finset.mem_univ y⟩
  simp_rw [hevent]
  rw [source_jointMiss_mass_eq_pow a ha hn
    (Finset.univ : Finset (Molecule n)) (sourceSplitBlock x),
    card_sourceSplitBlock, hcard]

end PowerLawSmallRAF
