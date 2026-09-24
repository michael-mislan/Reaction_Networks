import proofs.HordijkSteelThreshold.ExponentialWitnessSize

namespace HordijkSteelThreshold

open RAF RAF.Polymer RAF.Concrete

/-- The ordinary reactions named by a finite gateway trace. -/
def forcedReactionSet {n : Nat} (J : Finset (PolymerSeedReaction n 2)) :
    Finset (Reaction n) :=
  J.image Subtype.val

/-- Nongateway reactions that have at least one catalyst somewhere in the
ambient molecule universe of the bulk sample. -/
noncomputable def ambientOpenBulkReactions {n : Nat}
    (bulk : Set (NonseedCoord n)) : Finset (Reaction n) := by
  classical
  exact Finset.univ.filter fun r =>
    ∃ h : ¬ RevSeedReaction (binaryPolymerCRS n 2) r,
      ∃ x : Molecule n, (x, ⟨r, h⟩) ∈ bulk

/-- Independent ambient-open upper exploration with the gateway trace forced. -/
noncomputable def ambientSeededReactionSet {n : Nat}
    (bulk : Set (NonseedCoord n))
    (J : Finset (PolymerSeedReaction n 2)) : Finset (Reaction n) :=
  forcedReactionSet J ∪ ambientOpenBulkReactions bulk

theorem gatewaySeededMaxRAF_subset_ambientSeeded {n : Nat}
    (bulk : Set (NonseedCoord n))
    (J : Finset (PolymerSeedReaction n 2)) :
    gatewaySeededMaxRAF bulk J ⊆ ambientSeededReactionSet bulk J := by
  classical
  intro r hr
  simp only [gatewaySeededMaxRAF, Finset.mem_biUnion] at hr
  obtain ⟨S, hSF, hrS⟩ := hr
  have hS : IsGatewaySeededRAF bulk J S :=
    (mem_gatewaySeededRAFFamily bulk J S).mp hSF
  rcases hS.2.2 r hrS with hforced | ⟨x, _k, _hx, hcat⟩
  · apply Finset.mem_union_left
    obtain ⟨hseed, hrJ⟩ := hforced
    exact Finset.mem_image.mpr ⟨⟨r, hseed⟩, hrJ, rfl⟩
  · apply Finset.mem_union_right
    simp only [ambientOpenBulkReactions, Finset.mem_filter,
      Finset.mem_univ, true_and]
    have hnonseed : ¬ RevSeedReaction (binaryPolymerCRS n 2) r := by
      intro hseed
      simp [bulkCatalysis, hseed] at hcat
    refine ⟨hnonseed, x, ?_⟩
    simpa [bulkCatalysis, hnonseed] using hcat

/-- Molecules reached by the independent ambient-open upper exploration. -/
noncomputable def ambientSeededClosureMolecules {n : Nat}
    (bulk : Set (NonseedCoord n))
    (J : Finset (PolymerSeedReaction n 2)) : Finset (Molecule n) := by
  classical
  exact Finset.univ.filter fun x => ∃ k,
    x ∈ revClosureAt (binaryPolymerCRS n 2)
      (ambientSeededReactionSet bulk J) k

@[simp] theorem mem_ambientSeededClosureMolecules {n : Nat}
    (bulk : Set (NonseedCoord n))
    (J : Finset (PolymerSeedReaction n 2)) (x : Molecule n) :
    x ∈ ambientSeededClosureMolecules bulk J ↔ ∃ k,
      x ∈ revClosureAt (binaryPolymerCRS n 2)
        (ambientSeededReactionSet bulk J) k := by
  classical
  simp [ambientSeededClosureMolecules]

theorem seededClosureMolecules_subset_ambient {n : Nat}
    (bulk : Set (NonseedCoord n))
    (J : Finset (PolymerSeedReaction n 2)) :
    seededClosureMolecules bulk J ⊆ ambientSeededClosureMolecules bulk J := by
  intro x hx
  obtain ⟨k, hk⟩ := (mem_seededClosureMolecules bulk J x).mp hx
  exact (mem_ambientSeededClosureMolecules bulk J x).mpr
    ⟨k, revClosureAt_mono_reactions _
      (gatewaySeededMaxRAF_subset_ambientSeeded bulk J) k hk⟩

/-- Exact event domination: true macroscopic seeded ignition implies
macroscopic closure in the independent ambient-open reaction exploration. -/
theorem macroEvent_implies_ambient_macro {n : Nat}
    (J : Finset (PolymerSeedReaction n 2))
    {bulk : Set (NonseedCoord n)} (hmacro : bulk ∈ SeededBulkMacroEvent n J) :
    Fintype.card (Molecule n) ≤
      2 * (ambientSeededClosureMolecules bulk J).card := by
  exact hmacro.trans (Nat.mul_le_mul_left 2
    (Finset.card_le_card (seededClosureMolecules_subset_ambient bulk J)))

end HordijkSteelThreshold
