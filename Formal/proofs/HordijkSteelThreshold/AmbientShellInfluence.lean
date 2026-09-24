import proofs.HordijkSteelThreshold.AmbientExplorationDominates

namespace HordijkSteelThreshold

open RAF RAF.Polymer RAF.Concrete

/-- The nongateway reaction block having one fixed product length. -/
def nonseedProductShell (n L : Nat) : Finset (Reaction n) :=
  Finset.univ.filter fun r =>
    ¬ RevSeedReaction (binaryPolymerCRS n 2) r ∧ reactionProductLength r = L

/-- Close one product-length block in the ambient upper exploration. -/
noncomputable def ambientShellClosedReactionSet {n : Nat}
    (bulk : Set (NonseedCoord n)) (J : Finset (PolymerSeedReaction n 2))
    (L : Nat) : Finset (Reaction n) :=
  ambientSeededReactionSet bulk J \ nonseedProductShell n L

/-- Open every reaction in one nongateway product-length block. -/
noncomputable def ambientShellOpenedReactionSet {n : Nat}
    (bulk : Set (NonseedCoord n)) (J : Finset (PolymerSeedReaction n 2))
    (L : Nat) : Finset (Reaction n) :=
  ambientSeededReactionSet bulk J ∪ nonseedProductShell n L

theorem ambientShellClosed_subset {n : Nat}
    (bulk : Set (NonseedCoord n)) (J : Finset (PolymerSeedReaction n 2))
    (L : Nat) :
    ambientShellClosedReactionSet bulk J L ⊆
      ambientSeededReactionSet bulk J := by
  exact Finset.sdiff_subset

theorem ambient_subset_shellOpened {n : Nat}
    (bulk : Set (NonseedCoord n)) (J : Finset (PolymerSeedReaction n 2))
    (L : Nat) :
    ambientSeededReactionSet bulk J ⊆
      ambientShellOpenedReactionSet bulk J L := by
  exact Finset.subset_union_left

/-- All molecules reached at some finite reversible-closure time from a
specified reaction set. -/
noncomputable def reactionClosureMolecules {n : Nat}
    (S : Finset (Reaction n)) : Finset (Molecule n) := by
  classical
  exact Finset.univ.filter fun x =>
    ∃ k, x ∈ revClosureAt (binaryPolymerCRS n 2) S k

@[simp] theorem mem_reactionClosureMolecules {n : Nat}
    (S : Finset (Reaction n)) (x : Molecule n) :
    x ∈ reactionClosureMolecules S ↔
      ∃ k, x ∈ revClosureAt (binaryPolymerCRS n 2) S k := by
  classical
  simp [reactionClosureMolecules]

theorem reactionClosureMolecules_mono {n : Nat}
    {S T : Finset (Reaction n)} (hST : S ⊆ T) :
    reactionClosureMolecules S ⊆ reactionClosureMolecules T := by
  intro x hx
  obtain ⟨k, hk⟩ := (mem_reactionClosureMolecules S x).mp hx
  exact (mem_reactionClosureMolecules T x).mpr
    ⟨k, revClosureAt_mono_reactions _ hST k hk⟩

/-- The exact finite-shell influence sandwich.  Every ambient closure lies
between the closures obtained by closing and opening that entire shell. -/
theorem ambient_shell_closure_sandwich {n : Nat}
    (bulk : Set (NonseedCoord n)) (J : Finset (PolymerSeedReaction n 2))
    (L : Nat) :
    reactionClosureMolecules (ambientShellClosedReactionSet bulk J L) ⊆
      ambientSeededClosureMolecules bulk J ∧
    ambientSeededClosureMolecules bulk J ⊆
      reactionClosureMolecules (ambientShellOpenedReactionSet bulk J L) := by
  constructor
  · intro x hx
    obtain ⟨k, hk⟩ := (mem_reactionClosureMolecules _ x).mp hx
    exact (mem_ambientSeededClosureMolecules bulk J x).mpr
      ⟨k, revClosureAt_mono_reactions _
        (ambientShellClosed_subset bulk J L) k hk⟩
  · intro x hx
    obtain ⟨k, hk⟩ := (mem_ambientSeededClosureMolecules bulk J x).mp hx
    exact (mem_reactionClosureMolecules _ x).mpr
      ⟨k, revClosureAt_mono_reactions _
        (ambient_subset_shellOpened bulk J L) k hk⟩

/-- Subcritical shell certificate: if even the all-open intervention on one
shell is below half density, then the original ambient exploration is below
half density. -/
theorem ambient_not_macro_of_shellOpened_not_macro {n : Nat}
    (bulk : Set (NonseedCoord n)) (J : Finset (PolymerSeedReaction n 2))
    (L : Nat)
    (hopen : 2 * (reactionClosureMolecules
      (ambientShellOpenedReactionSet bulk J L)).card <
        Fintype.card (Molecule n)) :
    2 * (ambientSeededClosureMolecules bulk J).card <
      Fintype.card (Molecule n) := by
  have hcard := Finset.card_le_card
    (ambient_shell_closure_sandwich bulk J L).2
  omega

/-- Supercritical shell certificate: if the all-closed intervention is already
macroscopic, then the original ambient exploration is macroscopic. -/
theorem ambient_macro_of_shellClosed_macro {n : Nat}
    (bulk : Set (NonseedCoord n)) (J : Finset (PolymerSeedReaction n 2))
    (L : Nat)
    (hclosed : Fintype.card (Molecule n) ≤
      2 * (reactionClosureMolecules
        (ambientShellClosedReactionSet bulk J L)).card) :
    Fintype.card (Molecule n) ≤
      2 * (ambientSeededClosureMolecules bulk J).card := by
  exact hclosed.trans (Nat.mul_le_mul_left 2 <|
    Finset.card_le_card (ambient_shell_closure_sandwich bulk J L).1)

end HordijkSteelThreshold
