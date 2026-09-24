import proofs.HordijkSteelThreshold.TwoPoolPruning
import proofs.HordijkSteelThreshold.SplitLowerTail
import proofs.HordijkSteelThreshold.SplitCylinderProfile

namespace HordijkSteelThreshold

open RAF RAF.Polymer RAF.Concrete

/-- The ambient molecule represented by one word in a fixed product layer. -/
def layerMolecule {n m : Nat} (hm : 1 ≤ m) (hmn : m ≤ n)
    (w : Word m) : Molecule n :=
  moleculeOfCode hm hmn w

/-- The concrete split-position reaction for a word in a fixed layer. -/
def layerReactionAtSplit {n m : Nat} (hm : 2 ≤ m) (hmn : m ≤ n)
    (w : Word m) (i : Fin (m - 1)) : Reaction n := by
  let x := layerMolecule (hm.trans' (by omega)) hmn w
  have hi : i.val < x.1.val := by
    dsimp [x, layerMolecule, moleculeOfCode]
    exact i.2
  exact reactionAtSplit x ⟨i.val, hi⟩

/-- At one split position, the target words whose two concrete factors lie in
the current union of pools. -/
noncomputable def layerSplitViableTargets {n m : Nat}
    (hm : 2 ≤ m) (hmn : m ≤ n) (A B : Finset (Molecule n))
    (i : Fin (m - 1)) : Finset (Word m) := by
  classical
  exact Finset.univ.filter fun w =>
    reactionLeft (layerReactionAtSplit hm hmn w i) ∈ A ∪ B ∧
      reactionRight (layerReactionAtSplit hm hmn w i) ∈ A ∪ B

/-- The generic overlap-safe lower-tail inequality, instantiated on one exact
binary product layer. -/
theorem layer_splitMissingTail_le_uniform {n m b d : Nat}
    (hm : 2 ≤ m) (hmn : m ≤ n) (A B : Finset (Molecule n))
    (hmiss : ∀ i : Fin (m - 1),
      ((Finset.univ : Finset (Word m)) \
        layerSplitViableTargets hm hmn A B i).card ≤ b) :
    d * (splitMissingTail
      (layerSplitViableTargets hm hmn A B) d).card ≤ (m - 1) * b := by
  simpa using threshold_mul_card_splitMissingTail_le_uniform
    (layerSplitViableTargets hm hmn A B) b d hmiss

/-- Outside the exceptional lower tail, a word has more than `m-1-d`
factor-viable concrete split positions. -/
theorem layer_many_viable_splits_of_not_mem_tail {n m d : Nat}
    (hm : 2 ≤ m) (hmn : m ≤ n) (A B : Finset (Molecule n))
    {w : Word m}
    (hw : w ∉ splitMissingTail
      (layerSplitViableTargets hm hmn A B) d) :
    m - 1 < splitIncidenceCount
      (layerSplitViableTargets hm hmn A B) w + d := by
  simpa using many_viable_splits_of_not_mem_tail
    (layerSplitViableTargets hm hmn A B) d hw

/-- The incidence statistic on the word layer is exactly the number of
factor-viable split positions of its ambient molecule. -/
theorem splitIncidenceCount_layer_eq_crossViableSplitPositions_card
    {n m : Nat} (hm : 2 ≤ m) (hmn : m ≤ n)
    (A B : Finset (Molecule n)) (w : Word m) :
    splitIncidenceCount (layerSplitViableTargets hm hmn A B) w =
      (crossViableSplitPositions A B
        (layerMolecule (by omega) hmn w)).card := by
  classical
  change (∑ i : Fin (m - 1),
      if w ∈ layerSplitViableTargets hm hmn A B i then 1 else 0) =
    (Finset.univ.filter fun i : Fin (m - 1) =>
      reactionLeft (layerReactionAtSplit hm hmn w i) ∈ A ∪ B ∧
        reactionRight (layerReactionAtSplit hm hmn w i) ∈ A ∪ B).card
  simp [layerSplitViableTargets]

/-- A word outside the exceptional tail contributes at least `m-d` distinct
factor-viable concrete reactions to its ambient target molecule. -/
theorem layer_crossViableReactions_card_ge_of_not_mem_tail
    {n m d : Nat} (hm : 2 ≤ m) (hmn : m ≤ n)
    (A B : Finset (Molecule n)) {w : Word m}
    (hw : w ∉ splitMissingTail
      (layerSplitViableTargets hm hmn A B) d) :
    m - d ≤ (crossViableReactions A B
      (layerMolecule (by omega) hmn w)).card := by
  have hmany := layer_many_viable_splits_of_not_mem_tail
    hm hmn A B hw
  have heq := splitIncidenceCount_layer_eq_crossViableSplitPositions_card
    hm hmn A B w
  have hsplits : m - d ≤ (crossViableSplitPositions A B
      (layerMolecule (by omega) hmn w)).card := by
    omega
  exact hsplits.trans
    (card_crossViableSplitPositions_le_reactions A B
      (layerMolecule (by omega) hmn w))

theorem layerMolecule_injective {n m : Nat} (hm : 1 ≤ m) (hmn : m ≤ n) :
    Function.Injective (layerMolecule hm hmn) := by
  intro u v huv
  simpa [layerMolecule, moleculeOfCode, Sigma.mk.inj_iff, heq_eq_eq] using huv

/-- The complete ambient molecule layer represented by binary words of one
fixed length. -/
noncomputable def layerMolecules {n m : Nat} (hm : 1 ≤ m) (hmn : m ≤ n) :
    Finset (Molecule n) := by
  classical
  exact (Finset.univ : Finset (Word m)).image (layerMolecule hm hmn)

/-- Ambient targets represented by an arbitrary fixed block of words in one
product layer. -/
noncomputable def layerWordTargets {n m : Nat} (hm : 1 ≤ m) (hmn : m ≤ n)
    (W : Finset (Word m)) : Finset (Molecule n) := by
  classical
  exact W.image (layerMolecule hm hmn)

@[simp] theorem card_layerWordTargets {n m : Nat} (hm : 1 ≤ m) (hmn : m ≤ n)
    (W : Finset (Word m)) :
    (layerWordTargets hm hmn W).card = W.card := by
  classical
  exact Finset.card_image_of_injective W (layerMolecule_injective hm hmn)

theorem layerWordTargets_mono {n m : Nat} (hm : 1 ≤ m) (hmn : m ≤ n)
    {W V : Finset (Word m)} (hWV : W ⊆ V) :
    layerWordTargets hm hmn W ⊆ layerWordTargets hm hmn V := by
  classical
  intro x hx
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hx
  exact Finset.mem_image.mpr ⟨w, hWV hw, rfl⟩

@[simp] theorem card_layerMolecules {n m : Nat} (hm : 1 ≤ m) (hmn : m ≤ n) :
    (layerMolecules hm hmn).card = 2 ^ m := by
  classical
  rw [layerMolecules, Finset.card_image_of_injective _
    (layerMolecule_injective hm hmn)]
  simp

/-- Ambient targets corresponding to the nonexceptional words in one layer. -/
noncomputable def layerGoodMolecules {n m : Nat}
    (hm : 2 ≤ m) (hmn : m ≤ n) (A B : Finset (Molecule n)) (d : Nat) :
    Finset (Molecule n) := by
  classical
  exact ((Finset.univ : Finset (Word m)) \
    splitMissingTail (layerSplitViableTargets hm hmn A B) d).image
      (layerMolecule (by omega) hmn)

@[simp] theorem card_layerGoodMolecules {n m : Nat}
    (hm : 2 ≤ m) (hmn : m ≤ n) (A B : Finset (Molecule n)) (d : Nat) :
    (layerGoodMolecules hm hmn A B d).card =
      2 ^ m - (splitMissingTail
        (layerSplitViableTargets hm hmn A B) d).card := by
  classical
  rw [layerGoodMolecules, Finset.card_image_of_injective _
    (layerMolecule_injective (by omega) hmn), Finset.card_sdiff]
  simp

theorem layerGoodMolecules_subset_layerMolecules {n m d : Nat}
    (hm : 2 ≤ m) (hmn : m ≤ n) (A B : Finset (Molecule n)) :
    layerGoodMolecules hm hmn A B d ⊆ layerMolecules (by omega) hmn := by
  classical
  intro x hx
  rw [layerGoodMolecules] at hx
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hx
  exact Finset.mem_image.mpr ⟨w, Finset.mem_univ w, rfl⟩

/-- Any barrier selected from the good part of a layer carries the full
distinct-reaction energy, with no loss from overlaps between targets. -/
theorem layerGood_barrier_reaction_union_ge {n m d : Nat}
    (hm : 2 ≤ m) (hmn : m ≤ n) (A B T : Finset (Molecule n))
    (hT : T ⊆ layerGoodMolecules hm hmn A B d) :
    (m - d) * T.card ≤ (T.biUnion (crossViableReactions A B)).card := by
  apply card_biUnion_crossViableReactions_ge
  intro x hx
  have hxgood := hT hx
  rw [layerGoodMolecules] at hxgood
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hxgood
  have hwtail : w ∉ splitMissingTail
      (layerSplitViableTargets hm hmn A B) d :=
    (Finset.mem_sdiff.mp hw).2
  exact layer_crossViableReactions_card_ge_of_not_mem_tail
    hm hmn A B hwtail

/-- Cylinder-mixing form of the exceptional-layer estimate. -/
theorem layer_splitIncidenceLowTail_le_deviation {n m c d : Nat}
    (hm : 2 ≤ m) (hmn : m ≤ n) (A B : Finset (Molecule n)) :
    (d : ℝ) ^ 2 * (splitIncidenceLowTail
      (layerSplitViableTargets hm hmn A B) c d).card ≤
        splitIncidenceSquaredDeviation
          (layerSplitViableTargets hm hmn A B) c := by
  exact sq_mul_card_splitIncidenceLowTail_le_deviation
    (layerSplitViableTargets hm hmn A B) c d

/-- Outside the cylinder-discrepancy low tail, the exact source target has at
least `c-d` distinct viable reactions. -/
theorem layer_crossViableReactions_card_ge_of_not_mem_incidenceLowTail
    {n m c d : Nat} (hm : 2 ≤ m) (hmn : m ≤ n)
    (A B : Finset (Molecule n)) {w : Word m}
    (hw : w ∉ splitIncidenceLowTail
      (layerSplitViableTargets hm hmn A B) c d) :
    c - d ≤ (crossViableReactions A B
      (layerMolecule (by omega) hmn w)).card := by
  have hnot : ¬(splitIncidenceCount
      (layerSplitViableTargets hm hmn A B) w + d ≤ c) := by
    simpa [splitIncidenceLowTail] using hw
  have heq := splitIncidenceCount_layer_eq_crossViableSplitPositions_card
    hm hmn A B w
  have hsplits : c - d ≤ (crossViableSplitPositions A B
      (layerMolecule (by omega) hmn w)).card := by
    omega
  exact hsplits.trans
    (card_crossViableSplitPositions_le_reactions A B
      (layerMolecule (by omega) hmn w))

end HordijkSteelThreshold
