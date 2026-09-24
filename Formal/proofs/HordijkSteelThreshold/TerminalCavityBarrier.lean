import proofs.HordijkSteelThreshold.CavityWidthProbability
import proofs.HordijkSteelThreshold.LayerSplitProduct

namespace HordijkSteelThreshold

open MeasureTheory ProbabilityTheory unitInterval
open RAF RAF.Polymer RAF.Concrete

/-- In one exact molecule layer, targets with fewer than `m-delta` viable
reactions are contained in the overlap-safe missing-split tail. -/
theorem card_layer_lowViable_le_splitMissingTail
    {n m delta : Nat} (hm : 2 ≤ m) (hmn : m ≤ n)
    (A B : Finset (Molecule n)) :
    ((layerMolecules (by omega) hmn).filter fun x =>
      (crossViableReactions A B x).card < m - delta).card ≤
      (splitMissingTail
        (layerSplitViableTargets hm hmn A B) delta).card := by
  classical
  let Low := (layerMolecules (by omega) hmn).filter fun x =>
    (crossViableReactions A B x).card < m - delta
  let Good := layerGoodMolecules hm hmn A B delta
  have hGood : Good ⊆ layerMolecules (by omega) hmn :=
    layerGoodMolecules_subset_layerMolecules hm hmn A B
  have hLow : Low ⊆ layerMolecules (by omega) hmn \ Good := by
    intro x hx
    have hx' := Finset.mem_filter.mp hx
    refine Finset.mem_sdiff.mpr ⟨hx'.1, ?_⟩
    intro hxGood
    have hviableUnion := layerGood_barrier_reaction_union_ge
      hm hmn A B {x} (by simpa [Good] using hxGood)
    have hviable : m - delta ≤ (crossViableReactions A B x).card := by
      simpa using hviableUnion
    omega
  calc
    Low.card ≤ (layerMolecules (by omega) hmn \ Good).card :=
      Finset.card_le_card hLow
    _ = (layerMolecules (by omega) hmn).card - Good.card :=
      Finset.card_sdiff_of_subset hGood
    _ = 2 ^ m - (2 ^ m - (splitMissingTail
          (layerSplitViableTargets hm hmn A B) delta).card) := by
      rw [card_layerMolecules, card_layerGoodMolecules]
    _ = (splitMissingTail
          (layerSplitViableTargets hm hmn A B) delta).card := by
      have htail := Finset.card_le_univ
        (splitMissingTail (layerSplitViableTargets hm hmn A B) delta)
      have htail' : (splitMissingTail
          (layerSplitViableTargets hm hmn A B) delta).card ≤ 2 ^ m := by
        simpa using htail
      omega

/-- A uniform pair of factor-layer deficit budgets bounds the number of
low-viability targets.  This is the deterministic bridge from retained-pool
mass profiles to the terminal cavity estimate. -/
theorem card_layer_lowViable_le_of_factorDeficits
    {n m delta u r : Nat} (hm : 2 ≤ m) (hmn : m ≤ n)
    (A B : Finset (Molecule n))
    (dl dr : Fin (m - 1) → Nat)
    (hleft : ∀ i : Fin (m - 1),
      2 ^ (i.val + 1) -
        (layerPoolWords (l := i.val + 1)
          (by omega) (by omega) (A ∪ B)).card ≤ dl i)
    (hright : ∀ i : Fin (m - 1),
      2 ^ (m - (i.val + 1)) -
        (layerPoolWords (l := m - (i.val + 1))
          (by omega) (by omega) (A ∪ B)).card ≤ dr i)
    (hbudget : ∀ i : Fin (m - 1),
      dl i * 2 ^ (m - (i.val + 1)) + dr i * 2 ^ (i.val + 1) ≤ u)
    (hdelta : 0 < delta) (hscale : (m - 1) * u ≤ delta * r) :
    ((layerMolecules (by omega) hmn).filter fun x =>
      (crossViableReactions A B x).card < m - delta).card ≤ r := by
  have hlow : delta *
      ((layerMolecules (by omega) hmn).filter fun x =>
        (crossViableReactions A B x).card < m - delta).card ≤
      delta * (splitMissingTail
        (layerSplitViableTargets hm hmn A B) delta).card :=
    Nat.mul_le_mul_left delta
      (card_layer_lowViable_le_splitMissingTail hm hmn A B)
  have htail := layer_splitMissingTail_le_factorDeficits
    (b := u) (d := delta) hm hmn A B dl dr hleft hright hbudget
  apply le_of_mul_le_mul_left _ hdelta
  exact hlow.trans (htail.trans hscale)

/-- Exact terminal layer-width barrier.  The low-viability allowance is now
the concrete split-profile tail, so the only remaining deterministic inputs
are its cardinality and the retained closed-core mass. -/
theorem measure_terminalLayerWidth_large_of_splitTail_le
    {n foodLength k b m delta r t : Nat} (lambda : ℝ)
    (hm : 2 ≤ m) (hmn : m ≤ n)
    (T A : Finset (Molecule n)) :
    ambientPiMeasure n lambda {ω |
      crossPoolIter foodLength
          (closeTargetBlocks (fun y z => ω (y, z)) T) (A, A) (k + 1) =
        crossPoolIter foodLength
          (closeTargetBlocks (fun y z => ω (y, z)) T) (A, A) k ∧
      let S := crossPoolIter foodLength
        (closeTargetBlocks (fun y z => ω (y, z)) T) (A, A) k
      b ≤ S.2.card ∧
        r + t ≤ ((layerMolecules (by omega) hmn) ∩
          (leftTargetCavityWidth (foodLength := foodLength)
            (fun y z => ω (y, z)) T (A, A) k \ T)).card ∧
        (splitMissingTail
          (layerSplitViableTargets hm hmn S.1 S.2) delta).card ≤ r} ≤
      (Nat.choose (2 ^ m) t : ENNReal) *
        (toNNReal (σ (catalysisP n lambda)) : ENNReal) ^
          (b * ((m - delta) * t)) := by
  have hprob := measure_terminalLeftWidth_large_of_few_lowViable_exact_le
    (foodLength := foodLength) (k := k) (b := b)
    (d := m - delta) (r := r) (t := t) lambda T
    (layerMolecules (by omega) hmn) A
  calc
    ambientPiMeasure n lambda {ω |
        crossPoolIter foodLength
            (closeTargetBlocks (fun y z => ω (y, z)) T) (A, A) (k + 1) =
          crossPoolIter foodLength
            (closeTargetBlocks (fun y z => ω (y, z)) T) (A, A) k ∧
        let S := crossPoolIter foodLength
          (closeTargetBlocks (fun y z => ω (y, z)) T) (A, A) k
        b ≤ S.2.card ∧
          r + t ≤ ((layerMolecules (by omega) hmn) ∩
            (leftTargetCavityWidth (foodLength := foodLength)
              (fun y z => ω (y, z)) T (A, A) k \ T)).card ∧
          (splitMissingTail
            (layerSplitViableTargets hm hmn S.1 S.2) delta).card ≤ r} ≤
        ambientPiMeasure n lambda {ω |
          crossPoolIter foodLength
              (closeTargetBlocks (fun y z => ω (y, z)) T) (A, A) (k + 1) =
            crossPoolIter foodLength
              (closeTargetBlocks (fun y z => ω (y, z)) T) (A, A) k ∧
          let S := crossPoolIter foodLength
            (closeTargetBlocks (fun y z => ω (y, z)) T) (A, A) k
          b ≤ S.2.card ∧
            r + t ≤ ((layerMolecules (by omega) hmn) ∩
              (leftTargetCavityWidth (foodLength := foodLength)
                (fun y z => ω (y, z)) T (A, A) k \ T)).card ∧
            (((layerMolecules (by omega) hmn).filter fun x =>
              (crossViableReactions S.1 S.2 x).card < m - delta).card ≤ r)} := by
          apply measure_mono
          intro ω hω
          rcases hω with ⟨hfix, hb, hlarge, htail⟩
          refine ⟨hfix, hb, hlarge, ?_⟩
          exact (card_layer_lowViable_le_splitMissingTail hm hmn
            (crossPoolIter foodLength
              (closeTargetBlocks (fun y z => ω (y, z)) T) (A, A) k).1
            (crossPoolIter foodLength
              (closeTargetBlocks (fun y z => ω (y, z)) T) (A, A) k).2).trans htail
    _ ≤ (Nat.choose (2 ^ m) t : ENNReal) *
          (toNNReal (σ (catalysisP n lambda)) : ENNReal) ^
            (b * ((m - delta) * t)) := by
      simpa only [card_layerMolecules] using hprob

end HordijkSteelThreshold
