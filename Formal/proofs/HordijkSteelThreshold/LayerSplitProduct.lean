import proofs.HordijkSteelThreshold.LayerSplitProfile

namespace HordijkSteelThreshold

open RAF RAF.Polymer RAF.Concrete

theorem finProdFinEquiv_symm_fst_val {a b : Nat} (x : Fin (a * b)) :
    ((finProdFinEquiv.symm x).1).val = x.val / b := rfl

theorem finProdFinEquiv_symm_snd_val {a b : Nat} (x : Fin (a * b)) :
    ((finProdFinEquiv.symm x).2).val = x.val % b := rfl

theorem castFinCongrArg_val {a b : Nat} (h : a = b) (x : Fin a) :
    (cast (congrArg Fin h) x).val = x.val := by
  cases h
  rfl

theorem mul_sub_mul_le_deficit_sum {a b x y : Nat}
    (hx : x ≤ a) (hy : y ≤ b) :
    a * b - x * y ≤ (a - x) * b + (b - y) * a := by
  have hxb : x * b ≤ a * b := Nat.mul_le_mul_right b hx
  have hxy : x * y ≤ x * b := Nat.mul_le_mul_left x hy
  have hmono : x * (b - y) ≤ a * (b - y) :=
    Nat.mul_le_mul_right (b - y) hx
  calc
    a * b - x * y = (a * b - x * b) + (x * b - x * y) :=
      (tsub_add_tsub_cancel hxb hxy).symm
    _ = (a - x) * b + x * (b - y) := by
      rw [← Nat.sub_mul]
      congr 1
      exact (Nat.mul_sub_left_distrib x b y).symm
    _ ≤ (a - x) * b + a * (b - y) := Nat.add_le_add_left hmono _
    _ = (a - x) * b + (b - y) * a := by
      rw [Nat.mul_comm a (b - y)]

/-- The prefix/suffix code pair obtained by cutting a length-`m` word at a
fixed nontrivial split. -/
def splitLayerWordEquiv (m : Nat) (i : Fin (m - 1)) :
    Word m ≃ Word (i.val + 1) × Word (m - (i.val + 1)) := by
  have hle : i.val + 1 ≤ m := by omega
  have hsum : (i.val + 1) + (m - (i.val + 1)) = m := by omega
  have hpow : 2 ^ m = 2 ^ (i.val + 1) * 2 ^ (m - (i.val + 1)) := by
    rw [← pow_add, hsum]
  exact (Equiv.cast (congrArg Fin hpow)).trans finProdFinEquiv.symm

/-- Words of one exact length whose ambient molecules lie in a pool. -/
noncomputable def layerPoolWords {n l : Nat} (hl : 1 ≤ l) (hln : l ≤ n)
    (U : Finset (Molecule n)) : Finset (Word l) := by
  classical
  exact Finset.univ.filter fun w => layerMolecule hl hln w ∈ U

@[simp] theorem mem_layerPoolWords {n l : Nat} (hl : 1 ≤ l) (hln : l ≤ n)
    (U : Finset (Molecule n)) (w : Word l) :
    w ∈ layerPoolWords hl hln U ↔ layerMolecule hl hln w ∈ U := by
  simp [layerPoolWords]

/-- The concrete left factor at a layer split is the ambient molecule of the
prefix component of `splitLayerWordEquiv`. -/
theorem reactionLeft_layerReactionAtSplit_eq {n m : Nat}
    (hm : 2 ≤ m) (hmn : m ≤ n) (w : Word m) (i : Fin (m - 1)) :
    reactionLeft (layerReactionAtSplit hm hmn w i) =
      layerMolecule (by omega) (by omega)
        (splitLayerWordEquiv m i w).1 := by
  apply Sigma.ext
  · apply Fin.ext
    simp [reactionLeft, layerReactionAtSplit, reactionAtSplit, layerMolecule,
      moleculeOfCode, reactionLeftLength]
  · apply (Fin.heq_ext_iff (by
      simp [reactionLeft, layerReactionAtSplit, reactionAtSplit, layerMolecule,
        moleculeOfCode, reactionLeftLength])).2
    simp [reactionLeft, layerReactionAtSplit, layerMolecule, moleculeOfCode,
      reactionAtSplit, splitCodes, splitLayerWordEquiv, reactionLeftLength]
    calc
      _ = (Fin.cast _ w).val / 2 ^ (m - 1 - i.val) :=
        finProdFinEquiv_symm_fst_val _
      _ = _ := by
        simp only [Fin.val_cast]
        rw [show m - 1 - i.val = m - (i.val + 1) by omega]
        rw [castFinCongrArg_val (show
          2 ^ m = 2 ^ (i.val + 1) * 2 ^ (m - (i.val + 1)) by
            rw [← pow_add]
            congr 1
            omega)]

/-- The corresponding right-factor identity. -/
theorem reactionRight_layerReactionAtSplit_eq {n m : Nat}
    (hm : 2 ≤ m) (hmn : m ≤ n) (w : Word m) (i : Fin (m - 1)) :
    reactionRight (layerReactionAtSplit hm hmn w i) =
      layerMolecule (by omega) (by omega)
        (splitLayerWordEquiv m i w).2 := by
  apply Sigma.ext
  · apply Fin.ext
    simp [reactionRight, layerReactionAtSplit, reactionAtSplit, layerMolecule,
      moleculeOfCode, reactionRightLength]
    omega
  · apply (Fin.heq_ext_iff (by
      simp [reactionRight, layerReactionAtSplit, reactionAtSplit, layerMolecule,
        moleculeOfCode, reactionRightLength]
      omega)).2
    simp [reactionRight, layerReactionAtSplit, layerMolecule, moleculeOfCode,
      reactionAtSplit, splitCodes, splitLayerWordEquiv, reactionRightLength]
    calc
      _ = (Fin.cast _ w).val % 2 ^ (m - 1 - i.val) :=
        finProdFinEquiv_symm_snd_val _
      _ = _ := by
        simp only [Fin.val_cast]
        rw [show m - 1 - i.val = m - (i.val + 1) by omega]
        rw [castFinCongrArg_val (show
          2 ^ m = 2 ^ (i.val + 1) * 2 ^ (m - (i.val + 1)) by
            rw [← pow_add]
            congr 1
            omega)]

theorem mem_layerSplitViableTargets_iff {n m : Nat}
    (hm : 2 ≤ m) (hmn : m ≤ n) (A B : Finset (Molecule n))
    (i : Fin (m - 1)) (w : Word m) :
    w ∈ layerSplitViableTargets hm hmn A B i ↔
      (splitLayerWordEquiv m i w).1 ∈
          layerPoolWords (l := i.val + 1) (by omega) (by omega) (A ∪ B) ∧
        (splitLayerWordEquiv m i w).2 ∈
          layerPoolWords (l := m - (i.val + 1)) (by omega) (by omega) (A ∪ B) := by
  rw [mem_layerPoolWords, mem_layerPoolWords]
  simp only [layerSplitViableTargets, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [reactionLeft_layerReactionAtSplit_eq,
    reactionRight_layerReactionAtSplit_eq]

/-- At a fixed split, factor-viable target words are exactly the Cartesian
product of the surviving words in the two factor layers. -/
theorem card_layerSplitViableTargets_eq_mul {n m : Nat}
    (hm : 2 ≤ m) (hmn : m ≤ n) (A B : Finset (Molecule n))
    (i : Fin (m - 1)) :
    (layerSplitViableTargets hm hmn A B i).card =
      (layerPoolWords (l := i.val + 1) (by omega) (by omega) (A ∪ B)).card *
        (layerPoolWords (l := m - (i.val + 1)) (by omega) (by omega) (A ∪ B)).card := by
  classical
  let e := splitLayerWordEquiv m i
  let L := layerPoolWords (n := n) (l := i.val + 1)
    (by omega) (by omega) (A ∪ B)
  let R := layerPoolWords (n := n) (l := m - (i.val + 1))
    (by omega) (by omega) (A ∪ B)
  have hmap :
      (layerSplitViableTargets hm hmn A B i).map e.toEmbedding = L.product R := by
    ext z
    simp [e, L, R, mem_layerSplitViableTargets_iff]
  calc
    (layerSplitViableTargets hm hmn A B i).card =
        ((layerSplitViableTargets hm hmn A B i).map e.toEmbedding).card := by
      rw [Finset.card_map]
    _ = (L.product R).card := congrArg Finset.card hmap
    _ = L.card * R.card := Finset.card_product L R
    _ = _ := rfl

/-- Exact deficit of one split-position family from the full target layer. -/
theorem card_layerSplitMissingTargets_eq_sub {n m : Nat}
    (hm : 2 ≤ m) (hmn : m ≤ n) (A B : Finset (Molecule n))
    (i : Fin (m - 1)) :
    ((Finset.univ : Finset (Word m)) \
      layerSplitViableTargets hm hmn A B i).card =
      2 ^ m -
        (layerPoolWords (l := i.val + 1) (by omega) (by omega) (A ∪ B)).card *
          (layerPoolWords (l := m - (i.val + 1))
            (by omega) (by omega) (A ∪ B)).card := by
  rw [Finset.card_sdiff]
  simp only [Finset.inter_univ]
  rw [card_layerSplitViableTargets_eq_mul]
  simp

/-- A split family can be missing only because its left or right factor layer
is missing words.  The bound is linear in those two layer deficits. -/
theorem card_layerSplitMissingTargets_le_factorDeficits {n m dl dr : Nat}
    (hm : 2 ≤ m) (hmn : m ≤ n) (A B : Finset (Molecule n))
    (i : Fin (m - 1))
    (hleft : 2 ^ (i.val + 1) -
      (layerPoolWords (l := i.val + 1) (by omega) (by omega) (A ∪ B)).card ≤ dl)
    (hright : 2 ^ (m - (i.val + 1)) -
      (layerPoolWords (l := m - (i.val + 1))
        (by omega) (by omega) (A ∪ B)).card ≤ dr) :
    ((Finset.univ : Finset (Word m)) \
      layerSplitViableTargets hm hmn A B i).card ≤
        dl * 2 ^ (m - (i.val + 1)) + dr * 2 ^ (i.val + 1) := by
  let L := layerPoolWords (n := n) (l := i.val + 1)
    (by omega) (by omega) (A ∪ B)
  let R := layerPoolWords (n := n) (l := m - (i.val + 1))
    (by omega) (by omega) (A ∪ B)
  have hL : L.card ≤ 2 ^ (i.val + 1) := by
    simpa [L] using Finset.card_le_univ L
  have hR : R.card ≤ 2 ^ (m - (i.val + 1)) := by
    simpa [R] using Finset.card_le_univ R
  have hpow :
      2 ^ m = 2 ^ (i.val + 1) * 2 ^ (m - (i.val + 1)) := by
    rw [← pow_add]
    congr 1
    omega
  rw [card_layerSplitMissingTargets_eq_sub]
  rw [hpow]
  calc
    2 ^ (i.val + 1) * 2 ^ (m - (i.val + 1)) - L.card * R.card ≤
        (2 ^ (i.val + 1) - L.card) * 2 ^ (m - (i.val + 1)) +
          (2 ^ (m - (i.val + 1)) - R.card) * 2 ^ (i.val + 1) :=
      mul_sub_mul_le_deficit_sum hL hR
    _ ≤ dl * 2 ^ (m - (i.val + 1)) + dr * 2 ^ (i.val + 1) := by
      exact Nat.add_le_add
        (Nat.mul_le_mul_right _ hleft) (Nat.mul_le_mul_right _ hright)

/-- Factor-layer deficit control feeds directly into the overlap-safe
missing-split tail, uniformly over all split positions. -/
theorem layer_splitMissingTail_le_factorDeficits {n m b d : Nat}
    (hm : 2 ≤ m) (hmn : m ≤ n) (A B : Finset (Molecule n))
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
      dl i * 2 ^ (m - (i.val + 1)) + dr i * 2 ^ (i.val + 1) ≤ b) :
    d * (splitMissingTail
      (layerSplitViableTargets hm hmn A B) d).card ≤ (m - 1) * b := by
  apply layer_splitMissingTail_le_uniform hm hmn A B
  intro i
  exact (card_layerSplitMissingTargets_le_factorDeficits hm hmn A B i
    (hleft i) (hright i)).trans (hbudget i)

end HordijkSteelThreshold
