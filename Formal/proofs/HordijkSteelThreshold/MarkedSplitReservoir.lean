import proofs.HordijkSteelThreshold.FamilyOpenProbability
import proofs.HordijkSteelThreshold.AdaptiveMixtureBound
import proofs.HordijkSteelThreshold.LayerSplitProfile
import proofs.HordijkSteelThreshold.LayerSplitProduct
import proofs.HordijkSteelThreshold.TargetFamilyVariance

namespace HordijkSteelThreshold

open MeasureTheory ProbabilityTheory unitInterval
open RAF RAF.Polymer RAF.Concrete

/-- The first `k` split reactions of one exact-layer target.  These can be
reserved as an auxiliary mark block, leaving every remaining split coordinate
available for the support construction. -/
noncomputable def layerInitialSplitReactions {n m k : Nat}
    (hm : 2 ≤ m) (hmn : m ≤ n) (hk : k ≤ m - 1) (w : Word m) :
    Finset (Reaction n) := by
  classical
  exact (Finset.univ : Finset (Fin k)).image fun i =>
    layerReactionAtSplit hm hmn w
      ⟨i.val, lt_of_lt_of_le i.isLt hk⟩

theorem layerReactionAtSplit_injective {n m : Nat}
    (hm : 2 ≤ m) (hmn : m ≤ n) (w : Word m) :
    Function.Injective (layerReactionAtSplit hm hmn w) := by
  intro i j hij
  unfold layerReactionAtSplit at hij
  apply Fin.ext
  exact congrArg Fin.val ((reactionAtSplit_injective
    (layerMolecule (hm.trans' (by omega)) hmn w)) hij)

@[simp] theorem card_layerInitialSplitReactions {n m k : Nat}
    (hm : 2 ≤ m) (hmn : m ≤ n) (hk : k ≤ m - 1) (w : Word m) :
    (layerInitialSplitReactions hm hmn hk w).card = k := by
  classical
  rw [layerInitialSplitReactions, Finset.card_image_of_injective]
  · simp
  · intro i j hij
    apply Fin.ext
    have hs := layerReactionAtSplit_injective hm hmn w hij
    have hsval := congrArg (fun z : Fin (m - 1) => z.val) hs
    exact hsval

/-- Every split reaction of one exact-layer target. -/
noncomputable def layerAllSplitReactions {n m : Nat}
    (hm : 2 ≤ m) (hmn : m ≤ n) (w : Word m) : Finset (Reaction n) := by
  classical
  exact (Finset.univ : Finset (Fin (m - 1))).image
    (layerReactionAtSplit hm hmn w)

@[simp] theorem card_layerAllSplitReactions {n m : Nat}
    (hm : 2 ≤ m) (hmn : m ≤ n) (w : Word m) :
    (layerAllSplitReactions hm hmn w).card = m - 1 := by
  classical
  rw [layerAllSplitReactions, Finset.card_image_of_injective]
  · simp
  · exact layerReactionAtSplit_injective hm hmn w

theorem layerInitialSplitReactions_subset_all {n m k : Nat}
    (hm : 2 ≤ m) (hmn : m ≤ n) (hk : k ≤ m - 1) (w : Word m) :
    layerInitialSplitReactions hm hmn hk w ⊆
      layerAllSplitReactions hm hmn w := by
  classical
  intro r hr
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hr
  apply Finset.mem_image.mpr
  exact ⟨⟨i.val, lt_of_lt_of_le i.isLt hk⟩, Finset.mem_univ _, rfl⟩

/-- The support reactions left after reserving the first `k` splits as marks. -/
noncomputable def layerRemainingSplitReactions {n m k : Nat}
    (hm : 2 ≤ m) (hmn : m ≤ n) (hk : k ≤ m - 1) (w : Word m) :
    Finset (Reaction n) :=
  layerAllSplitReactions hm hmn w \
    layerInitialSplitReactions hm hmn hk w

@[simp] theorem card_layerRemainingSplitReactions {n m k : Nat}
    (hm : 2 ≤ m) (hmn : m ≤ n) (hk : k ≤ m - 1) (w : Word m) :
    (layerRemainingSplitReactions hm hmn hk w).card = m - 1 - k := by
  rw [layerRemainingSplitReactions,
    Finset.card_sdiff_of_subset
      (layerInitialSplitReactions_subset_all hm hmn hk w),
    card_layerAllSplitReactions, card_layerInitialSplitReactions]

theorem layerRemainingSplitReactions_disjoint_initial {n m k : Nat}
    (hm : 2 ≤ m) (hmn : m ≤ n) (hk : k ≤ m - 1) (w : Word m) :
    Disjoint (layerRemainingSplitReactions hm hmn hk w)
      (layerInitialSplitReactions hm hmn hk w) := by
  exact Finset.sdiff_disjoint

/-- Factor-viable reactions for a layer target after removing the coordinates
reserved for its auxiliary mark. -/
noncomputable def unreservedCrossViableReactions {n m k : Nat}
    (hm : 2 ≤ m) (hmn : m ≤ n) (hk : k ≤ m - 1)
    (A B : Finset (Molecule n)) (w : Word m) : Finset (Reaction n) :=
  crossViableReactions A B (layerMolecule (by omega) hmn w) \
    layerInitialSplitReactions hm hmn hk w

/-- Reserving `k` target-local coordinates costs at most `k` from the exact
factor-viable support count.  Thus every word outside the split lower tail
retains the linear support energy `m - d - k`. -/
theorem card_unreservedCrossViableReactions_ge_of_not_mem_tail
    {n m d k : Nat} (hm : 2 ≤ m) (hmn : m ≤ n) (hk : k ≤ m - 1)
    (A B : Finset (Molecule n)) {w : Word m}
    (hw : w ∉ splitMissingTail
      (layerSplitViableTargets hm hmn A B) d) :
    m - d - k ≤
      (unreservedCrossViableReactions hm hmn hk A B w).card := by
  have hviable : m - d ≤
      (crossViableReactions A B
        (layerMolecule (by omega) hmn w)).card :=
    layer_crossViableReactions_card_ge_of_not_mem_tail
      hm hmn A B hw
  have hsplit :
      (crossViableReactions A B
        (layerMolecule (by omega) hmn w)).card ≤
        (unreservedCrossViableReactions hm hmn hk A B w).card + k := by
    simpa [unreservedCrossViableReactions, card_layerInitialSplitReactions]
      using (Finset.card_le_card_sdiff_add_card
        (s := crossViableReactions A B
          (layerMolecule (by omega) hmn w))
        (t := layerInitialSplitReactions hm hmn hk w))
  omega

/-- The words with too little unreserved support are contained in the same
overlap-safe split lower tail as before reservation. -/
theorem card_layer_lowUnreservedViableWords_le_splitMissingTail
    {n m delta k : Nat} (hm : 2 ≤ m) (hmn : m ≤ n)
    (hk : k ≤ m - 1) (A B : Finset (Molecule n)) :
    ((Finset.univ : Finset (Word m)).filter fun w =>
      (unreservedCrossViableReactions hm hmn hk A B w).card <
        m - delta - k).card ≤
      (splitMissingTail
        (layerSplitViableTargets hm hmn A B) delta).card := by
  apply Finset.card_le_card
  intro w hw
  have hlow := (Finset.mem_filter.mp hw).2
  by_contra htail
  have hhigh := card_unreservedCrossViableReactions_ge_of_not_mem_tail
    hm hmn hk A B htail
  omega

/-- Factor-layer deficit budgets therefore control the entire exceptional
set for the unreserved support family. -/
theorem layer_lowUnreservedViableWords_mul_le_factorDeficits
    {n m delta k b : Nat} (hm : 2 ≤ m) (hmn : m ≤ n)
    (hk : k ≤ m - 1) (A B : Finset (Molecule n))
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
    delta * ((Finset.univ : Finset (Word m)).filter fun w =>
      (unreservedCrossViableReactions hm hmn hk A B w).card <
        m - delta - k).card ≤ (m - 1) * b := by
  exact (Nat.mul_le_mul_left delta
    (card_layer_lowUnreservedViableWords_le_splitMissingTail
      hm hmn hk A B)).trans
    (layer_splitMissingTail_le_factorDeficits
      hm hmn A B dl dr hleft hright hbudget)

/-- All reserved label reactions over a block of target words. -/
noncomputable def layerInitialSplitReactionUnion {n m k : Nat}
    (hm : 2 ≤ m) (hmn : m ≤ n) (hk : k ≤ m - 1)
    (W : Finset (Word m)) : Finset (Reaction n) :=
  W.biUnion (layerInitialSplitReactions hm hmn hk)

/-- All unreserved viable support reactions over a block of target words. -/
noncomputable def layerUnreservedCrossViableReactionUnion {n m k : Nat}
    (hm : 2 ≤ m) (hmn : m ≤ n) (hk : k ≤ m - 1)
    (A B : Finset (Molecule n)) (W : Finset (Word m)) :
    Finset (Reaction n) :=
  W.biUnion (unreservedCrossViableReactions hm hmn hk A B)

/-- The entire reserved label field is coordinate-disjoint from the entire
unreserved support field, even for overlapping word blocks.  Distinct words
are separated by reaction product; the equal-word case is a set difference. -/
theorem layerInitialSplitReactionUnion_disjoint_unreservedUnion
    {n m k : Nat} (hm : 2 ≤ m) (hmn : m ≤ n) (hk : k ≤ m - 1)
    (A B : Finset (Molecule n)) (W V : Finset (Word m)) :
    Disjoint (layerInitialSplitReactionUnion hm hmn hk W)
      (layerUnreservedCrossViableReactionUnion hm hmn hk A B V) := by
  classical
  rw [Finset.disjoint_left]
  intro r hrReserved hrSupport
  obtain ⟨u, huW, hru⟩ := Finset.mem_biUnion.mp hrReserved
  obtain ⟨v, hvV, hrv⟩ := Finset.mem_biUnion.mp hrSupport
  obtain ⟨i, hi, hir⟩ := Finset.mem_image.mp hru
  have hprodReserved : reactionProduct r =
      layerMolecule (by omega) hmn u := by
    rw [← hir]
    rfl
  have hrvCross : r ∈ crossViableReactions A B
      (layerMolecule (by omega) hmn v) :=
    (Finset.mem_sdiff.mp hrv).1
  have hprodSupport : reactionProduct r =
      layerMolecule (by omega) hmn v :=
    (mem_crossViableReactions A B _ r).mp hrvCross |>.1
  have huv : u = v := by
    apply layerMolecule_injective (by omega) hmn
    exact hprodReserved.symm.trans hprodSupport
  subst v
  exact (Finset.mem_sdiff.mp hrv).2 hru

/-- The actual ambient-coordinate block read by all auxiliary labels. -/
noncomputable def layerReservedMarkBlock {n m k : Nat}
    (hm : 2 ≤ m) (hmn : m ≤ n) (hk : k ≤ m - 1)
    (C : Finset (Molecule n)) (W : Finset (Word m)) :
    Finset (AmbientCoord n) :=
  catalystPoolFamilyBlock C (layerInitialSplitReactionUnion hm hmn hk W)

/-- The ambient-coordinate block available for all unreserved support tests. -/
noncomputable def layerUnreservedSupportBlock {n m k : Nat}
    (hm : 2 ≤ m) (hmn : m ≤ n) (hk : k ≤ m - 1)
    (D A B : Finset (Molecule n)) (W : Finset (Word m)) :
    Finset (AmbientCoord n) :=
  catalystPoolFamilyBlock D
    (layerUnreservedCrossViableReactionUnion hm hmn hk A B W)

theorem layerReservedMarkBlock_disjoint_unreservedSupportBlock
    {n m k : Nat} (hm : 2 ≤ m) (hmn : m ≤ n) (hk : k ≤ m - 1)
    (C D A B : Finset (Molecule n)) (W V : Finset (Word m)) :
    Disjoint (layerReservedMarkBlock hm hmn hk C W)
      (layerUnreservedSupportBlock hm hmn hk D A B V) := by
  rw [Finset.disjoint_left]
  intro z hzReserved hzSupport
  have hrReserved := (Finset.mem_product.mp hzReserved).2
  have hrSupport := (Finset.mem_product.mp hzSupport).2
  exact Finset.disjoint_left.mp
    (layerInitialSplitReactionUnion_disjoint_unreservedUnion
      hm hmn hk A B W V) hrReserved hrSupport

/-- The whole auxiliary-label field is independent of the whole unreserved
support field.  Catalyst pools may differ and may overlap; only reaction
identity separation is needed. -/
theorem layerReservedMarkField_indep_unreservedSupportField
    {n m k : Nat} (hm : 2 ≤ m) (hmn : m ≤ n) (hk : k ≤ m - 1)
    (lambda : ℝ) (C D A B : Finset (Molecule n))
    (W V : Finset (Word m)) :
    IndepFun
      (fun (ω : AmbientCoord n → Prop)
        (z : layerReservedMarkBlock hm hmn hk C W) => ω z)
      (fun (ω : AmbientCoord n → Prop)
        (z : layerUnreservedSupportBlock hm hmn hk D A B V) => ω z)
      (ambientPiMeasure n lambda) := by
  exact (ambientCoordinate_iIndep n lambda).indepFun_finset
    (layerReservedMarkBlock hm hmn hk C W)
    (layerUnreservedSupportBlock hm hmn hk D A B V)
    (layerReservedMarkBlock_disjoint_unreservedSupportBlock
      hm hmn hk C D A B W V)
    (fun _ => measurable_pi_apply _)

/-- Auxiliary marked words, using a deterministic catalyst band only to
generate random labels.  These reserved coordinates are discarded from all
subsequent support tests. -/
local instance markedWordSetMeasurableSpace (m : Nat) :
    MeasurableSpace (Finset (Word m)) := ⊤

noncomputable def layerMarkedWords {n m k : Nat}
    (hm : 2 ≤ m) (hmn : m ≤ n) (hk : k ≤ m - 1)
    (C : Finset (Molecule n)) (W : Finset (Word m))
    (ω : AmbientCoord n → Prop) : Finset (Word m) := by
  classical
  exact W.filter fun w => catalystPoolFamilyOpen ω C
    (layerInitialSplitReactions hm hmn hk w)

/-- The same marked set computed only from the finite reserved field. -/
noncomputable def layerMarkedWordsFromField {n m k : Nat}
    (hm : 2 ≤ m) (hmn : m ≤ n) (hk : k ≤ m - 1)
    (C : Finset (Molecule n)) (W : Finset (Word m))
    (v : layerReservedMarkBlock hm hmn hk C W → Prop) :
    Finset (Word m) := by
  classical
  exact W.filter fun w => ∃ z : layerReservedMarkBlock hm hmn hk C W,
    z.1.2 ∈ layerInitialSplitReactions hm hmn hk w ∧ v z

theorem layerMarkedWords_eq_fromField {n m k : Nat}
    (hm : 2 ≤ m) (hmn : m ≤ n) (hk : k ≤ m - 1)
    (C : Finset (Molecule n)) (W : Finset (Word m))
    (ω : AmbientCoord n → Prop) :
    layerMarkedWords hm hmn hk C W ω =
      layerMarkedWordsFromField hm hmn hk C W
        (fun z => ω z) := by
  classical
  ext w
  simp only [layerMarkedWords, layerMarkedWordsFromField,
    Finset.mem_filter, and_congr_right_iff]
  intro hwW
  constructor
  · rintro ⟨r, hr, y, hy, hω⟩
    refine ⟨⟨(y, r), ?_⟩, hr, hω⟩
    show (y, r) ∈ C.product
      (layerInitialSplitReactionUnion hm hmn hk W)
    exact Finset.mem_product.mpr
      ⟨hy, Finset.mem_biUnion.mpr ⟨w, hwW, hr⟩⟩
  · rintro ⟨z, hr, hω⟩
    have hz := Finset.mem_product.mp z.property
    exact ⟨z.1.2, hr, z.1.1, hz.1, hω⟩

theorem layerMarkedWords_measurable {n m k : Nat}
    (hm : 2 ≤ m) (hmn : m ≤ n) (hk : k ≤ m - 1)
    (C : Finset (Molecule n)) (W : Finset (Word m)) :
    Measurable (layerMarkedWords hm hmn hk C W) := by
  exact measurable_of_finite _

/-- The selected marked reservoir itself, not just its raw coordinate field,
is independent of every unreserved support coordinate in the chosen block. -/
theorem layerMarkedWords_indep_unreservedSupportField
    {n m k : Nat} (hm : 2 ≤ m) (hmn : m ≤ n) (hk : k ≤ m - 1)
    (lambda : ℝ) (C D A B : Finset (Molecule n))
    (W V : Finset (Word m)) :
    IndepFun (layerMarkedWords hm hmn hk C W)
      (fun (ω : AmbientCoord n → Prop)
        (z : layerUnreservedSupportBlock hm hmn hk D A B V) => ω z)
      (ambientPiMeasure n lambda) := by
  have hfield := layerReservedMarkField_indep_unreservedSupportField
    hm hmn hk lambda C D A B W V
  have hcomp := hfield.comp
    (measurable_of_finite
      (layerMarkedWordsFromField hm hmn hk C W)) measurable_id
  have heq : layerMarkedWords hm hmn hk C W =
      layerMarkedWordsFromField hm hmn hk C W ∘
        (fun (ω : AmbientCoord n → Prop)
          (z : layerReservedMarkBlock hm hmn hk C W) => ω z) := by
    funext ω
    exact layerMarkedWords_eq_fromField hm hmn hk C W ω
  rw [heq]
  simpa [Function.comp_apply] using hcomp

/-- Extend a finite coordinate field by `False` outside its block. -/
def ambientFromFiniteBlock {n : Nat} (S : Finset (AmbientCoord n))
    (v : S → Prop) : AmbientCoord n → Prop := fun z =>
  if h : z ∈ S then v ⟨z, h⟩ else False

theorem catalystPoolFamilyOpen_ambientFromFiniteBlock_iff
    {n : Nat} (S : Finset (AmbientCoord n))
    (ω : AmbientCoord n → Prop) (C : Finset (Molecule n))
    (R : Finset (Reaction n))
    (hblock : catalystPoolFamilyBlock C R ⊆ S) :
    catalystPoolFamilyOpen
        (ambientFromFiniteBlock S (fun z : S => ω z)) C R ↔
      catalystPoolFamilyOpen ω C R := by
  constructor
  · rintro ⟨r, hr, y, hy, hopen⟩
    have hz : (y, r) ∈ S := hblock (Finset.mem_product.mpr ⟨hy, hr⟩)
    exact ⟨r, hr, y, hy, by
      simpa [ambientFromFiniteBlock, hz] using hopen⟩
  · rintro ⟨r, hr, y, hy, hopen⟩
    have hz : (y, r) ∈ S := hblock (Finset.mem_product.mpr ⟨hy, hr⟩)
    exact ⟨r, hr, y, hy, by
      simpa [ambientFromFiniteBlock, hz] using hopen⟩

/-- Finite-block adaptive concentration.  An independently selected finite
state may choose its catalyst pool, target indices, and reaction families,
provided every queried coordinate lies in one common fresh block. -/
theorem measure_adaptive_finiteBlock_familyCount_le_sharp
    {n d K b : Nat} (lambda : ℝ) (S : Finset (AmbientCoord n))
    {α ι : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α]
    (X : (AmbientCoord n → Prop) → α) (hX : Measurable X)
    (hIndep : IndepFun X
      (fun (ω : AmbientCoord n → Prop) (z : S) => ω z)
      (ambientPiMeasure n lambda))
    (C : α → Finset (Molecule n)) (s : α → Finset ι)
    (R : α → ι → Finset (Reaction n))
    (hs : ∀ a, (s a).card ≤ K) (hb : ∀ a, b ≤ (C a).card)
    (hR : ∀ a, Pairwise fun i j => Disjoint (R a i) (R a j))
    (hcard : ∀ a i, i ∈ s a → d ≤ (R a i).card)
    (hblock : ∀ a i, i ∈ s a →
      catalystPoolFamilyBlock (C a) (R a i) ⊆ S)
    {c : ℝ} (hc : 0 < c) :
    ambientPiMeasure n lambda {ω |
      (∑ i ∈ s (X ω),
        catalystPoolFamilyIndicator (C (X ω)) (R (X ω) i) ω) ≤
      ((s (X ω)).card : ℝ) *
        (1 - (toNNReal (σ (catalysisP n lambda)) : ℝ) ^
          ((C (X ω)).card * d)) - c} ≤
      ENNReal.ofReal ((((K : Nat) : ℝ) *
        (toNNReal (σ (catalysisP n lambda)) : ℝ) ^ (b * d)) /
          c ^ 2) := by
  classical
  let Y : (AmbientCoord n → Prop) → (S → Prop) := fun ω z => ω z
  let H : α → (S → Prop) → Prop := fun a v =>
    (∑ i ∈ s a, catalystPoolFamilyIndicator (C a) (R a i)
      (ambientFromFiniteBlock S v)) ≤
    ((s a).card : ℝ) *
      (1 - (toNNReal (σ (catalysisP n lambda)) : ℝ) ^
        ((C a).card * d)) - c
  have hsec : ∀ a, ambientPiMeasure n lambda {ω | H a (Y ω)} ≤
      ENNReal.ofReal ((((K : Nat) : ℝ) *
        (toNNReal (σ (catalysisP n lambda)) : ℝ) ^ (b * d)) /
          c ^ 2) := by
    intro a
    have heq : {ω : AmbientCoord n → Prop | H a (Y ω)} =
        {ω | (∑ i ∈ s a,
          catalystPoolFamilyIndicator (C a) (R a i) ω) ≤
        ((s a).card : ℝ) *
          (1 - (toNNReal (σ (catalysisP n lambda)) : ℝ) ^
            ((C a).card * d)) - c} := by
      ext ω
      simp only [Set.mem_setOf_eq, H, Y]
      have hsum :
          (∑ i ∈ s a, catalystPoolFamilyIndicator (C a) (R a i)
            (ambientFromFiniteBlock S (fun z : S => ω z))) =
          (∑ i ∈ s a,
            catalystPoolFamilyIndicator (C a) (R a i) ω) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [catalystPoolFamilyIndicator]
        rw [catalystPoolFamilyOpen_ambientFromFiniteBlock_iff
          S ω (C a) (R a i) (hblock a i hi)]
      rw [hsum]
    rw [heq]
    have hfixed :=
      measure_sum_catalystPoolFamilyIndicator_le_card_mul_one_sub_pow_sub_sharp
        lambda (C a) (s a) (R a) (hR a) (hcard a) hc
    have hfixed' : ambientPiMeasure n lambda {ω |
        (∑ i ∈ s a,
          catalystPoolFamilyIndicator (C a) (R a i) ω) ≤
        ((s a).card : ℝ) *
          (1 - (toNNReal (σ (catalysisP n lambda)) : ℝ) ^
            ((C a).card * d)) - c} ≤
        ENNReal.ofReal ((((s a).card : ℝ) *
          (toNNReal (σ (catalysisP n lambda)) : ℝ) ^
            ((C a).card * d)) / c ^ 2) := by
      simpa only [Finset.sum_apply] using hfixed
    refine hfixed'.trans ?_
    apply ENNReal.ofReal_le_ofReal
    apply div_le_div_of_nonneg_right
    · apply mul_le_mul
      · exact_mod_cast hs a
      · apply pow_le_pow_of_le_one
        · positivity
        · simpa using (σ (catalysisP n lambda)).2.2
        · exact Nat.mul_le_mul_right d (hb a)
      · positivity
      · positivity
    · exact sq_nonneg c
  have hadaptive := measure_adaptive_of_indep_finite hIndep hX H
    (fun _ => MeasurableSet.of_discrete) hsec
  refine (measure_mono ?_).trans hadaptive
  intro ω hω
  change H (X ω) (Y ω)
  simp only [H, Y]
  have hsum :
      (∑ i ∈ s (X ω),
        catalystPoolFamilyIndicator (C (X ω)) (R (X ω) i)
          (ambientFromFiniteBlock S (fun z : S => ω z))) =
      (∑ i ∈ s (X ω),
        catalystPoolFamilyIndicator (C (X ω)) (R (X ω) i) ω) := by
    apply Finset.sum_congr rfl
    intro i hi
    simp only [catalystPoolFamilyIndicator]
    rw [catalystPoolFamilyOpen_ambientFromFiniteBlock_iff
      S ω (C (X ω)) (R (X ω) i) (hblock (X ω) i hi)]
  rw [hsum]
  simpa only [Set.mem_setOf_eq, Finset.sum_apply] using hω

/-- Event-conditioned catalyst-floor form of the finite-block mixture. -/
theorem measure_adaptive_finiteBlock_familyCount_and_poolFloor_le_sharp
    {n d K b : Nat} (lambda : ℝ) (S : Finset (AmbientCoord n))
    {α ι : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α]
    (X : (AmbientCoord n → Prop) → α) (hX : Measurable X)
    (hIndep : IndepFun X
      (fun (ω : AmbientCoord n → Prop) (z : S) => ω z)
      (ambientPiMeasure n lambda))
    (C : α → Finset (Molecule n)) (s : α → Finset ι)
    (R : α → ι → Finset (Reaction n))
    (hs : ∀ a, (s a).card ≤ K)
    (hR : ∀ a, Pairwise fun i j => Disjoint (R a i) (R a j))
    (hcard : ∀ a i, i ∈ s a → d ≤ (R a i).card)
    (hblock : ∀ a i, i ∈ s a →
      catalystPoolFamilyBlock (C a) (R a i) ⊆ S)
    {c : ℝ} (hc : 0 < c) :
    ambientPiMeasure n lambda {ω |
      b ≤ (C (X ω)).card ∧
      (∑ i ∈ s (X ω),
        catalystPoolFamilyIndicator (C (X ω)) (R (X ω) i) ω) ≤
      ((s (X ω)).card : ℝ) *
        (1 - (toNNReal (σ (catalysisP n lambda)) : ℝ) ^
          ((C (X ω)).card * d)) - c} ≤
      ENNReal.ofReal ((((K : Nat) : ℝ) *
        (toNNReal (σ (catalysisP n lambda)) : ℝ) ^ (b * d)) /
          c ^ 2) := by
  classical
  let Y : (AmbientCoord n → Prop) → (S → Prop) := fun ω z => ω z
  let H : α → (S → Prop) → Prop := fun a v =>
    b ≤ (C a).card ∧
    (∑ i ∈ s a, catalystPoolFamilyIndicator (C a) (R a i)
      (ambientFromFiniteBlock S v)) ≤
    ((s a).card : ℝ) *
      (1 - (toNNReal (σ (catalysisP n lambda)) : ℝ) ^
        ((C a).card * d)) - c
  have hsec : ∀ a, ambientPiMeasure n lambda {ω | H a (Y ω)} ≤
      ENNReal.ofReal ((((K : Nat) : ℝ) *
        (toNNReal (σ (catalysisP n lambda)) : ℝ) ^ (b * d)) /
          c ^ 2) := by
    intro a
    by_cases hfloor : b ≤ (C a).card
    · have heq : {ω : AmbientCoord n → Prop | H a (Y ω)} =
          {ω | (∑ i ∈ s a,
            catalystPoolFamilyIndicator (C a) (R a i) ω) ≤
          ((s a).card : ℝ) *
            (1 - (toNNReal (σ (catalysisP n lambda)) : ℝ) ^
              ((C a).card * d)) - c} := by
        ext ω
        simp only [Set.mem_setOf_eq, H, Y, hfloor, true_and]
        have hsum :
            (∑ i ∈ s a, catalystPoolFamilyIndicator (C a) (R a i)
              (ambientFromFiniteBlock S (fun z : S => ω z))) =
            (∑ i ∈ s a,
              catalystPoolFamilyIndicator (C a) (R a i) ω) := by
          apply Finset.sum_congr rfl
          intro i hi
          simp only [catalystPoolFamilyIndicator]
          rw [catalystPoolFamilyOpen_ambientFromFiniteBlock_iff
            S ω (C a) (R a i) (hblock a i hi)]
        rw [hsum]
      rw [heq]
      have hfixed :=
        measure_sum_catalystPoolFamilyIndicator_le_card_mul_one_sub_pow_sub_sharp
          lambda (C a) (s a) (R a) (hR a) (hcard a) hc
      have hfixed' : ambientPiMeasure n lambda {ω |
          (∑ i ∈ s a,
            catalystPoolFamilyIndicator (C a) (R a i) ω) ≤
          ((s a).card : ℝ) *
            (1 - (toNNReal (σ (catalysisP n lambda)) : ℝ) ^
              ((C a).card * d)) - c} ≤
          ENNReal.ofReal ((((s a).card : ℝ) *
            (toNNReal (σ (catalysisP n lambda)) : ℝ) ^
              ((C a).card * d)) / c ^ 2) := by
        simpa only [Finset.sum_apply] using hfixed
      refine hfixed'.trans ?_
      apply ENNReal.ofReal_le_ofReal
      apply div_le_div_of_nonneg_right
      · apply mul_le_mul
        · exact_mod_cast hs a
        · apply pow_le_pow_of_le_one
          · positivity
          · simpa using (σ (catalysisP n lambda)).2.2
          · exact Nat.mul_le_mul_right d hfloor
        · positivity
        · positivity
      · exact sq_nonneg c
    · simp [H, hfloor]
  have hadaptive := measure_adaptive_of_indep_finite hIndep hX H
    (fun _ => MeasurableSet.of_discrete) hsec
  refine (measure_mono ?_).trans hadaptive
  intro ω hω
  change H (X ω) (Y ω)
  refine ⟨hω.1, ?_⟩
  simp only [Y]
  have hsum :
      (∑ i ∈ s (X ω),
        catalystPoolFamilyIndicator (C (X ω)) (R (X ω) i)
          (ambientFromFiniteBlock S (fun z : S => ω z))) =
      (∑ i ∈ s (X ω),
        catalystPoolFamilyIndicator (C (X ω)) (R (X ω) i) ω) := by
    apply Finset.sum_congr rfl
    intro i hi
    simp only [catalystPoolFamilyIndicator]
    rw [catalystPoolFamilyOpen_ambientFromFiniteBlock_iff
      S ω (C (X ω)) (R (X ω) i) (hblock (X ω) i hi)]
  rw [hsum]
  simpa only [Finset.sum_apply] using hω.2

theorem reactionProduct_layerReactionAtSplit {n m : Nat}
    (hm : 2 ≤ m) (hmn : m ≤ n) (w : Word m) (i : Fin (m - 1)) :
    reactionProduct (layerReactionAtSplit hm hmn w i) =
      layerMolecule (by omega) hmn w := by
  rfl

/-- Mark families of distinct target words use disjoint reaction identities,
so their auxiliary mark events are pairwise independent. -/
theorem layerInitialSplitReactions_disjoint {n m k : Nat}
    (hm : 2 ≤ m) (hmn : m ≤ n) (hk : k ≤ m - 1)
    {u v : Word m} (huv : u ≠ v) :
    Disjoint (layerInitialSplitReactions hm hmn hk u)
      (layerInitialSplitReactions hm hmn hk v) := by
  classical
  rw [Finset.disjoint_left]
  intro r hru hrv
  obtain ⟨i, hi, hir⟩ := Finset.mem_image.mp hru
  obtain ⟨j, hj, hjr⟩ := Finset.mem_image.mp hrv
  have hprod := congrArg reactionProduct (hir.trans hjr.symm)
  apply huv
  apply layerMolecule_injective (by omega) hmn
  simpa [reactionProduct_layerReactionAtSplit] using hprod

/-- Exact law of one reserved mark block. -/
theorem measure_layerInitialSplitMarkOpen {n m k : Nat}
    (hm : 2 ≤ m) (hmn : m ≤ n) (hk : k ≤ m - 1)
    (lambda : ℝ) (C : Finset (Molecule n)) (w : Word m) :
    ambientPiMeasure n lambda {ω |
      catalystPoolFamilyOpen ω C
        (layerInitialSplitReactions hm hmn hk w)} =
      1 - (toNNReal (σ (catalysisP n lambda)) : ENNReal) ^
        (C.card * k) := by
  rw [measure_catalystPoolFamilyOpen_card,
    card_layerInitialSplitReactions]

/-- Reserved marks for two distinct words are independent even though they
query the same prospective catalyst pool. -/
theorem layerInitialSplitMarkOpen_indep {n m k : Nat}
    (hm : 2 ≤ m) (hmn : m ≤ n) (hk : k ≤ m - 1)
    (lambda : ℝ) (C : Finset (Molecule n)) {u v : Word m} (huv : u ≠ v) :
    IndepFun
      (fun ω => catalystPoolFamilyOpen ω C
        (layerInitialSplitReactions hm hmn hk u))
      (fun ω => catalystPoolFamilyOpen ω C
        (layerInitialSplitReactions hm hmn hk v))
      (ambientPiMeasure n lambda) := by
  exact catalystPoolFamilyOpen_indep lambda C
    (layerInitialSplitReactions_disjoint hm hmn hk huv)

/-- Sharp concentration of the reserved marks over an arbitrary word block.
The closed-mark energy `q^(|C|*k)` is retained, so a fixed sufficiently large
`k` makes the selected reservoir arbitrarily close to the full block once
`C` is macroscopic. -/
theorem measure_layerInitialSplitMarkCount_le_sharp {n m k : Nat}
    (hm : 2 ≤ m) (hmn : m ≤ n) (hk : k ≤ m - 1)
    (lambda : ℝ) (C : Finset (Molecule n)) (W : Finset (Word m))
    {c : ℝ} (hc : 0 < c) :
    ambientPiMeasure n lambda {ω |
      (∑ w ∈ W, catalystPoolFamilyIndicator C
        (layerInitialSplitReactions hm hmn hk w) ω) ≤
      (W.card : ℝ) *
        (1 - (toNNReal (σ (catalysisP n lambda)) : ℝ) ^
          (C.card * k)) - c} ≤
      ENNReal.ofReal (((W.card : ℝ) *
        (toNNReal (σ (catalysisP n lambda)) : ℝ) ^
          (C.card * k)) / c ^ 2) := by
  have hR : Pairwise fun u v =>
      Disjoint (layerInitialSplitReactions hm hmn hk u)
        (layerInitialSplitReactions hm hmn hk v) := by
    intro u v huv
    exact layerInitialSplitReactions_disjoint hm hmn hk huv
  have hcard : ∀ w ∈ W,
      k ≤ (layerInitialSplitReactions hm hmn hk w).card := by
    intro w _
    simp
  simpa using
    (measure_sum_catalystPoolFamilyIndicator_le_card_mul_one_sub_pow_sub_sharp
      lambda C W (layerInitialSplitReactions hm hmn hk) hR hcard hc)

/-- The reserved labels select an adaptive catalyst pool, while all actual
support tests use the globally disjoint unreserved field. -/
theorem measure_layerMarkedWords_goodUnreservedFamilyCount_and_poolFloor_le_sharp
    {n m k delta b : Nat} (hm : 2 ≤ m) (hmn : m ≤ n)
    (hk : k ≤ m - 1) (lambda : ℝ)
    (Cmark A B : Finset (Molecule n)) (W : Finset (Word m))
    {c : ℝ} (hc : 0 < c) :
    ambientPiMeasure n lambda {ω |
      let M := layerMarkedWords hm hmn hk Cmark W ω
      let MW := M ∩ W
      let G := MW \ splitMissingTail
        (layerSplitViableTargets hm hmn A B) delta
      b ≤ (layerWordTargets (by omega) hmn MW).card ∧
      (∑ w ∈ G, catalystPoolFamilyIndicator
        (layerWordTargets (by omega) hmn MW)
        (unreservedCrossViableReactions hm hmn hk A B w) ω) ≤
      (G.card : ℝ) *
        (1 - (toNNReal (σ (catalysisP n lambda)) : ℝ) ^
          ((layerWordTargets (by omega) hmn MW).card *
            (m - delta - k))) - c} ≤
      ENNReal.ofReal ((((W.card : Nat) : ℝ) *
        (toNNReal (σ (catalysisP n lambda)) : ℝ) ^
          (b * (m - delta - k))) / c ^ 2) := by
  classical
  let State := Finset (Word m)
  let X : (AmbientCoord n → Prop) → State :=
    layerMarkedWords hm hmn hk Cmark W
  let S : Finset (AmbientCoord n) :=
    layerUnreservedSupportBlock hm hmn hk
      (Finset.univ : Finset (Molecule n)) A B W
  let Cstate : State → Finset (Molecule n) := fun M =>
    layerWordTargets (by omega) hmn (M ∩ W)
  let sstate : State → Finset (Word m) := fun M =>
    (M ∩ W) \ splitMissingTail
      (layerSplitViableTargets hm hmn A B) delta
  let Rstate : State → Word m → Finset (Reaction n) := fun _ w =>
    unreservedCrossViableReactions hm hmn hk A B w
  have hs : ∀ M, (sstate M).card ≤ W.card := by
    intro M
    exact Finset.card_le_card
      (Finset.sdiff_subset.trans Finset.inter_subset_right)
  have hR : ∀ M, Pairwise fun u v =>
      Disjoint (Rstate M u) (Rstate M v) := by
    intro M u v huv
    rw [Finset.disjoint_left]
    intro r hru hrv
    have htargets : layerMolecule (by omega) hmn u ≠
        layerMolecule (by omega) hmn v := by
      intro huvMol
      exact huv (layerMolecule_injective (by omega) hmn huvMol)
    exact Finset.disjoint_left.mp
      (crossViableReactions_disjoint A B htargets)
      (Finset.mem_sdiff.mp hru).1 (Finset.mem_sdiff.mp hrv).1
  have hcard : ∀ M w, w ∈ sstate M →
      m - delta - k ≤ (Rstate M w).card := by
    intro M w hw
    exact card_unreservedCrossViableReactions_ge_of_not_mem_tail
      hm hmn hk A B (Finset.mem_sdiff.mp hw).2
  have hblock : ∀ M w, w ∈ sstate M →
      catalystPoolFamilyBlock (Cstate M) (Rstate M w) ⊆ S := by
    intro M w hw z hz
    have hzprod := Finset.mem_product.mp hz
    have hwW : w ∈ W :=
      Finset.inter_subset_right (Finset.sdiff_subset hw)
    show z ∈ (Finset.univ : Finset (Molecule n)).product
      (layerUnreservedCrossViableReactionUnion hm hmn hk A B W)
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _,
      Finset.mem_biUnion.mpr ⟨w, hwW, hzprod.2⟩⟩
  have hIndep : IndepFun X
      (fun (ω : AmbientCoord n → Prop) (z : S) => ω z)
      (ambientPiMeasure n lambda) := by
    simpa only [X, S] using
      (layerMarkedWords_indep_unreservedSupportField
        hm hmn hk lambda Cmark
        (Finset.univ : Finset (Molecule n)) A B W W)
  have htail :=
    measure_adaptive_finiteBlock_familyCount_and_poolFloor_le_sharp
      (n := n) (d := m - delta - k) (K := W.card) (b := b)
      lambda S X (layerMarkedWords_measurable hm hmn hk Cmark W)
      hIndep Cstate sstate Rstate hs hR hcard hblock hc
  simpa only [State, X, S, Cstate, sstate, Rstate] using htail

end HordijkSteelThreshold
