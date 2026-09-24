import proofs.HordijkSteelThreshold.AdaptiveTargetBlockConcentration
import proofs.HordijkSteelThreshold.LayerSplitProfile

namespace HordijkSteelThreshold

open MeasureTheory ProbabilityTheory unitInterval
open RAF RAF.Polymer RAF.Concrete

/-- Fresh-layer concentration with fully adaptive factor and catalyst pools.
The state `f` may inspect every catalysis coordinate whose reaction product is
outside the exact length-`m` layer.  It then selects the factor pools, the good
targets, their viable reaction families, and the opposite catalyst pool.  The
length-`m` target block is still fresh, so the supported-good-target count has
the fixed-state Chebyshev lower tail without an entropy factor. -/
theorem measure_complementAdaptive_layerGoodFamilyCount_le
    {n m delta : Nat} (hm : 2 ≤ m) (hmn : m ≤ n) (lambda : ℝ)
    (f : (catalystPoolTargetBlock
      (Finset.univ : Finset (Molecule n))
        ((Finset.univ : Finset (Molecule n)) \
          layerMolecules (by omega) hmn) → Prop) →
        (Finset (Molecule n) × Finset (Molecule n)))
    {c : ℝ} (hc : 0 < c) :
    ambientPiMeasure n lambda {ω |
      let S := f (fun z : catalystPoolTargetBlock
        (Finset.univ : Finset (Molecule n))
          ((Finset.univ : Finset (Molecule n)) \
            layerMolecules (by omega) hmn) => ω z)
      (∑ x ∈ layerGoodMolecules hm hmn S.1 S.2 delta,
        catalystPoolFamilyIndicator S.2
          (crossViableReactions S.1 S.2 x) ω) ≤
      ((layerGoodMolecules hm hmn S.1 S.2 delta).card : ℝ) *
        (1 - (toNNReal (σ (catalysisP n lambda)) : ℝ) ^
          (S.2.card * (m - delta))) - c} ≤
      ENNReal.ofReal ((((2 ^ m : Nat) : ℝ) / 4) / c ^ 2) := by
  classical
  let State := Finset (Molecule n) × Finset (Molecule n)
  letI : MeasurableSpace State := ⊤
  let T : Finset (Molecule n) := layerMolecules (by omega) hmn
  let C : State → Finset (Molecule n) := fun S => S.2
  let s : State → Finset (Molecule n) := fun S =>
    layerGoodMolecules hm hmn S.1 S.2 delta
  let R : State → Molecule n → Finset (Reaction n) := fun S x =>
    crossViableReactions S.1 S.2 x
  have hs : ∀ S, (s S).card ≤ 2 ^ m := by
    intro S
    rw [← card_layerMolecules (by omega) hmn]
    exact Finset.card_le_card
      (layerGoodMolecules_subset_layerMolecules hm hmn S.1 S.2)
  have hR : ∀ S, Pairwise fun x y => Disjoint (R S x) (R S y) := by
    intro S x y hxy
    exact crossViableReactions_disjoint S.1 S.2 hxy
  have hcard : ∀ S x, x ∈ s S →
      m - delta ≤ (R S x).card := by
    intro S x hx
    change x ∈ layerGoodMolecules hm hmn S.1 S.2 delta at hx
    rw [layerGoodMolecules] at hx
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hx
    have hwtail : w ∉ splitMissingTail
        (layerSplitViableTargets hm hmn S.1 S.2) delta :=
      (Finset.mem_sdiff.mp hw).2
    exact layer_crossViableReactions_card_ge_of_not_mem_tail
      hm hmn S.1 S.2 hwtail
  have hprod : ∀ S x, x ∈ s S → ∀ r ∈ R S x,
      reactionProduct r ∈ T := by
    intro S x hx r hr
    change x ∈ layerGoodMolecules hm hmn S.1 S.2 delta at hx
    have hxT : x ∈ T := by
      exact layerGoodMolecules_subset_layerMolecules hm hmn S.1 S.2 hx
    have hrx : reactionProduct r = x :=
      (mem_crossViableReactions S.1 S.2 x r).mp hr |>.1
    simpa [hrx] using hxT
  have htail := measure_complementAdaptive_targetBlock_familyCount_le
    (n := n) (d := m - delta) (K := 2 ^ m) lambda T f
    (measurable_of_finite _) C s R hs hR hcard hprod hc
  simpa only [T, C, s, R, State] using htail

/-- Word-block form of the fresh-layer bootstrap.  Since `W` is arbitrary,
this single estimate applies to prefix cylinders, suffix cylinders, and their
pairwise intersections.  Those are precisely the first and second moments in
the split-incidence discrepancy expansion. -/
theorem measure_complementAdaptive_layerWordGoodFamilyCount_le
    {n m delta : Nat} (hm : 2 ≤ m) (hmn : m ≤ n) (lambda : ℝ)
    (W : Finset (Word m))
    (f : (catalystPoolTargetBlock
      (Finset.univ : Finset (Molecule n))
        ((Finset.univ : Finset (Molecule n)) \
          layerMolecules (by omega) hmn) → Prop) →
        (Finset (Molecule n) × Finset (Molecule n)))
    {c : ℝ} (hc : 0 < c) :
    ambientPiMeasure n lambda {ω |
      let S := f (fun z : catalystPoolTargetBlock
        (Finset.univ : Finset (Molecule n))
          ((Finset.univ : Finset (Molecule n)) \
            layerMolecules (by omega) hmn) => ω z)
      let G := layerWordTargets (by omega) hmn W ∩
        layerGoodMolecules hm hmn S.1 S.2 delta
      (∑ x ∈ G, catalystPoolFamilyIndicator S.2
        (crossViableReactions S.1 S.2 x) ω) ≤
      (G.card : ℝ) *
        (1 - (toNNReal (σ (catalysisP n lambda)) : ℝ) ^
          (S.2.card * (m - delta))) - c} ≤
      ENNReal.ofReal ((((W.card : Nat) : ℝ) / 4) / c ^ 2) := by
  classical
  let State := Finset (Molecule n) × Finset (Molecule n)
  letI : MeasurableSpace State := ⊤
  let T : Finset (Molecule n) := layerMolecules (by omega) hmn
  let C : State → Finset (Molecule n) := fun S => S.2
  let s : State → Finset (Molecule n) := fun S =>
    layerWordTargets (by omega) hmn W ∩
      layerGoodMolecules hm hmn S.1 S.2 delta
  let R : State → Molecule n → Finset (Reaction n) := fun S x =>
    crossViableReactions S.1 S.2 x
  have hs : ∀ S, (s S).card ≤ W.card := by
    intro S
    calc
      (s S).card ≤ (layerWordTargets (by omega) hmn W).card := by
        exact Finset.card_le_card (Finset.inter_subset_left)
      _ = W.card := card_layerWordTargets (by omega) hmn W
  have hR : ∀ S, Pairwise fun x y => Disjoint (R S x) (R S y) := by
    intro S x y hxy
    exact crossViableReactions_disjoint S.1 S.2 hxy
  have hcard : ∀ S x, x ∈ s S →
      m - delta ≤ (R S x).card := by
    intro S x hx
    change x ∈ layerWordTargets (by omega) hmn W ∩
      layerGoodMolecules hm hmn S.1 S.2 delta at hx
    have hxgood := (Finset.mem_inter.mp hx).2
    rw [layerGoodMolecules] at hxgood
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hxgood
    have hwtail : w ∉ splitMissingTail
        (layerSplitViableTargets hm hmn S.1 S.2) delta :=
      (Finset.mem_sdiff.mp hw).2
    exact layer_crossViableReactions_card_ge_of_not_mem_tail
      hm hmn S.1 S.2 hwtail
  have hprod : ∀ S x, x ∈ s S → ∀ r ∈ R S x,
      reactionProduct r ∈ T := by
    intro S x hx r hr
    change x ∈ layerWordTargets (by omega) hmn W ∩
      layerGoodMolecules hm hmn S.1 S.2 delta at hx
    have hxT : x ∈ T :=
      layerGoodMolecules_subset_layerMolecules hm hmn S.1 S.2
        (Finset.mem_inter.mp hx).2
    have hrx : reactionProduct r = x :=
      (mem_crossViableReactions S.1 S.2 x r).mp hr |>.1
    simpa [hrx] using hxT
  have htail := measure_complementAdaptive_targetBlock_familyCount_le
    (n := n) (d := m - delta) (K := W.card) lambda T f
    (measurable_of_finite _) C s R hs hR hcard hprod hc
  simpa only [T, C, s, R, State] using htail

/-- Adaptive word-block form.  The complementary state may itself choose the
word block whose supported targets are counted.  Consequently a cylinder or
overlap set built from previously exposed factor languages incurs no union
over its possible values; only its uniform cardinality cap `K` appears. -/
theorem measure_complementAdaptive_layerAdaptiveWordGoodFamilyCount_le
    {n m delta K : Nat} (hm : 2 ≤ m) (hmn : m ≤ n) (lambda : ℝ)
    (f : (catalystPoolTargetBlock
      (Finset.univ : Finset (Molecule n))
        ((Finset.univ : Finset (Molecule n)) \
          layerMolecules (by omega) hmn) → Prop) →
        (Finset (Molecule n) × Finset (Molecule n)))
    (W : (Finset (Molecule n) × Finset (Molecule n)) →
      Finset (Word m))
    (hW : ∀ S, (W S).card ≤ K)
    {c : ℝ} (hc : 0 < c) :
    ambientPiMeasure n lambda {ω |
      let S := f (fun z : catalystPoolTargetBlock
        (Finset.univ : Finset (Molecule n))
          ((Finset.univ : Finset (Molecule n)) \
            layerMolecules (by omega) hmn) => ω z)
      let G := layerWordTargets (by omega) hmn (W S) ∩
        layerGoodMolecules hm hmn S.1 S.2 delta
      (∑ x ∈ G, catalystPoolFamilyIndicator S.2
        (crossViableReactions S.1 S.2 x) ω) ≤
      (G.card : ℝ) *
        (1 - (toNNReal (σ (catalysisP n lambda)) : ℝ) ^
          (S.2.card * (m - delta))) - c} ≤
      ENNReal.ofReal ((((K : Nat) : ℝ) / 4) / c ^ 2) := by
  classical
  let State := Finset (Molecule n) × Finset (Molecule n)
  letI : MeasurableSpace State := ⊤
  let T : Finset (Molecule n) := layerMolecules (by omega) hmn
  let C : State → Finset (Molecule n) := fun S => S.2
  let s : State → Finset (Molecule n) := fun S =>
    layerWordTargets (by omega) hmn (W S) ∩
      layerGoodMolecules hm hmn S.1 S.2 delta
  let R : State → Molecule n → Finset (Reaction n) := fun S x =>
    crossViableReactions S.1 S.2 x
  have hs : ∀ S, (s S).card ≤ K := by
    intro S
    calc
      (s S).card ≤ (layerWordTargets (by omega) hmn (W S)).card := by
        exact Finset.card_le_card (Finset.inter_subset_left)
      _ = (W S).card := card_layerWordTargets (by omega) hmn (W S)
      _ ≤ K := hW S
  have hR : ∀ S, Pairwise fun x y => Disjoint (R S x) (R S y) := by
    intro S x y hxy
    exact crossViableReactions_disjoint S.1 S.2 hxy
  have hcard : ∀ S x, x ∈ s S →
      m - delta ≤ (R S x).card := by
    intro S x hx
    change x ∈ layerWordTargets (by omega) hmn (W S) ∩
      layerGoodMolecules hm hmn S.1 S.2 delta at hx
    have hxgood := (Finset.mem_inter.mp hx).2
    rw [layerGoodMolecules] at hxgood
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hxgood
    have hwtail : w ∉ splitMissingTail
        (layerSplitViableTargets hm hmn S.1 S.2) delta :=
      (Finset.mem_sdiff.mp hw).2
    exact layer_crossViableReactions_card_ge_of_not_mem_tail
      hm hmn S.1 S.2 hwtail
  have hprod : ∀ S x, x ∈ s S → ∀ r ∈ R S x,
      reactionProduct r ∈ T := by
    intro S x hx r hr
    change x ∈ layerWordTargets (by omega) hmn (W S) ∩
      layerGoodMolecules hm hmn S.1 S.2 delta at hx
    have hxT : x ∈ T :=
      layerGoodMolecules_subset_layerMolecules hm hmn S.1 S.2
        (Finset.mem_inter.mp hx).2
    have hrx : reactionProduct r = x :=
      (mem_crossViableReactions S.1 S.2 x r).mp hr |>.1
    simpa [hrx] using hxT
  have htail := measure_complementAdaptive_targetBlock_familyCount_le
    (n := n) (d := m - delta) (K := K) lambda T f
    (measurable_of_finite _) C s R hs hR hcard hprod hc
  simpa only [T, C, s, R, State] using htail

/-- Sharp adaptive word-block bootstrap.  When the complementary state carries
a catalyst pool of size at least `b`, the block failure cost retains the
closed-family factor `q^(b*(m-delta))`. -/
theorem measure_complementAdaptive_layerAdaptiveWordGoodFamilyCount_le_sharp
    {n m delta K b : Nat} (hm : 2 ≤ m) (hmn : m ≤ n) (lambda : ℝ)
    (f : (catalystPoolTargetBlock
      (Finset.univ : Finset (Molecule n))
        ((Finset.univ : Finset (Molecule n)) \
          layerMolecules (by omega) hmn) → Prop) →
        (Finset (Molecule n) × Finset (Molecule n)))
    (W : (Finset (Molecule n) × Finset (Molecule n)) →
      Finset (Word m))
    (hW : ∀ S, (W S).card ≤ K)
    (hb : ∀ S : Finset (Molecule n) × Finset (Molecule n),
      b ≤ S.2.card)
    {c : ℝ} (hc : 0 < c) :
    ambientPiMeasure n lambda {ω |
      let S := f (fun z : catalystPoolTargetBlock
        (Finset.univ : Finset (Molecule n))
          ((Finset.univ : Finset (Molecule n)) \
            layerMolecules (by omega) hmn) => ω z)
      let G := layerWordTargets (by omega) hmn (W S) ∩
        layerGoodMolecules hm hmn S.1 S.2 delta
      (∑ x ∈ G, catalystPoolFamilyIndicator S.2
        (crossViableReactions S.1 S.2 x) ω) ≤
      (G.card : ℝ) *
        (1 - (toNNReal (σ (catalysisP n lambda)) : ℝ) ^
          (S.2.card * (m - delta))) - c} ≤
      ENNReal.ofReal ((((K : Nat) : ℝ) *
        (toNNReal (σ (catalysisP n lambda)) : ℝ) ^
          (b * (m - delta))) / c ^ 2) := by
  classical
  let State := Finset (Molecule n) × Finset (Molecule n)
  letI : MeasurableSpace State := ⊤
  let T : Finset (Molecule n) := layerMolecules (by omega) hmn
  let C : State → Finset (Molecule n) := fun S => S.2
  let s : State → Finset (Molecule n) := fun S =>
    layerWordTargets (by omega) hmn (W S) ∩
      layerGoodMolecules hm hmn S.1 S.2 delta
  let R : State → Molecule n → Finset (Reaction n) := fun S x =>
    crossViableReactions S.1 S.2 x
  have hs : ∀ S, (s S).card ≤ K := by
    intro S
    calc
      (s S).card ≤ (layerWordTargets (by omega) hmn (W S)).card := by
        exact Finset.card_le_card (Finset.inter_subset_left)
      _ = (W S).card := card_layerWordTargets (by omega) hmn (W S)
      _ ≤ K := hW S
  have hR : ∀ S, Pairwise fun x y => Disjoint (R S x) (R S y) := by
    intro S x y hxy
    exact crossViableReactions_disjoint S.1 S.2 hxy
  have hcard : ∀ S x, x ∈ s S →
      m - delta ≤ (R S x).card := by
    intro S x hx
    change x ∈ layerWordTargets (by omega) hmn (W S) ∩
      layerGoodMolecules hm hmn S.1 S.2 delta at hx
    have hxgood := (Finset.mem_inter.mp hx).2
    rw [layerGoodMolecules] at hxgood
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hxgood
    have hwtail : w ∉ splitMissingTail
        (layerSplitViableTargets hm hmn S.1 S.2) delta :=
      (Finset.mem_sdiff.mp hw).2
    exact layer_crossViableReactions_card_ge_of_not_mem_tail
      hm hmn S.1 S.2 hwtail
  have hprod : ∀ S x, x ∈ s S → ∀ r ∈ R S x,
      reactionProduct r ∈ T := by
    intro S x hx r hr
    change x ∈ layerWordTargets (by omega) hmn (W S) ∩
      layerGoodMolecules hm hmn S.1 S.2 delta at hx
    have hxT : x ∈ T :=
      layerGoodMolecules_subset_layerMolecules hm hmn S.1 S.2
        (Finset.mem_inter.mp hx).2
    have hrx : reactionProduct r = x :=
      (mem_crossViableReactions S.1 S.2 x r).mp hr |>.1
    simpa [hrx] using hxT
  have htail := measure_complementAdaptive_targetBlock_familyCount_le_sharp
    (n := n) (d := m - delta) (K := K) (b := b) lambda T f
    (measurable_of_finite _) C s R hs hb hR hcard hprod hc
  simpa only [T, C, s, R, State] using htail

/-- Event-conditioned sharp fresh-layer bootstrap.  Unlike the preceding
uniform-floor form, this theorem permits arbitrary complementary states and
charges only failures occurring when the selected catalyst pool actually has
size at least `b`.  It is therefore suitable for a one-pass staged profile. -/
theorem measure_complementAdaptive_layerAdaptiveWordGoodFamilyCount_and_poolFloor_le_sharp
    {n m delta K b : Nat} (hm : 2 ≤ m) (hmn : m ≤ n) (lambda : ℝ)
    (f : (catalystPoolTargetBlock
      (Finset.univ : Finset (Molecule n))
        ((Finset.univ : Finset (Molecule n)) \
          layerMolecules (by omega) hmn) → Prop) →
        (Finset (Molecule n) × Finset (Molecule n)))
    (W : (Finset (Molecule n) × Finset (Molecule n)) →
      Finset (Word m))
    (hW : ∀ S, (W S).card ≤ K)
    {c : ℝ} (hc : 0 < c) :
    ambientPiMeasure n lambda {ω |
      let S := f (fun z : catalystPoolTargetBlock
        (Finset.univ : Finset (Molecule n))
          ((Finset.univ : Finset (Molecule n)) \
            layerMolecules (by omega) hmn) => ω z)
      let G := layerWordTargets (by omega) hmn (W S) ∩
        layerGoodMolecules hm hmn S.1 S.2 delta
      b ≤ S.2.card ∧
      (∑ x ∈ G, catalystPoolFamilyIndicator S.2
        (crossViableReactions S.1 S.2 x) ω) ≤
      (G.card : ℝ) *
        (1 - (toNNReal (σ (catalysisP n lambda)) : ℝ) ^
          (S.2.card * (m - delta))) - c} ≤
      ENNReal.ofReal ((((K : Nat) : ℝ) *
        (toNNReal (σ (catalysisP n lambda)) : ℝ) ^
          (b * (m - delta))) / c ^ 2) := by
  classical
  let State := Finset (Molecule n) × Finset (Molecule n)
  letI : MeasurableSpace State := ⊤
  let T : Finset (Molecule n) := layerMolecules (by omega) hmn
  let C : State → Finset (Molecule n) := fun S => S.2
  let s : State → Finset (Molecule n) := fun S =>
    layerWordTargets (by omega) hmn (W S) ∩
      layerGoodMolecules hm hmn S.1 S.2 delta
  let R : State → Molecule n → Finset (Reaction n) := fun S x =>
    crossViableReactions S.1 S.2 x
  have hs : ∀ S, (s S).card ≤ K := by
    intro S
    calc
      (s S).card ≤ (layerWordTargets (by omega) hmn (W S)).card := by
        exact Finset.card_le_card Finset.inter_subset_left
      _ = (W S).card := card_layerWordTargets (by omega) hmn (W S)
      _ ≤ K := hW S
  have hR : ∀ S, Pairwise fun x y => Disjoint (R S x) (R S y) := by
    intro S x y hxy
    exact crossViableReactions_disjoint S.1 S.2 hxy
  have hcard : ∀ S x, x ∈ s S → m - delta ≤ (R S x).card := by
    intro S x hx
    change x ∈ layerWordTargets (by omega) hmn (W S) ∩
      layerGoodMolecules hm hmn S.1 S.2 delta at hx
    have hxgood := (Finset.mem_inter.mp hx).2
    rw [layerGoodMolecules] at hxgood
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hxgood
    exact layer_crossViableReactions_card_ge_of_not_mem_tail hm hmn S.1 S.2
      (Finset.mem_sdiff.mp hw).2
  have hprod : ∀ S x, x ∈ s S → ∀ r ∈ R S x,
      reactionProduct r ∈ T := by
    intro S x hx r hr
    change x ∈ layerWordTargets (by omega) hmn (W S) ∩
      layerGoodMolecules hm hmn S.1 S.2 delta at hx
    have hxT : x ∈ T :=
      layerGoodMolecules_subset_layerMolecules hm hmn S.1 S.2
        (Finset.mem_inter.mp hx).2
    have hrx : reactionProduct r = x :=
      (mem_crossViableReactions S.1 S.2 x r).mp hr |>.1
    simpa [hrx] using hxT
  have htail :=
    measure_complementAdaptive_targetBlock_familyCount_and_poolFloor_le_sharp
      (n := n) (d := m - delta) (K := K) (b := b) lambda T f
      (measurable_of_finite _) C s R hs hR hcard hprod hc
  simpa only [T, C, s, R, State] using htail

end HordijkSteelThreshold
