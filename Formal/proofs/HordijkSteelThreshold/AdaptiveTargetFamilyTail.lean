import proofs.HordijkSteelThreshold.TargetBlockCavityIndependence
import proofs.HordijkSteelThreshold.TargetFamilyVariance
import proofs.HordijkSteelThreshold.LayerSplitProduct

namespace HordijkSteelThreshold

open MeasureTheory ProbabilityTheory unitInterval
open RAF RAF.Polymer RAF.Concrete

/-- Targets in a held-out layer which retain at least `d` factor-viable
reactions in a fixed closed-cavity pruning state. -/
noncomputable def closedTargetGoodTargets {n d : Nat}
    (T : Finset (Molecule n))
    (S : Finset (Molecule n) × Finset (Molecule n)) :
    Finset (Molecule n) := by
  classical
  exact T.filter fun x => d ≤ (crossViableReactions S.1 S.2 x).card

@[simp] theorem mem_closedTargetGoodTargets {n d : Nat}
    (T : Finset (Molecule n))
    (S : Finset (Molecule n) × Finset (Molecule n)) (x : Molecule n) :
    x ∈ closedTargetGoodTargets (d := d) T S ↔
      x ∈ T ∧ d ≤ (crossViableReactions S.1 S.2 x).card := by
  classical
  simp [closedTargetGoodTargets]

/-- Reconstructing a held-out target restriction preserves every coordinate
whose reaction product lies in that target set. -/
theorem catalysisFromTargetRestriction_eq_on_target {n : Nat}
    (T : Finset (Molecule n)) (ω : AmbientCoord n → Prop)
    (y : Molecule n) (r : Reaction n) (hr : reactionProduct r ∈ T) :
    catalysisFromTargetRestriction T
        (fun z : catalystPoolTargetBlock
          (Finset.univ : Finset (Molecule n)) T => ω z) y r ↔
      ω (y, r) := by
  simp [catalysisFromTargetRestriction, hr]

/-- A family all of whose reactions produce a held-out target has the same
open indicator before and after reconstruction from the target restriction. -/
theorem catalystPoolFamilyIndicator_fromTargetRestriction_eq {n : Nat}
    (T C : Finset (Molecule n)) (ω : AmbientCoord n → Prop)
    (x : Molecule n) (hx : x ∈ T) (R : Finset (Reaction n))
    (hprod : ∀ r ∈ R, reactionProduct r = x) :
    catalystPoolFamilyIndicator C R
        (fun z => catalysisFromTargetRestriction T
          (fun q : catalystPoolTargetBlock
            (Finset.univ : Finset (Molecule n)) T => ω q) z.1 z.2) =
      catalystPoolFamilyIndicator C R ω := by
  have hopen :
      catalystPoolFamilyOpen
          (fun z => catalysisFromTargetRestriction T
            (fun q : catalystPoolTargetBlock
              (Finset.univ : Finset (Molecule n)) T => ω q) z.1 z.2) C R ↔
        catalystPoolFamilyOpen ω C R := by
    constructor
    · rintro ⟨r, hrR, y, hyC, hcat⟩
      refine ⟨r, hrR, y, hyC, ?_⟩
      exact (catalysisFromTargetRestriction_eq_on_target
        T ω y r (hprod r hrR ▸ hx)).mp hcat
    · rintro ⟨r, hrR, y, hyC, hω⟩
      refine ⟨r, hrR, y, hyC, ?_⟩
      exact (catalysisFromTargetRestriction_eq_on_target
        T ω y r (hprod r hrR ▸ hx)).mpr hω
  unfold catalystPoolFamilyIndicator
  have hopen' : catalystPoolFamilyOpen
      (fun z => reactionProduct z.2 ∈ T ∧ ω z) C R ↔
        catalystPoolFamilyOpen ω C R := by
    simpa [catalysisFromTargetRestriction] using hopen
  by_cases hleft : catalystPoolFamilyOpen
      (fun z => reactionProduct z.2 ∈ T ∧ ω z) C R
  · have hright := hopen'.mp hleft
    simp [hleft, hright]
  · have hright : ¬catalystPoolFamilyOpen ω C R := fun h =>
      hleft (hopen'.mpr h)
    simp [hleft, hright]

/-- State-dependent supported-good-target count evaluated from the fresh
held-out target coordinates. -/
noncomputable def closedTargetGoodFamilyCount {n d : Nat}
    (T : Finset (Molecule n))
    (S : Finset (Molecule n) × Finset (Molecule n))
    (v : catalystPoolTargetBlock
      (Finset.univ : Finset (Molecule n)) T → Prop) : ℝ := by
  classical
  exact ∑ x ∈ closedTargetGoodTargets (d := d) T S,
    catalystPoolFamilyIndicator S.2 (crossViableReactions S.1 S.2 x)
      (fun z => catalysisFromTargetRestriction T v z.1 z.2)

/-- On an actual ambient sample, the reconstructed count is exactly the
ordinary supported-family count over the adaptive good-target subset. -/
theorem closedTargetGoodFamilyCount_restriction_eq {n d : Nat}
    (T : Finset (Molecule n))
    (S : Finset (Molecule n) × Finset (Molecule n))
    (ω : AmbientCoord n → Prop) :
    closedTargetGoodFamilyCount (d := d) T S (fun z => ω z) =
      ∑ x ∈ closedTargetGoodTargets (d := d) T S,
        catalystPoolFamilyIndicator S.2
          (crossViableReactions S.1 S.2 x) ω := by
  classical
  unfold closedTargetGoodFamilyCount
  apply Finset.sum_congr rfl
  intro x hx
  apply catalystPoolFamilyIndicator_fromTargetRestriction_eq T S.2 ω x
  · exact (mem_closedTargetGoodTargets T S x).mp hx |>.1
  · intro r hr
    exact (mem_crossViableReactions S.1 S.2 x r).mp hr |>.1

/-- The adaptive good-target count inherits the fixed-state Chebyshev tail
without a union bound over closed-cavity pruning states.  The state-dependent
variance cost is dominated by the cardinality of the fixed held-out shell. -/
theorem measure_adaptive_closedTargetGoodFamilyCount_le {n foodLength k d : Nat}
    (lambda : ℝ) (T : Finset (Molecule n))
    (P : Finset (Molecule n) × Finset (Molecule n))
    {c : ℝ} (hc : 0 < c) :
    ambientPiMeasure n lambda {ω |
      let S := crossPoolIter foodLength
        (closeTargetBlocks (fun y r => ω (y, r)) T) P k
      closedTargetGoodFamilyCount (d := d) T S (fun z => ω z) ≤
        ((closedTargetGoodTargets (d := d) T S).card : ℝ) *
          (1 - (toNNReal (σ (catalysisP n lambda)) : ℝ) ^
            (S.2.card * d)) - c} ≤
      ENNReal.ofReal (((T.card : ℝ) / 4) / c ^ 2) := by
  classical
  let H : (Finset (Molecule n) × Finset (Molecule n)) →
      (catalystPoolTargetBlock
        (Finset.univ : Finset (Molecule n)) T → Prop) → Prop :=
    fun S v =>
      closedTargetGoodFamilyCount (d := d) T S v ≤
        ((closedTargetGoodTargets (d := d) T S).card : ℝ) *
          (1 - (toNNReal (σ (catalysisP n lambda)) : ℝ) ^
            (S.2.card * d)) - c
  have hsec : ∀ S,
      ambientPiMeasure n lambda {ω | H S (fun z => ω z)} ≤
        ENNReal.ofReal (((T.card : ℝ) / 4) / c ^ 2) := by
    intro S
    let G := closedTargetGoodTargets (d := d) T S
    have hR : Pairwise fun x y =>
        Disjoint (crossViableReactions S.1 S.2 x)
          (crossViableReactions S.1 S.2 y) := by
      intro x y hxy
      exact crossViableReactions_disjoint S.1 S.2 hxy
    have hcard : ∀ x ∈ G,
        d ≤ (crossViableReactions S.1 S.2 x).card := by
      intro x hx
      exact (mem_closedTargetGoodTargets T S x).mp hx |>.2
    have htail :=
      measure_sum_catalystPoolFamilyIndicator_le_card_mul_one_sub_pow_sub
        lambda S.2 G (fun x => crossViableReactions S.1 S.2 x)
        hR hcard hc
    have hevent : {ω | H S (fun z => ω z)} =
        {ω | (∑ x ∈ G, catalystPoolFamilyIndicator S.2
          (crossViableReactions S.1 S.2 x) ω) ≤
            (G.card : ℝ) *
              (1 - (toNNReal (σ (catalysisP n lambda)) : ℝ) ^
                (S.2.card * d)) - c} := by
      ext ω
      simp only [Set.mem_setOf_eq]
      rw [show G = closedTargetGoodTargets (d := d) T S by rfl]
      simp only [H]
      rw [closedTargetGoodFamilyCount_restriction_eq (d := d) T S ω]
    rw [hevent]
    have htail' : ambientPiMeasure n lambda
        {ω | (∑ x ∈ G, catalystPoolFamilyIndicator S.2
          (crossViableReactions S.1 S.2 x) ω) ≤
            (G.card : ℝ) *
              (1 - (toNNReal (σ (catalysisP n lambda)) : ℝ) ^
                (S.2.card * d)) - c} ≤
          ENNReal.ofReal (((G.card : ℝ) / 4) / c ^ 2) := by
      simpa only [Finset.sum_apply] using htail
    refine htail'.trans ?_
    apply ENNReal.ofReal_le_ofReal
    apply div_le_div_of_nonneg_right
    · apply div_le_div_of_nonneg_right
      · have hGT : G ⊆ T := by
          intro x hx
          exact (mem_closedTargetGoodTargets T S x).mp hx |>.1
        exact_mod_cast Finset.card_le_card hGT
      · norm_num
    · positivity
  exact measure_adaptive_closedTargetIter_le lambda T P H
    (fun _ => (Set.toFinite _).measurableSet) hsec

/-- The sharp adaptive lower tail, restricted to closed-cavity states whose
right catalyst pool has the prescribed floor.  This event-conditioned form is
the usable bootstrap interface: no impossible uniform lower bound over every
possible cavity state is assumed. -/
theorem measure_adaptive_closedTargetGoodFamilyCount_and_poolFloor_le_sharp
    {n foodLength k d b : Nat}
    (lambda : ℝ) (T : Finset (Molecule n))
    (P : Finset (Molecule n) × Finset (Molecule n))
    {c : ℝ} (hc : 0 < c) :
    ambientPiMeasure n lambda {ω |
      let S := crossPoolIter foodLength
        (closeTargetBlocks (fun y r => ω (y, r)) T) P k
      b ≤ S.2.card ∧
      closedTargetGoodFamilyCount (d := d) T S (fun z => ω z) ≤
        ((closedTargetGoodTargets (d := d) T S).card : ℝ) *
          (1 - (toNNReal (σ (catalysisP n lambda)) : ℝ) ^
            (S.2.card * d)) - c} ≤
      ENNReal.ofReal (((T.card : ℝ) *
        (toNNReal (σ (catalysisP n lambda)) : ℝ) ^ (b * d)) /
          c ^ 2) := by
  classical
  let H : (Finset (Molecule n) × Finset (Molecule n)) →
      (catalystPoolTargetBlock
        (Finset.univ : Finset (Molecule n)) T → Prop) → Prop :=
    fun S v =>
      b ≤ S.2.card ∧
      closedTargetGoodFamilyCount (d := d) T S v ≤
        ((closedTargetGoodTargets (d := d) T S).card : ℝ) *
          (1 - (toNNReal (σ (catalysisP n lambda)) : ℝ) ^
            (S.2.card * d)) - c
  have hsec : ∀ S,
      ambientPiMeasure n lambda {ω | H S (fun z => ω z)} ≤
        ENNReal.ofReal (((T.card : ℝ) *
          (toNNReal (σ (catalysisP n lambda)) : ℝ) ^ (b * d)) /
            c ^ 2) := by
    intro S
    by_cases hb : b ≤ S.2.card
    · let G := closedTargetGoodTargets (d := d) T S
      have hR : Pairwise fun x y =>
          Disjoint (crossViableReactions S.1 S.2 x)
            (crossViableReactions S.1 S.2 y) := by
        intro x y hxy
        exact crossViableReactions_disjoint S.1 S.2 hxy
      have hcard : ∀ x ∈ G,
          d ≤ (crossViableReactions S.1 S.2 x).card := by
        intro x hx
        exact (mem_closedTargetGoodTargets T S x).mp hx |>.2
      have htail :=
        measure_sum_catalystPoolFamilyIndicator_le_card_mul_one_sub_pow_sub_sharp
          lambda S.2 G (fun x => crossViableReactions S.1 S.2 x)
          hR hcard hc
      have hevent : {ω | H S (fun z => ω z)} =
          {ω | (∑ x ∈ G, catalystPoolFamilyIndicator S.2
            (crossViableReactions S.1 S.2 x) ω) ≤
              (G.card : ℝ) *
                (1 - (toNNReal (σ (catalysisP n lambda)) : ℝ) ^
                  (S.2.card * d)) - c} := by
        ext ω
        simp only [Set.mem_setOf_eq, H, hb, true_and]
        rw [show G = closedTargetGoodTargets (d := d) T S by rfl]
        rw [closedTargetGoodFamilyCount_restriction_eq (d := d) T S ω]
      rw [hevent]
      have htail' : ambientPiMeasure n lambda
          {ω | (∑ x ∈ G, catalystPoolFamilyIndicator S.2
            (crossViableReactions S.1 S.2 x) ω) ≤
              (G.card : ℝ) *
                (1 - (toNNReal (σ (catalysisP n lambda)) : ℝ) ^
                  (S.2.card * d)) - c} ≤
            ENNReal.ofReal (((G.card : ℝ) *
              (toNNReal (σ (catalysisP n lambda)) : ℝ) ^
                (S.2.card * d)) / c ^ 2) := by
        simpa only [Finset.sum_apply] using htail
      refine htail'.trans ?_
      apply ENNReal.ofReal_le_ofReal
      apply div_le_div_of_nonneg_right
      · apply mul_le_mul
        · have hGT : G ⊆ T := by
            intro x hx
            exact (mem_closedTargetGoodTargets T S x).mp hx |>.1
          exact_mod_cast Finset.card_le_card hGT
        · apply pow_le_pow_of_le_one
          · positivity
          · simpa using (σ (catalysisP n lambda)).2.2
          · exact Nat.mul_le_mul_right d hb
        · positivity
        · positivity
      · exact sq_nonneg c
    · simp [H, hb]
  exact measure_adaptive_closedTargetIter_le lambda T P H
    (fun _ => (Set.toFinite _).measurableSet) hsec

/-- Deterministic cavity docking.  A target initially assigned to the left
pool survives every ordinary pruning round whenever a single viable reaction
for it has both factors and a right-pool catalyst surviving to the matching
closed-target cavity depth.  The proof propagates the terminal witness
backward through the nested cavity states and then forward through ordinary
pruning. -/
theorem mem_crossPoolIter_left_of_closedTarget_familyOpen
    {n foodLength k : Nat} (Cat : Catalysis (Molecule n) (Reaction n))
    (T : Finset (Molecule n))
    (P : Finset (Molecule n) × Finset (Molecule n))
    {x : Molecule n} (hxP : x ∈ P.1)
    (hopen :
      let S := crossPoolIter foodLength (closeTargetBlocks Cat T) P k
      catalystPoolFamilyOpen (fun z => Cat z.1 z.2) S.2
        (crossViableReactions S.1 S.2 x)) :
    x ∈ (crossPoolIter foodLength Cat P k).1 := by
  classical
  induction k with
  | zero => exact hxP
  | succ k ih =>
      let S := crossPoolIter foodLength (closeTargetBlocks Cat T) P (k + 1)
      let Q := crossPoolIter foodLength (closeTargetBlocks Cat T) P k
      obtain ⟨r, hrS, y, hyS, hCat⟩ := hopen
      have hSQ := crossPoolIter_succ_subset (foodLength := foodLength)
        (closeTargetBlocks Cat T) P k
      have hrData := (mem_crossViableReactions S.1 S.2 x r).mp hrS
      have hleftQ : reactionLeft r ∈ Q.1 ∪ Q.2 := by
        rcases Finset.mem_union.mp hrData.2.1 with h | h
        · exact Finset.mem_union_left _ (hSQ.1 h)
        · exact Finset.mem_union_right _ (hSQ.2 h)
      have hrightQ : reactionRight r ∈ Q.1 ∪ Q.2 := by
        rcases Finset.mem_union.mp hrData.2.2 with h | h
        · exact Finset.mem_union_left _ (hSQ.1 h)
        · exact Finset.mem_union_right _ (hSQ.2 h)
      have hopenQ : catalystPoolFamilyOpen (fun z => Cat z.1 z.2) Q.2
          (crossViableReactions Q.1 Q.2 x) := by
        refine ⟨r, (mem_crossViableReactions Q.1 Q.2 x r).mpr
          ⟨hrData.1, hleftQ, hrightQ⟩, y, hSQ.2 hyS, hCat⟩
      have hxQ : x ∈ (crossPoolIter foodLength Cat P k).1 :=
        ih hopenQ
      have hQactual := crossPoolIter_mono (foodLength := foodLength)
        (P := P) (Q := P) (closeTargetBlocks_le Cat T)
        (Finset.Subset.rfl) (Finset.Subset.rfl) k
      have hleftActual : reactionLeft r ∈
          (crossPoolIter foodLength Cat P k).1 ∪
            (crossPoolIter foodLength Cat P k).2 := by
        rcases Finset.mem_union.mp hleftQ with h | h
        · exact Finset.mem_union_left _ (hQactual.1 h)
        · exact Finset.mem_union_right _ (hQactual.2 h)
      have hrightActual : reactionRight r ∈
          (crossPoolIter foodLength Cat P k).1 ∪
            (crossPoolIter foodLength Cat P k).2 := by
        rcases Finset.mem_union.mp hrightQ with h | h
        · exact Finset.mem_union_left _ (hQactual.1 h)
        · exact Finset.mem_union_right _ (hQactual.2 h)
      have hyActual : y ∈ (crossPoolIter foodLength Cat P k).2 :=
        hQactual.2 (hSQ.2 hyS)
      exact Finset.mem_filter.mpr ⟨hxQ, Or.inr
        ⟨r, hrData.1, hleftActual, hrightActual, y, hyActual, hCat⟩⟩

/-- Good held-out targets whose viable reaction family is actually supported
by a catalyst in the terminal closed-cavity right pool. -/
noncomputable def closedTargetSupportedGoodTargets {n d : Nat}
    (T : Finset (Molecule n))
    (S : Finset (Molecule n) × Finset (Molecule n))
    (ω : AmbientCoord n → Prop) : Finset (Molecule n) := by
  classical
  exact (closedTargetGoodTargets (d := d) T S).filter fun x =>
    catalystPoolFamilyOpen ω S.2 (crossViableReactions S.1 S.2 x)

@[simp] theorem mem_closedTargetSupportedGoodTargets {n d : Nat}
    (T : Finset (Molecule n))
    (S : Finset (Molecule n) × Finset (Molecule n))
    (ω : AmbientCoord n → Prop) (x : Molecule n) :
    x ∈ closedTargetSupportedGoodTargets (d := d) T S ω ↔
      x ∈ closedTargetGoodTargets (d := d) T S ∧
        catalystPoolFamilyOpen ω S.2
          (crossViableReactions S.1 S.2 x) := by
  classical
  simp [closedTargetSupportedGoodTargets]

/-- The adaptive real-valued indicator count is the cardinality of the
corresponding supported-good-target set. -/
theorem closedTargetGoodFamilyCount_eq_card_supported {n d : Nat}
    (T : Finset (Molecule n))
    (S : Finset (Molecule n) × Finset (Molecule n))
    (ω : AmbientCoord n → Prop) :
    closedTargetGoodFamilyCount (d := d) T S (fun z => ω z) =
      (closedTargetSupportedGoodTargets (d := d) T S ω).card := by
  rw [closedTargetGoodFamilyCount_restriction_eq]
  simp [catalystPoolFamilyIndicator, closedTargetSupportedGoodTargets,
    Finset.sum_boole]

/-- Every supported good target counted by the closed-cavity experiment is
an actual survivor of ordinary pruning, provided the held-out shell was
initially assigned to the left pool. -/
theorem closedTargetGoodFamilyCount_le_crossPoolIter_left_card
    {n foodLength k d : Nat} (Cat : Catalysis (Molecule n) (Reaction n))
    (T : Finset (Molecule n))
    (P : Finset (Molecule n) × Finset (Molecule n)) (hTP : T ⊆ P.1) :
    let S := crossPoolIter foodLength (closeTargetBlocks Cat T) P k
    closedTargetGoodFamilyCount (d := d) T S
        (fun z => Cat z.val.1 z.val.2) ≤
      ((crossPoolIter foodLength Cat P k).1.card : ℝ) := by
  classical
  let S := crossPoolIter foodLength (closeTargetBlocks Cat T) P k
  let ω : AmbientCoord n → Prop := fun z => Cat z.1 z.2
  change closedTargetGoodFamilyCount (d := d) T S
      (fun z => ω z) ≤ _
  rw [closedTargetGoodFamilyCount_eq_card_supported]
  exact_mod_cast Finset.card_le_card (by
    intro x hx
    have hxData := (mem_closedTargetSupportedGoodTargets T S
      ω x).mp hx
    have hxT := (mem_closedTargetGoodTargets T S x).mp hxData.1 |>.1
    exact mem_crossPoolIter_left_of_closedTarget_familyOpen Cat T P
      (hTP hxT) (by simpa [ω] using hxData.2))

/-- The same docking lands inside the held target block, not merely inside the
whole retained pool.  This is the layer-by-layer bootstrap interface. -/
theorem closedTargetGoodFamilyCount_le_target_inter_crossPoolIter_left_card
    {n foodLength k d : Nat} (Cat : Catalysis (Molecule n) (Reaction n))
    (T : Finset (Molecule n))
    (P : Finset (Molecule n) × Finset (Molecule n)) (hTP : T ⊆ P.1) :
    let S := crossPoolIter foodLength (closeTargetBlocks Cat T) P k
    closedTargetGoodFamilyCount (d := d) T S
        (fun z => Cat z.val.1 z.val.2) ≤
      ((T ∩ (crossPoolIter foodLength Cat P k).1).card : ℝ) := by
  classical
  let S := crossPoolIter foodLength (closeTargetBlocks Cat T) P k
  let ω : AmbientCoord n → Prop := fun z => Cat z.1 z.2
  change closedTargetGoodFamilyCount (d := d) T S (fun z => ω z) ≤ _
  rw [closedTargetGoodFamilyCount_eq_card_supported]
  exact_mod_cast Finset.card_le_card (by
    intro x hx
    have hxData := (mem_closedTargetSupportedGoodTargets T S ω x).mp hx
    have hxT := (mem_closedTargetGoodTargets T S x).mp hxData.1 |>.1
    exact Finset.mem_inter.mpr ⟨hxT,
      mem_crossPoolIter_left_of_closedTarget_familyOpen Cat T P
        (hTP hxT) (by simpa [ω] using hxData.2)⟩)

/-- Adaptive lower tail for the number of actual survivors in the held target
block. -/
theorem measure_target_inter_crossPoolIter_left_card_le_adaptive_bound
    {n foodLength k d : Nat} (lambda : ℝ) (T : Finset (Molecule n))
    (P : Finset (Molecule n) × Finset (Molecule n)) (hTP : T ⊆ P.1)
    {c : ℝ} (hc : 0 < c) :
    ambientPiMeasure n lambda {ω |
      let Cat : Catalysis (Molecule n) (Reaction n) := fun y r => ω (y, r)
      let S := crossPoolIter foodLength (closeTargetBlocks Cat T) P k
      (((T ∩ (crossPoolIter foodLength Cat P k).1).card : Nat) : ℝ) ≤
        ((closedTargetGoodTargets (d := d) T S).card : ℝ) *
          (1 - (toNNReal (σ (catalysisP n lambda)) : ℝ) ^
            (S.2.card * d)) - c} ≤
      ENNReal.ofReal (((T.card : ℝ) / 4) / c ^ 2) := by
  apply le_trans (measure_mono ?_)
    (measure_adaptive_closedTargetGoodFamilyCount_le
      (foodLength := foodLength) (k := k) (d := d) lambda T P hc)
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  let Cat : Catalysis (Molecule n) (Reaction n) := fun y r => ω (y, r)
  let S := crossPoolIter foodLength (closeTargetBlocks Cat T) P k
  have hdock :=
    closedTargetGoodFamilyCount_le_target_inter_crossPoolIter_left_card
      (foodLength := foodLength) (k := k) (d := d) Cat T P hTP
  have hdock' : closedTargetGoodFamilyCount (d := d) T S (fun z => ω z) ≤
      (((T ∩ (crossPoolIter foodLength Cat P k).1).card : Nat) : ℝ) := by
    simpa [Cat, S] using hdock
  exact hdock'.trans hω

/-- Sharp event-conditioned survivor tail obtained by composing the
pool-floor adaptive family estimate with deterministic cavity docking. -/
theorem measure_target_inter_crossPoolIter_left_card_and_poolFloor_le_sharp
    {n foodLength k d b : Nat}
    (lambda : ℝ) (T : Finset (Molecule n))
    (P : Finset (Molecule n) × Finset (Molecule n)) (hTP : T ⊆ P.1)
    {c : ℝ} (hc : 0 < c) :
    ambientPiMeasure n lambda {ω |
      let Cat : Catalysis (Molecule n) (Reaction n) := fun y r => ω (y, r)
      let S := crossPoolIter foodLength (closeTargetBlocks Cat T) P k
      b ≤ S.2.card ∧
      (((T ∩ (crossPoolIter foodLength Cat P k).1).card : Nat) : ℝ) ≤
        ((closedTargetGoodTargets (d := d) T S).card : ℝ) *
          (1 - (toNNReal (σ (catalysisP n lambda)) : ℝ) ^
            (S.2.card * d)) - c} ≤
      ENNReal.ofReal (((T.card : ℝ) *
        (toNNReal (σ (catalysisP n lambda)) : ℝ) ^ (b * d)) /
          c ^ 2) := by
  apply le_trans (measure_mono ?_)
    (measure_adaptive_closedTargetGoodFamilyCount_and_poolFloor_le_sharp
      (foodLength := foodLength) (k := k) (d := d) (b := b)
      lambda T P hc)
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  let Cat : Catalysis (Molecule n) (Reaction n) := fun y r => ω (y, r)
  let S := crossPoolIter foodLength (closeTargetBlocks Cat T) P k
  have hdock :=
    closedTargetGoodFamilyCount_le_target_inter_crossPoolIter_left_card
      (foodLength := foodLength) (k := k) (d := d) Cat T P hTP
  have hdock' : closedTargetGoodFamilyCount (d := d) T S (fun z => ω z) ≤
      (((T ∩ (crossPoolIter foodLength Cat P k).1).card : Nat) : ℝ) := by
    simpa [Cat, S] using hdock
  exact ⟨hω.1, hdock'.trans hω.2⟩

/-- Quantitative survivor lower tail obtained by composing the adaptive
held-out-family estimate with deterministic cavity docking. -/
theorem measure_crossPoolIter_left_card_le_adaptive_closedTarget_bound
    {n foodLength k d : Nat} (lambda : ℝ) (T : Finset (Molecule n))
    (P : Finset (Molecule n) × Finset (Molecule n)) (hTP : T ⊆ P.1)
    {c : ℝ} (hc : 0 < c) :
    ambientPiMeasure n lambda {ω |
      let Cat : Catalysis (Molecule n) (Reaction n) := fun y r => ω (y, r)
      let S := crossPoolIter foodLength (closeTargetBlocks Cat T) P k
      ((crossPoolIter foodLength Cat P k).1.card : ℝ) ≤
        ((closedTargetGoodTargets (d := d) T S).card : ℝ) *
          (1 - (toNNReal (σ (catalysisP n lambda)) : ℝ) ^
            (S.2.card * d)) - c} ≤
      ENNReal.ofReal (((T.card : ℝ) / 4) / c ^ 2) := by
  apply le_trans (measure_mono ?_)
    (measure_adaptive_closedTargetGoodFamilyCount_le
      (foodLength := foodLength) (k := k) (d := d) lambda T P hc)
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  let Cat : Catalysis (Molecule n) (Reaction n) := fun y r => ω (y, r)
  let S := crossPoolIter foodLength (closeTargetBlocks Cat T) P k
  have hdock := closedTargetGoodFamilyCount_le_crossPoolIter_left_card
    (foodLength := foodLength) (k := k) (d := d) Cat T P hTP
  have hdock' : closedTargetGoodFamilyCount (d := d) T S (fun z => ω z) ≤
      ((crossPoolIter foodLength Cat P k).1.card : ℝ) := by
    simpa [Cat, S] using hdock
  exact hdock'.trans hω

/-- The exact layer-profile good set is contained in the adaptive
reaction-count good set used by the cavity concentration theorem. -/
theorem layerGoodMolecules_subset_closedTargetGoodTargets
    {n m delta : Nat} (hm : 2 ≤ m) (hmn : m ≤ n)
    (A B : Finset (Molecule n)) :
    layerGoodMolecules hm hmn A B delta ⊆
      closedTargetGoodTargets (d := m - delta)
        (layerMolecules (by omega) hmn) (A, B) := by
  classical
  intro x hx
  apply (mem_closedTargetGoodTargets _ _ x).mpr
  refine ⟨layerGoodMolecules_subset_layerMolecules hm hmn A B hx, ?_⟩
  rw [layerGoodMolecules] at hx
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hx
  exact layer_crossViableReactions_card_ge_of_not_mem_tail hm hmn A B
    (Finset.mem_sdiff.mp hw).2

/-- Consequently the adaptive good-target cardinality has the same explicit
lower bound as the overlap-safe missing-split profile. -/
theorem card_closedTargetGoodTargets_layer_ge
    {n m delta : Nat} (hm : 2 ≤ m) (hmn : m ≤ n)
    (A B : Finset (Molecule n)) :
    2 ^ m - (splitMissingTail
        (layerSplitViableTargets hm hmn A B) delta).card ≤
      (closedTargetGoodTargets (d := m - delta)
        (layerMolecules (by omega) hmn) (A, B)).card := by
  rw [← card_layerGoodMolecules hm hmn A B delta]
  exact Finset.card_le_card
    (layerGoodMolecules_subset_closedTargetGoodTargets hm hmn A B)

/-- Arbitrary fixed word blocks inherit the same profile guarantee, losing at
most the global missing-split tail of the layer.  This is the interface needed
for two-block cavity reveals. -/
theorem card_closedTargetGoodTargets_layerWordTargets_ge
    {n m delta : Nat} (hm : 2 ≤ m) (hmn : m ≤ n)
    (A B : Finset (Molecule n)) (W : Finset (Word m)) :
    W.card - (splitMissingTail
        (layerSplitViableTargets hm hmn A B) delta).card ≤
      (closedTargetGoodTargets (d := m - delta)
        (layerWordTargets (by omega) hmn W) (A, B)).card := by
  classical
  let Tail := splitMissingTail
    (layerSplitViableTargets hm hmn A B) delta
  have hsub : layerWordTargets (by omega) hmn (W \ Tail) ⊆
      closedTargetGoodTargets (d := m - delta)
        (layerWordTargets (by omega) hmn W) (A, B) := by
    intro x hx
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hx
    have hwData := Finset.mem_sdiff.mp hw
    apply (mem_closedTargetGoodTargets _ _ _).mpr
    refine ⟨Finset.mem_image.mpr ⟨w, hwData.1, rfl⟩, ?_⟩
    exact layer_crossViableReactions_card_ge_of_not_mem_tail hm hmn A B
      hwData.2
  calc
    W.card - Tail.card ≤ (W \ Tail).card := by
      rw [Finset.card_sdiff]
      have hinter : (Tail ∩ W).card ≤ Tail.card :=
        Finset.card_le_card (Finset.inter_subset_left)
      exact Nat.sub_le_sub_left hinter W.card
    _ = (layerWordTargets (by omega) hmn (W \ Tail)).card := by simp
    _ ≤ (closedTargetGoodTargets (d := m - delta)
        (layerWordTargets (by omega) hmn W) (A, B)).card :=
      Finset.card_le_card hsub

/-- Full local layer barrier: for any fixed word block, the actual survivor
count is unlikely to fall below the factor-profile lower bound times the exact
family-open probability computed from the terminal closed-cavity catalyst
pool. -/
theorem measure_crossPoolIter_left_layerWordTargets_barrier
    {n m foodLength k delta : Nat} (hm : 2 ≤ m) (hmn : m ≤ n)
    (lambda : ℝ) (W : Finset (Word m))
    (P : Finset (Molecule n) × Finset (Molecule n))
    (hWP : layerWordTargets (by omega) hmn W ⊆ P.1)
    {c : ℝ} (hc : 0 < c) :
    ambientPiMeasure n lambda {ω |
      let Cat : Catalysis (Molecule n) (Reaction n) := fun y r => ω (y, r)
      let T := layerWordTargets (by omega) hmn W
      let S := crossPoolIter foodLength (closeTargetBlocks Cat T) P k
      ((crossPoolIter foodLength Cat P k).1.card : ℝ) ≤
        ((W.card - (splitMissingTail
          (layerSplitViableTargets hm hmn S.1 S.2) delta).card : Nat) : ℝ) *
          (1 - (toNNReal (σ (catalysisP n lambda)) : ℝ) ^
            (S.2.card * (m - delta))) - c} ≤
      ENNReal.ofReal (((W.card : ℝ) / 4) / c ^ 2) := by
  classical
  let T := layerWordTargets (by omega) hmn W
  calc
    _ ≤ ambientPiMeasure n lambda {ω |
        let Cat : Catalysis (Molecule n) (Reaction n) := fun y r => ω (y, r)
        let S := crossPoolIter foodLength (closeTargetBlocks Cat T) P k
        ((crossPoolIter foodLength Cat P k).1.card : ℝ) ≤
          ((closedTargetGoodTargets (d := m - delta) T S).card : ℝ) *
            (1 - (toNNReal (σ (catalysisP n lambda)) : ℝ) ^
              (S.2.card * (m - delta))) - c} := by
      apply measure_mono
      intro ω hω
      simp only [Set.mem_setOf_eq] at hω ⊢
      let Cat : Catalysis (Molecule n) (Reaction n) := fun y r => ω (y, r)
      let S := crossPoolIter foodLength (closeTargetBlocks Cat T) P k
      have hG := card_closedTargetGoodTargets_layerWordTargets_ge
        (delta := delta) hm hmn S.1 S.2 W
      have hq0 : 0 ≤ (toNNReal (σ (catalysisP n lambda)) : ℝ) := by positivity
      have hq1 : (toNNReal (σ (catalysisP n lambda)) : ℝ) ≤ 1 := by
        exact_mod_cast (σ (catalysisP n lambda)).2.2
      have hp : 0 ≤ 1 -
          (toNNReal (σ (catalysisP n lambda)) : ℝ) ^
            (S.2.card * (m - delta)) := by
        have hpw := pow_le_one₀ (n := S.2.card * (m - delta)) hq0 hq1
        linarith
      have hmul :
          ((W.card - (splitMissingTail
            (layerSplitViableTargets hm hmn S.1 S.2) delta).card : Nat) : ℝ) *
              (1 - (toNNReal (σ (catalysisP n lambda)) : ℝ) ^
                (S.2.card * (m - delta))) ≤
            ((closedTargetGoodTargets (d := m - delta) T S).card : ℝ) *
              (1 - (toNNReal (σ (catalysisP n lambda)) : ℝ) ^
                (S.2.card * (m - delta))) := by
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast hG
        · exact hp
      exact hω.trans (sub_le_sub_right hmul c)
    _ ≤ _ := by
      simpa [T] using
        (measure_crossPoolIter_left_card_le_adaptive_closedTarget_bound
          (foodLength := foodLength) (k := k) (d := m - delta)
          lambda T P hWP hc)

end HordijkSteelThreshold
