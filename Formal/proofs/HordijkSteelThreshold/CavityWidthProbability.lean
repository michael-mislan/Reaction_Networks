import proofs.HordijkSteelThreshold.CavityWidth
import proofs.HordijkSteelThreshold.TargetBlockCavityIndependence
import proofs.HordijkSteelThreshold.FamilyOpenProbability
import proofs.HordijkSteelThreshold.AdaptiveChainBound

namespace HordijkSteelThreshold

open MeasureTheory ProbabilityTheory unitInterval
open RAF RAF.Polymer RAF.Concrete

/-- A cavity obtained by first withholding `U` and then deterministically
withholding `T` is independent of the still-unrevealed `U` target block. -/
theorem preclosedTargetIter_statistics_indep {n foodLength k : Nat}
    (lambda : ℝ) (T U : Finset (Molecule n))
    (P : Finset (Molecule n) × Finset (Molecule n))
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (f : (Finset (Molecule n) × Finset (Molecule n)) → α)
    (g : (catalystPoolTargetBlock
      (Finset.univ : Finset (Molecule n)) U → Prop) → β)
    (hf : Measurable (fun v => f (crossPoolIter foodLength
      (closeTargetBlocks
        (catalysisFromTargetRestriction
          ((Finset.univ : Finset (Molecule n)) \ U) v) T) P k)))
    (hg : Measurable g) :
    IndepFun
      (fun (ω : AmbientCoord n → Prop) =>
        f (crossPoolIter foodLength
          (closeTargetBlocks (fun y r => ω (y, r)) (T ∪ U)) P k))
      (fun (ω : AmbientCoord n → Prop) =>
        g (fun z : catalystPoolTargetBlock
          (Finset.univ : Finset (Molecule n)) U => ω z))
      (ambientPiMeasure n lambda) := by
  let V : Finset (Molecule n) :=
    (Finset.univ : Finset (Molecule n)) \ U
  have hVU : Disjoint V U := by
    simp [V, Finset.disjoint_left]
  have hind := catalystPoolTarget_statistics_indep lambda
    (Finset.univ : Finset (Molecule n)) hVU
    (fun v => f (crossPoolIter foodLength
      (closeTargetBlocks (catalysisFromTargetRestriction V v) T) P k))
    g hf hg
  have hclose (ω : AmbientCoord n → Prop) :
      closeTargetBlocks (fun y r => ω (y, r)) (T ∪ U) =
        closeTargetBlocks
          (catalysisFromTargetRestriction
            ((Finset.univ : Finset (Molecule n)) \ U) (fun z => ω z)) T := by
    rw [Finset.union_comm, ← closeTargetBlocks_union,
      closeTargetBlocks_eq_from_complement]
  simpa only [V, Function.comp_apply, hclose] using hind

/-- Uniform section bounds survive a cavity that has an already specified
closed block `T` in addition to the fresh block `U`. -/
theorem measure_adaptive_preclosedTargetIter_le {n foodLength k : Nat}
    (lambda : ℝ) (T U : Finset (Molecule n))
    (P : Finset (Molecule n) × Finset (Molecule n))
    (H : (Finset (Molecule n) × Finset (Molecule n)) →
      (catalystPoolTargetBlock
        (Finset.univ : Finset (Molecule n)) U → Prop) → Prop)
    (hH : ∀ S, MeasurableSet {v | H S v}) {p : ENNReal}
    (hsec : ∀ S,
      ambientPiMeasure n lambda {ω | H S (fun z => ω z)} ≤ p) :
    ambientPiMeasure n lambda {ω |
      H (crossPoolIter foodLength
          (closeTargetBlocks (fun y r => ω (y, r)) (T ∪ U)) P k)
        (fun z => ω z)} ≤ p := by
  let State := Finset (Molecule n) × Finset (Molecule n)
  letI : MeasurableSpace State := ⊤
  let X : (AmbientCoord n → Prop) → State := fun ω =>
    crossPoolIter foodLength
      (closeTargetBlocks (fun y r => ω (y, r)) (T ∪ U)) P k
  let Y : (AmbientCoord n → Prop) →
      (catalystPoolTargetBlock
        (Finset.univ : Finset (Molecule n)) U → Prop) :=
    fun ω z => ω z
  have hind : IndepFun X Y (ambientPiMeasure n lambda) := by
    simpa [X, Y, State] using preclosedTargetIter_statistics_indep
      lambda T U P (fun S => S) (fun v => v)
      (measurable_of_finite _) measurable_id
  exact measure_adaptive_of_indep_finite hind (measurable_of_finite _) H hH hsec

/-- Weighted form of the pre-closed cavity mixture.  A complementary-state
event `K` may carry all later reveals in an ordered exploration, so successive
fresh target costs multiply. -/
theorem measure_adaptive_preclosedTargetIter_inter_le
    {n foodLength k : Nat}
    (lambda : ℝ) (T U : Finset (Molecule n))
    (P : Finset (Molecule n) × Finset (Molecule n))
    (K : (Finset (Molecule n) × Finset (Molecule n)) → Prop)
    (H : (Finset (Molecule n) × Finset (Molecule n)) →
      (catalystPoolTargetBlock
        (Finset.univ : Finset (Molecule n)) U → Prop) → Prop)
    (hH : ∀ S, MeasurableSet {v | H S v}) {p : ENNReal}
    (hsec : ∀ S,
      ambientPiMeasure n lambda {ω | H S (fun z => ω z)} ≤ p) :
    ambientPiMeasure n lambda {ω |
      let S := crossPoolIter foodLength
        (closeTargetBlocks (fun y r => ω (y, r)) (T ∪ U)) P k
      K S ∧ H S (fun z => ω z)} ≤
      p * ambientPiMeasure n lambda {ω |
        K (crossPoolIter foodLength
          (closeTargetBlocks (fun y r => ω (y, r)) (T ∪ U)) P k)} := by
  let State := Finset (Molecule n) × Finset (Molecule n)
  letI : MeasurableSpace State := ⊤
  let X : (AmbientCoord n → Prop) → State := fun ω =>
    crossPoolIter foodLength
      (closeTargetBlocks (fun y r => ω (y, r)) (T ∪ U)) P k
  let Y : (AmbientCoord n → Prop) →
      (catalystPoolTargetBlock
        (Finset.univ : Finset (Molecule n)) U → Prop) :=
    fun ω z => ω z
  have hind : IndepFun X Y (ambientPiMeasure n lambda) := by
    simpa [X, Y, State] using preclosedTargetIter_statistics_indep
      lambda T U P (fun S => S) (fun v => v)
      (measurable_of_finite _) measurable_id
  simpa [X, Y, State] using measure_adaptive_of_indep_finite_inter_le
    hind (measurable_of_finite _) K H hH hsec

/-- Strong weighted pre-closed mixture retaining the complete complementary
target restriction.  Unlike the state-only form above, `K` may inspect every
coordinate outside `U`; consequently it can encode all later disjoint batches
in an ordered reveal while the current `U`-section cost still multiplies. -/
theorem measure_adaptive_preclosedTargetIter_complement_inter_le
    {n foodLength k : Nat}
    (lambda : ℝ) (T U : Finset (Molecule n))
    (P : Finset (Molecule n) × Finset (Molecule n))
    (K : (catalystPoolTargetBlock
      (Finset.univ : Finset (Molecule n))
        ((Finset.univ : Finset (Molecule n)) \ U) → Prop) → Prop)
    (H : (Finset (Molecule n) × Finset (Molecule n)) →
      (catalystPoolTargetBlock
        (Finset.univ : Finset (Molecule n)) U → Prop) → Prop)
    (hH : ∀ S, MeasurableSet {v | H S v}) {p : ENNReal}
    (hsec : ∀ S,
      ambientPiMeasure n lambda {ω | H S (fun z => ω z)} ≤ p) :
    ambientPiMeasure n lambda {ω |
      K (fun z : catalystPoolTargetBlock
          (Finset.univ : Finset (Molecule n))
            ((Finset.univ : Finset (Molecule n)) \ U) => ω z) ∧
        H (crossPoolIter foodLength
            (closeTargetBlocks (fun y r => ω (y, r)) (T ∪ U)) P k)
          (fun z : catalystPoolTargetBlock
            (Finset.univ : Finset (Molecule n)) U => ω z)} ≤
      p * ambientPiMeasure n lambda {ω |
        K (fun z : catalystPoolTargetBlock
          (Finset.univ : Finset (Molecule n))
            ((Finset.univ : Finset (Molecule n)) \ U) => ω z)} := by
  let V : Finset (Molecule n) :=
    (Finset.univ : Finset (Molecule n)) \ U
  let X := fun (ω : AmbientCoord n → Prop)
    (z : catalystPoolTargetBlock
      (Finset.univ : Finset (Molecule n)) V) => ω z
  let Y := fun (ω : AmbientCoord n → Prop)
    (z : catalystPoolTargetBlock
      (Finset.univ : Finset (Molecule n)) U) => ω z
  let State := Finset (Molecule n) × Finset (Molecule n)
  let S : (catalystPoolTargetBlock
      (Finset.univ : Finset (Molecule n)) V → Prop) → State := fun v =>
    crossPoolIter foodLength
      (closeTargetBlocks (catalysisFromTargetRestriction V v) T) P k
  let H' := fun v w => H (S v) w
  have hVU : Disjoint V U := by
    simp [V, Finset.disjoint_left]
  have hind : IndepFun X Y (ambientPiMeasure n lambda) := by
    simpa [X, Y] using catalystPoolTarget_restrictions_indep
      lambda (Finset.univ : Finset (Molecule n)) hVU
  have hH' : ∀ v, MeasurableSet {w | H' v w} := by
    intro v
    exact hH (S v)
  have hsec' : ∀ v,
      ambientPiMeasure n lambda {ω | H' v (Y ω)} ≤ p := by
    intro v
    simpa [H', Y] using hsec (S v)
  have hweighted := measure_adaptive_of_indep_finite_inter_le hind
    (measurable_of_finite _) K H' hH' hsec'
  have hclose (ω : AmbientCoord n → Prop) :
      closeTargetBlocks (fun y r => ω (y, r)) (T ∪ U) =
        closeTargetBlocks
          (catalysisFromTargetRestriction V (X ω)) T := by
    rw [Finset.union_comm, ← closeTargetBlocks_union,
      closeTargetBlocks_eq_from_complement]
  simpa only [V, X, Y, S, H', Function.comp_apply, hclose] using hweighted

/-- Reconstructing the singleton target block preserves every reaction family
whose reactions all produce that singleton target. -/
theorem catalystPoolFamilyOpen_singleton_restriction_iff
    {n : Nat} (ω : AmbientCoord n → Prop)
    (C : Finset (Molecule n)) (x : Molecule n)
    (R : Finset (Reaction n))
    (hprod : ∀ r ∈ R, reactionProduct r = x) :
    catalystPoolFamilyOpen
        (fun z => catalysisFromTargetRestriction {x} (fun w => ω w) z.1 z.2)
        C R ↔
      catalystPoolFamilyOpen ω C R := by
  constructor
  · rintro ⟨r, hr, y, hy, hcat⟩
    have hrx : reactionProduct r ∈ ({x} : Finset (Molecule n)) := by
      simp [hprod r hr]
    have hcat' := (catalysisFromTargetRestriction_apply {x}
      (fun w => ω w) y r).mp hcat
    exact ⟨r, hr, y, hy, by simpa using hcat'.choose_spec⟩
  · rintro ⟨r, hr, y, hy, hcat⟩
    refine ⟨r, hr, y, hy, ?_⟩
    apply (catalysisFromTargetRestriction_apply {x}
      (fun w => ω w) y r).mpr
    refine ⟨by simp [hprod r hr], ?_⟩
    simpa using hcat

/-- General target-block reconstruction form of the preceding lemma. -/
theorem catalystPoolFamilyOpen_target_restriction_iff
    {n : Nat} (ω : AmbientCoord n → Prop)
    (U C : Finset (Molecule n)) (x : Molecule n) (hxU : x ∈ U)
    (R : Finset (Reaction n))
    (hprod : ∀ r ∈ R, reactionProduct r = x) :
    catalystPoolFamilyOpen
        (fun z => catalysisFromTargetRestriction U (fun w => ω w) z.1 z.2)
        C R ↔
      catalystPoolFamilyOpen ω C R := by
  constructor
  · rintro ⟨r, hr, y, hy, hcat⟩
    have htarget : reactionProduct r ∈ U := hprod r hr |>.symm ▸ hxU
    have hcat' := (catalysisFromTargetRestriction_apply U
      (fun w => ω w) y r).mp hcat
    exact ⟨r, hr, y, hy, by simpa using hcat'.choose_spec⟩
  · rintro ⟨r, hr, y, hy, hcat⟩
    refine ⟨r, hr, y, hy, ?_⟩
    apply (catalysisFromTargetRestriction_apply U
      (fun w => ω w) y r).mpr
    refine ⟨hprod r hr |>.symm ▸ hxU, ?_⟩
    simpa using hcat

theorem catalystPoolFamiliesClosed_target_restriction_iff
    {n : Nat} (ω : AmbientCoord n → Prop)
    (U C : Finset (Molecule n)) (R : Molecule n → Finset (Reaction n))
    (hprod : ∀ x ∈ U, ∀ r ∈ R x, reactionProduct r = x) :
    catalystPoolFamiliesClosed
        (fun z => catalysisFromTargetRestriction U (fun w => ω w) z.1 z.2)
        C U R ↔ catalystPoolFamiliesClosed ω C U R := by
  constructor
  · intro hclosed x hx hopen
    apply hclosed x hx
    rw [catalystPoolFamilyOpen_target_restriction_iff ω U C x hx]
    · exact hopen
    · exact hprod x hx
  · intro hclosed x hx hopen
    apply hclosed x hx
    rw [← catalystPoolFamilyOpen_target_restriction_iff ω U C x hx]
    · exact hopen
    · exact hprod x hx

/-- Simultaneous family-closure cost in a common deep cavity.  The pre-closed
block `T` is arbitrary, while every target coordinate in `U` is fresh against
the state obtained by closing `T ∪ U`. -/
theorem measure_adaptive_preclosed_familiesClosed_le
    {n foodLength k b d : Nat} (lambda : ℝ)
    (T U : Finset (Molecule n))
    (P : Finset (Molecule n) × Finset (Molecule n)) :
    ambientPiMeasure n lambda {ω |
      let S := crossPoolIter foodLength
        (closeTargetBlocks (fun y r => ω (y, r)) (T ∪ U)) P k
      b ≤ S.2.card ∧
        (∀ x ∈ U, d ≤ (crossViableReactions S.1 S.2 x).card) ∧
        catalystPoolFamiliesClosed ω S.2 U
          (crossViableReactions S.1 S.2)} ≤
      (toNNReal (σ (catalysisP n lambda)) : ENNReal) ^
        (b * (d * U.card)) := by
  classical
  let H := fun (S : Finset (Molecule n) × Finset (Molecule n))
      (v : catalystPoolTargetBlock
        (Finset.univ : Finset (Molecule n)) U → Prop) =>
    b ≤ S.2.card ∧
      (∀ x ∈ U, d ≤ (crossViableReactions S.1 S.2 x).card) ∧
      catalystPoolFamiliesClosed
        (fun z => catalysisFromTargetRestriction U v z.1 z.2)
        S.2 U (crossViableReactions S.1 S.2)
  have hsec : ∀ S,
      ambientPiMeasure n lambda {ω | H S (fun z => ω z)} ≤
        (toNNReal (σ (catalysisP n lambda)) : ENNReal) ^
          (b * (d * U.card)) := by
    intro S
    by_cases hbS : b ≤ S.2.card
    · by_cases hdS : ∀ x ∈ U,
          d ≤ (crossViableReactions S.1 S.2 x).card
      · have hevent : {ω : AmbientCoord n → Prop | H S (fun z => ω z)} =
            {ω | catalystPoolFamiliesClosed ω S.2 U
              (crossViableReactions S.1 S.2)} := by
          ext ω
          simp only [Set.mem_setOf_eq, H, hbS, true_and]
          have hrestr := catalystPoolFamiliesClosed_target_restriction_iff
            ω U S.2 (crossViableReactions S.1 S.2) (fun x hx r hr =>
              (mem_crossViableReactions S.1 S.2 x r).mp hr |>.1)
          rw [hrestr]
          exact and_iff_right hdS
        rw [hevent, measure_catalystPoolFamiliesClosed]
        apply pow_le_pow_right_of_le_one'
        · exact_mod_cast (σ (catalysisP n lambda)).2.2
        · apply Nat.mul_le_mul hbS
          · exact card_biUnion_crossViableReactions_ge S.1 S.2 U hdS
      · simp [H, hdS]
    · simp [H, hbS]
  have hadaptive := measure_adaptive_preclosedTargetIter_le
    (foodLength := foodLength) (k := k)
    lambda T U P H (fun _ => (Set.toFinite _).measurableSet) hsec
  rw [show {ω : AmbientCoord n → Prop |
      let S := crossPoolIter foodLength
        (closeTargetBlocks (fun y r => ω (y, r)) (T ∪ U)) P k
      b ≤ S.2.card ∧
        (∀ x ∈ U, d ≤ (crossViableReactions S.1 S.2 x).card) ∧
        catalystPoolFamiliesClosed ω S.2 U
          (crossViableReactions S.1 S.2)} =
      {ω | H (crossPoolIter foodLength
          (closeTargetBlocks (fun y r => ω (y, r)) (T ∪ U)) P k)
        (fun z => ω z)} by
    ext ω
    simp only [Set.mem_setOf_eq, H]
    let S := crossPoolIter foodLength
      (closeTargetBlocks (fun y r => ω (y, r)) (T ∪ U)) P k
    have hrestr := catalystPoolFamiliesClosed_target_restriction_iff
      ω U S.2 (crossViableReactions S.1 S.2) (fun x hx r hr =>
        (mem_crossViableReactions S.1 S.2 x r).mp hr |>.1)
    rw [hrestr]]
  exact hadaptive

/-- Weighted simultaneous family-closure cost retaining every coordinate
outside the fresh target block.  This is the one-step multiplicative interface
for a chain of disjoint adaptive batches. -/
theorem measure_adaptive_preclosed_familiesClosed_complement_inter_le
    {n foodLength k b d : Nat} (lambda : ℝ)
    (T U : Finset (Molecule n))
    (P : Finset (Molecule n) × Finset (Molecule n))
    (K : (catalystPoolTargetBlock
      (Finset.univ : Finset (Molecule n))
        ((Finset.univ : Finset (Molecule n)) \ U) → Prop) → Prop) :
    ambientPiMeasure n lambda {ω |
      K (fun z : catalystPoolTargetBlock
          (Finset.univ : Finset (Molecule n))
            ((Finset.univ : Finset (Molecule n)) \ U) => ω z) ∧
        let S := crossPoolIter foodLength
          (closeTargetBlocks (fun y r => ω (y, r)) (T ∪ U)) P k
        b ≤ S.2.card ∧
          (∀ x ∈ U, d ≤ (crossViableReactions S.1 S.2 x).card) ∧
          catalystPoolFamiliesClosed ω S.2 U
            (crossViableReactions S.1 S.2)} ≤
      (toNNReal (σ (catalysisP n lambda)) : ENNReal) ^
          (b * (d * U.card)) *
        ambientPiMeasure n lambda {ω |
          K (fun z : catalystPoolTargetBlock
            (Finset.univ : Finset (Molecule n))
              ((Finset.univ : Finset (Molecule n)) \ U) => ω z)} := by
  classical
  let H := fun (S : Finset (Molecule n) × Finset (Molecule n))
      (v : catalystPoolTargetBlock
        (Finset.univ : Finset (Molecule n)) U → Prop) =>
    b ≤ S.2.card ∧
      (∀ x ∈ U, d ≤ (crossViableReactions S.1 S.2 x).card) ∧
      catalystPoolFamiliesClosed
        (fun z => catalysisFromTargetRestriction U v z.1 z.2)
        S.2 U (crossViableReactions S.1 S.2)
  have hsec : ∀ S,
      ambientPiMeasure n lambda {ω | H S (fun z => ω z)} ≤
        (toNNReal (σ (catalysisP n lambda)) : ENNReal) ^
          (b * (d * U.card)) := by
    intro S
    by_cases hbS : b ≤ S.2.card
    · by_cases hdS : ∀ x ∈ U,
          d ≤ (crossViableReactions S.1 S.2 x).card
      · have hevent : {ω : AmbientCoord n → Prop | H S (fun z => ω z)} =
            {ω | catalystPoolFamiliesClosed ω S.2 U
              (crossViableReactions S.1 S.2)} := by
          ext ω
          simp only [Set.mem_setOf_eq, H, hbS, true_and]
          have hrestr := catalystPoolFamiliesClosed_target_restriction_iff
            ω U S.2 (crossViableReactions S.1 S.2) (fun x hx r hr =>
              (mem_crossViableReactions S.1 S.2 x r).mp hr |>.1)
          rw [hrestr]
          exact and_iff_right hdS
        rw [hevent, measure_catalystPoolFamiliesClosed]
        apply pow_le_pow_right_of_le_one'
        · exact_mod_cast (σ (catalysisP n lambda)).2.2
        · apply Nat.mul_le_mul hbS
          exact card_biUnion_crossViableReactions_ge S.1 S.2 U hdS
      · simp [H, hdS]
    · simp [H, hbS]
  have hadaptive := measure_adaptive_preclosedTargetIter_complement_inter_le
    (foodLength := foodLength) (k := k)
    lambda T U P K H (fun _ => (Set.toFinite _).measurableSet) hsec
  refine (measure_mono ?_).trans hadaptive
  intro ω hω
  refine ⟨hω.1, ?_⟩
  dsimp only at hω ⊢
  refine ⟨hω.2.1, hω.2.2.1, ?_⟩
  have hrestr := catalystPoolFamiliesClosed_target_restriction_iff
    ω U
      (crossPoolIter foodLength
        (closeTargetBlocks (fun y r => ω (y, r)) (T ∪ U)) P k).2
      (crossViableReactions
        (crossPoolIter foodLength
          (closeTargetBlocks (fun y r => ω (y, r)) (T ∪ U)) P k).1
        (crossPoolIter foodLength
          (closeTargetBlocks (fun y r => ω (y, r)) (T ∪ U)) P k).2)
      (fun x hx r hr =>
        (mem_crossViableReactions _ _ x r).mp hr |>.1)
  exact hrestr.mpr hω.2.2.2

/-- A fixed subset of one actual fresh left generation has the full common
deep-cavity Peierls cost. -/
theorem measure_freshLeftTargetCavityWidth_batch_deep_good_le
    {n foodLength k b d : Nat} (lambda : ℝ)
    (T U : Finset (Molecule n))
    (P : Finset (Molecule n) × Finset (Molecule n)) :
    ambientPiMeasure n lambda {ω |
      U ⊆ freshLeftTargetCavityWidth (foodLength := foodLength)
        (fun y r => ω (y, r)) T P k ∧
      let S := crossPoolIter foodLength
        (closeTargetBlocks (fun y r => ω (y, r)) (T ∪ U)) P k
      b ≤ S.2.card ∧
        ∀ x ∈ U, d ≤ (crossViableReactions S.1 S.2 x).card} ≤
      (toNNReal (σ (catalysisP n lambda)) : ENNReal) ^
        (b * (d * U.card)) := by
  have hprob := measure_adaptive_preclosed_familiesClosed_le
    (foodLength := foodLength) (k := k) (b := b) (d := d)
    lambda T U P
  refine (measure_mono ?_).trans hprob
  intro ω hω
  dsimp only at hω ⊢
  refine ⟨hω.2.1, hω.2.2, ?_⟩
  intro x hxU
  have hclosed := freshLeftTargetCavityWidth_batch_familyClosed
    (fun y r => ω (y, r)) T U P x hxU (hω.1 hxU)
  exact hclosed.2

/-- Right-pool form of the fixed fresh-batch Peierls cost. -/
theorem measure_freshRightTargetCavityWidth_batch_deep_good_le
    {n foodLength k b d : Nat} (lambda : ℝ)
    (T U : Finset (Molecule n))
    (P : Finset (Molecule n) × Finset (Molecule n)) :
    ambientPiMeasure n lambda {ω |
      U ⊆ freshRightTargetCavityWidth (foodLength := foodLength)
        (fun y r => ω (y, r)) T P k ∧
      let S := crossPoolIter foodLength
        (closeTargetBlocks (fun y r => ω (y, r)) (T ∪ U)) P k
      b ≤ S.1.card ∧
        ∀ x ∈ U, d ≤ (crossViableReactions S.2 S.1 x).card} ≤
      (toNNReal (σ (catalysisP n lambda)) : ENNReal) ^
        (b * (d * U.card)) := by
  simpa only [freshRightTargetCavityWidth_eq_left_swap,
    crossPoolIter_swap] using
    (measure_freshLeftTargetCavityWidth_batch_deep_good_le
      (foodLength := foodLength) (k := k) (b := b) (d := d)
      lambda T U (P.2, P.1))

/-- A fixed batch drawn from the union of every prior fresh left generation
has the full Peierls cost in one terminal common cavity. -/
theorem measure_freshLeft_allPrior_batch_deep_good_le
    {n foodLength k b d : Nat} (lambda : ℝ)
    (T U : Finset (Molecule n))
    (P : Finset (Molecule n) × Finset (Molecule n)) :
    ambientPiMeasure n lambda {ω |
      U ⊆ (Finset.biUnion (Finset.range k) fun j =>
        freshLeftTargetCavityWidth (foodLength := foodLength)
          (fun y r => ω (y, r)) T P j) ∧
      let S := crossPoolIter foodLength
        (closeTargetBlocks (fun y r => ω (y, r)) (T ∪ U)) P k
      b ≤ S.2.card ∧
        ∀ x ∈ U, d ≤ (crossViableReactions S.1 S.2 x).card} ≤
      (toNNReal (σ (catalysisP n lambda)) : ENNReal) ^
        (b * (d * U.card)) := by
  have hprob := measure_adaptive_preclosed_familiesClosed_le
    (foodLength := foodLength) (k := k) (b := b) (d := d)
    lambda T U P
  refine (measure_mono ?_).trans hprob
  intro ω hω
  dsimp only at hω ⊢
  refine ⟨hω.2.1, hω.2.2, ?_⟩
  intro x hxU
  have hclosed := freshLeftTargetCavityWidth_all_prior_familyClosed
    (fun y r => ω (y, r)) T U P hω.1 x hxU
  exact hclosed.2

/-- Union over all `t`-subsets of a prospective block, with targets allowed
to have entered the cavity width at different generations. -/
theorem measure_exists_freshLeft_allPrior_batch_deep_good_exact_le
    {n foodLength k b d t : Nat} (lambda : ℝ)
    (T W : Finset (Molecule n))
    (P : Finset (Molecule n) × Finset (Molecule n)) :
    ambientPiMeasure n lambda {ω |
      ∃ U ∈ W.powersetCard t,
        U ⊆ (Finset.biUnion (Finset.range k) fun j =>
          freshLeftTargetCavityWidth (foodLength := foodLength)
            (fun y r => ω (y, r)) T P j) ∧
        let S := crossPoolIter foodLength
          (closeTargetBlocks (fun y r => ω (y, r)) (T ∪ U)) P k
        b ≤ S.2.card ∧
          ∀ x ∈ U, d ≤ (crossViableReactions S.1 S.2 x).card} ≤
      (Nat.choose W.card t : ENNReal) *
        (toNNReal (σ (catalysisP n lambda)) : ENNReal) ^
          (b * (d * t)) := by
  classical
  let Candidates := W.powersetCard t
  let E : Finset (Molecule n) → Set (AmbientCoord n → Prop) := fun U =>
    {ω | U ⊆ (Finset.biUnion (Finset.range k) fun j =>
        freshLeftTargetCavityWidth (foodLength := foodLength)
          (fun y r => ω (y, r)) T P j) ∧
      let S := crossPoolIter foodLength
        (closeTargetBlocks (fun y r => ω (y, r)) (T ∪ U)) P k
      b ≤ S.2.card ∧
        ∀ x ∈ U, d ≤ (crossViableReactions S.1 S.2 x).card}
  rw [show {ω : AmbientCoord n → Prop |
      ∃ U ∈ W.powersetCard t,
        U ⊆ (Finset.biUnion (Finset.range k) fun j =>
          freshLeftTargetCavityWidth (foodLength := foodLength)
            (fun y r => ω (y, r)) T P j) ∧
        let S := crossPoolIter foodLength
          (closeTargetBlocks (fun y r => ω (y, r)) (T ∪ U)) P k
        b ≤ S.2.card ∧
          ∀ x ∈ U, d ≤ (crossViableReactions S.1 S.2 x).card} =
      ⋃ U ∈ Candidates, E U by
    ext ω
    constructor
    · rintro ⟨U, hUC, hUE⟩
      apply Set.mem_iUnion.mpr
      refine ⟨U, Set.mem_iUnion.mpr ⟨by simpa [Candidates] using hUC, hUE⟩⟩
    · intro hω
      rcases Set.mem_iUnion.mp hω with ⟨U, hω⟩
      rcases Set.mem_iUnion.mp hω with ⟨hUC, hUE⟩
      exact ⟨U, by simpa [Candidates] using hUC, hUE⟩]
  calc
    ambientPiMeasure n lambda (⋃ U ∈ Candidates, E U) ≤
        ∑ U ∈ Candidates, ambientPiMeasure n lambda (E U) :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑ _U ∈ Candidates,
        (toNNReal (σ (catalysisP n lambda)) : ENNReal) ^
          (b * (d * t)) := by
      apply Finset.sum_le_sum
      intro U hU
      have hcard := Finset.mem_powersetCard.mp hU |>.2
      simpa only [E, hcard] using
        (measure_freshLeft_allPrior_batch_deep_good_le
          (foodLength := foodLength) (k := k) (b := b) (d := d)
          lambda T U P)
    _ = (Candidates.card : ENNReal) *
        (toNNReal (σ (catalysisP n lambda)) : ENNReal) ^
          (b * (d * t)) := by simp
    _ = (Nat.choose W.card t : ENNReal) *
        (toNNReal (σ (catalysisP n lambda)) : ENNReal) ^
          (b * (d * t)) := by
      rw [show Candidates.card = Nat.choose W.card t by
        change (W.powersetCard t).card = Nat.choose W.card t
        rw [Finset.card_powersetCard]]

/-- Coarser powerset-entropy form retained for callers that do not need the
exact binomial candidate count. -/
theorem measure_exists_freshLeft_allPrior_batch_deep_good_le
    {n foodLength k b d t : Nat} (lambda : ℝ)
    (T W : Finset (Molecule n))
    (P : Finset (Molecule n) × Finset (Molecule n)) :
    ambientPiMeasure n lambda {ω |
      ∃ U ∈ W.powersetCard t,
        U ⊆ (Finset.biUnion (Finset.range k) fun j =>
          freshLeftTargetCavityWidth (foodLength := foodLength)
            (fun y r => ω (y, r)) T P j) ∧
        let S := crossPoolIter foodLength
          (closeTargetBlocks (fun y r => ω (y, r)) (T ∪ U)) P k
        b ≤ S.2.card ∧
          ∀ x ∈ U, d ≤ (crossViableReactions S.1 S.2 x).card} ≤
      (2 ^ W.card : ENNReal) *
        (toNNReal (σ (catalysisP n lambda)) : ENNReal) ^
          (b * (d * t)) := by
  refine (measure_exists_freshLeft_allPrior_batch_deep_good_exact_le
    (foodLength := foodLength) (k := k) (b := b) (d := d) (t := t)
    lambda T W P).trans ?_
  gcongr
  exact_mod_cast Nat.choose_le_two_pow W.card t

/-- Right-pool all-prior-generations Peierls union. -/
theorem measure_exists_freshRight_allPrior_batch_deep_good_le
    {n foodLength k b d t : Nat} (lambda : ℝ)
    (T W : Finset (Molecule n))
    (P : Finset (Molecule n) × Finset (Molecule n)) :
    ambientPiMeasure n lambda {ω |
      ∃ U ∈ W.powersetCard t,
        U ⊆ (Finset.biUnion (Finset.range k) fun j =>
          freshRightTargetCavityWidth (foodLength := foodLength)
            (fun y r => ω (y, r)) T P j) ∧
        let S := crossPoolIter foodLength
          (closeTargetBlocks (fun y r => ω (y, r)) (T ∪ U)) P k
        b ≤ S.1.card ∧
          ∀ x ∈ U, d ≤ (crossViableReactions S.2 S.1 x).card} ≤
      (2 ^ W.card : ENNReal) *
        (toNNReal (σ (catalysisP n lambda)) : ENNReal) ^
          (b * (d * t)) := by
  simpa only [freshRightTargetCavityWidth_eq_left_swap,
    crossPoolIter_swap] using
    (measure_exists_freshLeft_allPrior_batch_deep_good_le
      (foodLength := foodLength) (k := k) (b := b) (d := d) (t := t)
      lambda T W (P.2, P.1))

/-- Terminal diagonal cavity-width Peierls bound with no low-pool exception.
At a fixed `T`-closed state, closing a selected subset of the terminal width
does not alter that state, so the common deep cavity automatically retains
the stated pool and viable-family floors. -/
theorem measure_exists_terminalLeftWidth_batch_good_exact_le
    {n foodLength k b d t : Nat} (lambda : ℝ)
    (T W A : Finset (Molecule n)) :
    ambientPiMeasure n lambda {ω |
      ∃ U ∈ W.powersetCard t,
        U ⊆ leftTargetCavityWidth (foodLength := foodLength)
          (fun y r => ω (y, r)) T (A, A) k \ T ∧
        crossPoolIter foodLength
            (closeTargetBlocks (fun y r => ω (y, r)) T) (A, A) (k + 1) =
          crossPoolIter foodLength
            (closeTargetBlocks (fun y r => ω (y, r)) T) (A, A) k ∧
        let S := crossPoolIter foodLength
          (closeTargetBlocks (fun y r => ω (y, r)) T) (A, A) k
        b ≤ S.2.card ∧
          ∀ x ∈ U, d ≤ (crossViableReactions S.1 S.2 x).card} ≤
      (Nat.choose W.card t : ENNReal) *
        (toNNReal (σ (catalysisP n lambda)) : ENNReal) ^
          (b * (d * t)) := by
  have hprob := measure_exists_freshLeft_allPrior_batch_deep_good_exact_le
    (foodLength := foodLength) (k := k) (b := b) (d := d) (t := t)
    lambda T W (A, A)
  refine (measure_mono ?_).trans hprob
  intro ω hω
  rcases hω with ⟨U, hUW, hUterm, hfix, hb, hd⟩
  have hUwidth : U ⊆ leftTargetCavityWidth (foodLength := foodLength)
      (fun y r => ω (y, r)) T (A, A) k := by
    exact hUterm.trans Finset.sdiff_subset
  have hUfresh : U ⊆ (Finset.range k).biUnion fun j =>
      freshLeftTargetCavityWidth (foodLength := foodLength)
        (fun y r => ω (y, r)) T (A, A) j := by
    intro x hxU
    have hx := Finset.mem_sdiff.mp (hUterm hxU)
    have hcover := leftTargetCavityWidth_subset_held_union_allFresh
      (foodLength := foodLength) (fun y r => ω (y, r)) T (A, A)
      (k := k) hx.1
    rcases Finset.mem_union.mp hcover with hxT | hxfresh
    · exact (hx.2 hxT).elim
    · exact hxfresh
  have heq := crossPoolIter_close_terminalCavity_union_eq
    (foodLength := foodLength) (fun y r => ω (y, r)) T U A hfix hUwidth
  refine ⟨U, hUW, hUfresh, ?_⟩
  rw [heq]
  exact ⟨hb, hd⟩

/-- Coarse powerset-entropy form of the terminal batch estimate. -/
theorem measure_exists_terminalLeftWidth_batch_good_le
    {n foodLength k b d t : Nat} (lambda : ℝ)
    (T W A : Finset (Molecule n)) :
    ambientPiMeasure n lambda {ω |
      ∃ U ∈ W.powersetCard t,
        U ⊆ leftTargetCavityWidth (foodLength := foodLength)
          (fun y r => ω (y, r)) T (A, A) k \ T ∧
        crossPoolIter foodLength
            (closeTargetBlocks (fun y r => ω (y, r)) T) (A, A) (k + 1) =
          crossPoolIter foodLength
            (closeTargetBlocks (fun y r => ω (y, r)) T) (A, A) k ∧
        let S := crossPoolIter foodLength
          (closeTargetBlocks (fun y r => ω (y, r)) T) (A, A) k
        b ≤ S.2.card ∧
          ∀ x ∈ U, d ≤ (crossViableReactions S.1 S.2 x).card} ≤
      (2 ^ W.card : ENNReal) *
        (toNNReal (σ (catalysisP n lambda)) : ENNReal) ^
          (b * (d * t)) := by
  refine (measure_exists_terminalLeftWidth_batch_good_exact_le
    (foodLength := foodLength) (k := k) (b := b) (d := d) (t := t)
    lambda T W A).trans ?_
  gcongr
  exact_mod_cast Nat.choose_le_two_pow W.card t

/-- Terminal cavity-width tail after allowing `r` low-viability exceptions
inside a fixed target block.  If the width contains at least `r+t` targets
and at most `r` have fewer than `d` viable reactions, a good `t`-subset pays
the terminal Peierls cost. -/
theorem measure_terminalLeftWidth_large_of_few_lowViable_exact_le
    {n foodLength k b d r t : Nat} (lambda : ℝ)
    (T W A : Finset (Molecule n)) :
    ambientPiMeasure n lambda {ω |
      crossPoolIter foodLength
          (closeTargetBlocks (fun y z => ω (y, z)) T) (A, A) (k + 1) =
        crossPoolIter foodLength
          (closeTargetBlocks (fun y z => ω (y, z)) T) (A, A) k ∧
      let S := crossPoolIter foodLength
        (closeTargetBlocks (fun y z => ω (y, z)) T) (A, A) k
      b ≤ S.2.card ∧
        r + t ≤ (W ∩ (leftTargetCavityWidth (foodLength := foodLength)
          (fun y z => ω (y, z)) T (A, A) k \ T)).card ∧
        (W.filter fun x =>
          (crossViableReactions S.1 S.2 x).card < d).card ≤ r} ≤
      (Nat.choose W.card t : ENNReal) *
        (toNNReal (σ (catalysisP n lambda)) : ENNReal) ^
          (b * (d * t)) := by
  have hprob := measure_exists_terminalLeftWidth_batch_good_exact_le
    (foodLength := foodLength) (k := k) (b := b) (d := d) (t := t)
    lambda T W A
  refine (measure_mono ?_).trans hprob
  intro ω hω
  rcases hω with ⟨hfix, hb, hlarge, hbad⟩
  let S := crossPoolIter foodLength
    (closeTargetBlocks (fun y z => ω (y, z)) T) (A, A) k
  let D := W ∩ (leftTargetCavityWidth (foodLength := foodLength)
    (fun y z => ω (y, z)) T (A, A) k \ T)
  let Bad := W.filter fun x => (crossViableReactions S.1 S.2 x).card < d
  have hcardD : r + t ≤ D.card := by simpa [D] using hlarge
  have hcardBad : Bad.card ≤ r := by simpa [Bad, S] using hbad
  have hsplit : D.card ≤ (D \ Bad).card + Bad.card :=
    Finset.card_le_card_sdiff_add_card
  have ht : t ≤ (D \ Bad).card := by omega
  obtain ⟨U, hUD, hUcard⟩ := Finset.exists_subset_card_eq ht
  have hUW : U ∈ W.powersetCard t := by
    apply Finset.mem_powersetCard.mpr
    refine ⟨?_, hUcard⟩
    exact hUD.trans (Finset.sdiff_subset.trans Finset.inter_subset_left)
  have hUterm : U ⊆ leftTargetCavityWidth (foodLength := foodLength)
      (fun y z => ω (y, z)) T (A, A) k \ T := by
    exact hUD.trans (Finset.sdiff_subset.trans Finset.inter_subset_right)
  have hdU : ∀ x ∈ U, d ≤ (crossViableReactions S.1 S.2 x).card := by
    intro x hxU
    have hxNotBad : x ∉ Bad := (Finset.mem_sdiff.mp (hUD hxU)).2
    apply Nat.le_of_not_gt
    intro hxlow
    apply hxNotBad
    apply Finset.mem_filter.mpr
    have hUsubW := (Finset.mem_powersetCard.mp hUW).1
    refine ⟨hUsubW hxU, ?_⟩
    exact hxlow
  refine ⟨U, hUW, hUterm, hfix, hb, ?_⟩
  simpa only [S] using hdU

/-- Coarse powerset-entropy form of the terminal width tail. -/
theorem measure_terminalLeftWidth_large_of_few_lowViable_le
    {n foodLength k b d r t : Nat} (lambda : ℝ)
    (T W A : Finset (Molecule n)) :
    ambientPiMeasure n lambda {ω |
      crossPoolIter foodLength
          (closeTargetBlocks (fun y z => ω (y, z)) T) (A, A) (k + 1) =
        crossPoolIter foodLength
          (closeTargetBlocks (fun y z => ω (y, z)) T) (A, A) k ∧
      let S := crossPoolIter foodLength
        (closeTargetBlocks (fun y z => ω (y, z)) T) (A, A) k
      b ≤ S.2.card ∧
        r + t ≤ (W ∩ (leftTargetCavityWidth (foodLength := foodLength)
          (fun y z => ω (y, z)) T (A, A) k \ T)).card ∧
        (W.filter fun x =>
          (crossViableReactions S.1 S.2 x).card < d).card ≤ r} ≤
      (2 ^ W.card : ENNReal) *
        (toNNReal (σ (catalysisP n lambda)) : ENNReal) ^
          (b * (d * t)) := by
  refine (measure_terminalLeftWidth_large_of_few_lowViable_exact_le
    (foodLength := foodLength) (k := k) (b := b) (d := d)
    (r := r) (t := t) lambda T W A).trans ?_
  gcongr
  exact_mod_cast Nat.choose_le_two_pow W.card t

/-- Peierls union over all fixed `t`-subsets of a prospective left target
block.  Deep-cavity authentication is retained for the selected subset. -/
theorem measure_exists_freshLeft_batch_deep_good_le
    {n foodLength k b d t : Nat} (lambda : ℝ)
    (T W : Finset (Molecule n))
    (P : Finset (Molecule n) × Finset (Molecule n)) :
    ambientPiMeasure n lambda {ω |
      ∃ U ∈ W.powersetCard t,
        U ⊆ freshLeftTargetCavityWidth (foodLength := foodLength)
          (fun y r => ω (y, r)) T P k ∧
        let S := crossPoolIter foodLength
          (closeTargetBlocks (fun y r => ω (y, r)) (T ∪ U)) P k
        b ≤ S.2.card ∧
          ∀ x ∈ U, d ≤ (crossViableReactions S.1 S.2 x).card} ≤
      (2 ^ W.card : ENNReal) *
        (toNNReal (σ (catalysisP n lambda)) : ENNReal) ^
          (b * (d * t)) := by
  classical
  let Candidates := W.powersetCard t
  let E : Finset (Molecule n) → Set (AmbientCoord n → Prop) := fun U =>
    {ω | U ⊆ freshLeftTargetCavityWidth (foodLength := foodLength)
        (fun y r => ω (y, r)) T P k ∧
      let S := crossPoolIter foodLength
        (closeTargetBlocks (fun y r => ω (y, r)) (T ∪ U)) P k
      b ≤ S.2.card ∧
        ∀ x ∈ U, d ≤ (crossViableReactions S.1 S.2 x).card}
  rw [show {ω : AmbientCoord n → Prop |
      ∃ U ∈ W.powersetCard t,
        U ⊆ freshLeftTargetCavityWidth (foodLength := foodLength)
          (fun y r => ω (y, r)) T P k ∧
        let S := crossPoolIter foodLength
          (closeTargetBlocks (fun y r => ω (y, r)) (T ∪ U)) P k
        b ≤ S.2.card ∧
          ∀ x ∈ U, d ≤ (crossViableReactions S.1 S.2 x).card} =
      ⋃ U ∈ Candidates, E U by
    ext ω
    constructor
    · rintro ⟨U, hUC, hUE⟩
      apply Set.mem_iUnion.mpr
      refine ⟨U, ?_⟩
      apply Set.mem_iUnion.mpr
      exact ⟨by simpa [Candidates] using hUC, hUE⟩
    · intro hω
      rcases Set.mem_iUnion.mp hω with ⟨U, hω⟩
      rcases Set.mem_iUnion.mp hω with ⟨hUC, hUE⟩
      exact ⟨U, by simpa [Candidates] using hUC, hUE⟩]
  calc
    ambientPiMeasure n lambda (⋃ U ∈ Candidates, E U) ≤
        ∑ U ∈ Candidates, ambientPiMeasure n lambda (E U) :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑ _U ∈ Candidates,
        (toNNReal (σ (catalysisP n lambda)) : ENNReal) ^
          (b * (d * t)) := by
      apply Finset.sum_le_sum
      intro U hU
      have hcard := Finset.mem_powersetCard.mp hU |>.2
      simpa only [E, hcard] using
        (measure_freshLeftTargetCavityWidth_batch_deep_good_le
          (foodLength := foodLength) (k := k) (b := b) (d := d)
          lambda T U P)
    _ = (Candidates.card : ENNReal) *
        (toNNReal (σ (catalysisP n lambda)) : ENNReal) ^
          (b * (d * t)) := by simp
    _ ≤ (2 ^ W.card : ENNReal) *
        (toNNReal (σ (catalysisP n lambda)) : ENNReal) ^
          (b * (d * t)) := by
      gcongr
      exact_mod_cast (show Candidates.card ≤ 2 ^ W.card by
        change (W.powersetCard t).card ≤ 2 ^ W.card
        rw [Finset.card_powersetCard]
        exact Nat.choose_le_two_pow W.card t)

/-- Right-pool form of the adaptive deep-cavity batch union. -/
theorem measure_exists_freshRight_batch_deep_good_le
    {n foodLength k b d t : Nat} (lambda : ℝ)
    (T W : Finset (Molecule n))
    (P : Finset (Molecule n) × Finset (Molecule n)) :
    ambientPiMeasure n lambda {ω |
      ∃ U ∈ W.powersetCard t,
        U ⊆ freshRightTargetCavityWidth (foodLength := foodLength)
          (fun y r => ω (y, r)) T P k ∧
        let S := crossPoolIter foodLength
          (closeTargetBlocks (fun y r => ω (y, r)) (T ∪ U)) P k
        b ≤ S.1.card ∧
          ∀ x ∈ U, d ≤ (crossViableReactions S.2 S.1 x).card} ≤
      (2 ^ W.card : ENNReal) *
        (toNNReal (σ (catalysisP n lambda)) : ENNReal) ^
          (b * (d * t)) := by
  simpa only [freshRightTargetCavityWidth_eq_left_swap,
    crossPoolIter_swap] using
    (measure_exists_freshLeft_batch_deep_good_le
      (foodLength := foodLength) (k := k) (b := b) (d := d) (t := t)
      lambda T W (P.2, P.1))

/-- Exact adaptive singleton marginal for a fresh left cavity generation. -/
theorem measure_freshLeftTargetCavityWidth_mem_and_good_le
    {n foodLength k b d : Nat} (lambda : ℝ)
    (T : Finset (Molecule n))
    (P : Finset (Molecule n) × Finset (Molecule n))
    (x : Molecule n) :
    ambientPiMeasure n lambda {ω |
      x ∈ freshLeftTargetCavityWidth (foodLength := foodLength)
        (fun y r => ω (y, r)) T P k ∧
      let Sx := crossPoolIter foodLength
        (closeTargetBlocks (fun y r => ω (y, r)) (T ∪ {x})) P k
      b ≤ Sx.2.card ∧
        d ≤ (crossViableReactions Sx.1 Sx.2 x).card} ≤
      (toNNReal (σ (catalysisP n lambda)) : ENNReal) ^ (b * d) := by
  classical
  let H := fun (S : Finset (Molecule n) × Finset (Molecule n))
      (v : catalystPoolTargetBlock
        (Finset.univ : Finset (Molecule n)) {x} → Prop) =>
    b ≤ S.2.card ∧
      d ≤ (crossViableReactions S.1 S.2 x).card ∧
      ¬catalystPoolFamilyOpen
        (fun z => catalysisFromTargetRestriction {x} v z.1 z.2)
        S.2 (crossViableReactions S.1 S.2 x)
  have hsec : ∀ S,
      ambientPiMeasure n lambda {ω | H S (fun z => ω z)} ≤
        (toNNReal (σ (catalysisP n lambda)) : ENNReal) ^ (b * d) := by
    intro S
    by_cases hbS : b ≤ S.2.card
    · by_cases hdS : d ≤ (crossViableReactions S.1 S.2 x).card
      · have hevent : {ω : AmbientCoord n → Prop | H S (fun z => ω z)} =
            {ω | ¬catalystPoolFamilyOpen ω S.2
              (crossViableReactions S.1 S.2 x)} := by
          ext ω
          simp only [Set.mem_setOf_eq, H, hbS, hdS, true_and]
          rw [catalystPoolFamilyOpen_singleton_restriction_iff]
          intro r hr
          exact (mem_crossViableReactions S.1 S.2 x r).mp hr |>.1
        rw [hevent]
        calc
          _ ≤ (toNNReal (σ (catalysisP n lambda)) : ENNReal) ^
                (S.2.card * d) :=
            measure_catalystPoolFamilyClosed_le lambda S.2
              (crossViableReactions S.1 S.2 x) hdS
          _ ≤ (toNNReal (σ (catalysisP n lambda)) : ENNReal) ^ (b * d) := by
            apply pow_le_pow_right_of_le_one'
            · exact_mod_cast (σ (catalysisP n lambda)).2.2
            · exact Nat.mul_le_mul_right d hbS
      · simp [H, hdS]
    · simp [H, hbS]
  have hadaptive := measure_adaptive_preclosedTargetIter_le
    (foodLength := foodLength) (k := k)
    lambda T {x} P H (fun _ => (Set.toFinite _).measurableSet) hsec
  refine (measure_mono ?_).trans hadaptive
  intro ω hω
  change H (crossPoolIter foodLength
      (closeTargetBlocks (fun y r => ω (y, r)) (T ∪ {x})) P k)
      (fun z => ω z)
  refine ⟨hω.2.1, hω.2.2, ?_⟩
  have hclosed := freshLeftTargetCavityWidth_leaveOne_familyClosed
    (fun y r => ω (y, r)) T P hω.1
  rw [catalystPoolFamilyOpen_singleton_restriction_iff]
  · exact hclosed.2
  · intro r hr
    exact (mem_crossViableReactions
      (crossPoolIter foodLength
        (closeTargetBlocks (fun y r => ω (y, r)) (T ∪ {x})) P k).1
      (crossPoolIter foodLength
        (closeTargetBlocks (fun y r => ω (y, r)) (T ∪ {x})) P k).2
      x r).mp hr |>.1

/-- Right-pool form of the adaptive singleton marginal. -/
theorem measure_freshRightTargetCavityWidth_mem_and_good_le
    {n foodLength k b d : Nat} (lambda : ℝ)
    (T : Finset (Molecule n))
    (P : Finset (Molecule n) × Finset (Molecule n))
    (x : Molecule n) :
    ambientPiMeasure n lambda {ω |
      x ∈ freshRightTargetCavityWidth (foodLength := foodLength)
        (fun y r => ω (y, r)) T P k ∧
      let Sx := crossPoolIter foodLength
        (closeTargetBlocks (fun y r => ω (y, r)) (T ∪ {x})) P k
      b ≤ Sx.1.card ∧
        d ≤ (crossViableReactions Sx.2 Sx.1 x).card} ≤
      (toNNReal (σ (catalysisP n lambda)) : ENNReal) ^ (b * d) := by
  simpa only [freshRightTargetCavityWidth_eq_left_swap,
    crossPoolIter_swap] using
    (measure_freshLeftTargetCavityWidth_mem_and_good_le
      (foodLength := foodLength) (k := k) (b := b) (d := d)
      lambda T (P.2, P.1) x)

/-- A union bound over prospective targets converts the singleton estimate
into a block estimate.  Crucially, the cost is only the target-block size;
there is still no factor counting pruning histories or cavity states. -/
theorem measure_exists_freshLeftTargetCavityWidth_good_le
    {n foodLength k b d : Nat} (lambda : ℝ)
    (T W : Finset (Molecule n))
    (P : Finset (Molecule n) × Finset (Molecule n)) :
    ambientPiMeasure n lambda {ω |
      ∃ x ∈ W,
        x ∈ freshLeftTargetCavityWidth (foodLength := foodLength)
          (fun y r => ω (y, r)) T P k ∧
        let Sx := crossPoolIter foodLength
          (closeTargetBlocks (fun y r => ω (y, r)) (T ∪ {x})) P k
        b ≤ Sx.2.card ∧
          d ≤ (crossViableReactions Sx.1 Sx.2 x).card} ≤
      (W.card : ENNReal) *
        (toNNReal (σ (catalysisP n lambda)) : ENNReal) ^ (b * d) := by
  classical
  let E := fun x : Molecule n => {ω : AmbientCoord n → Prop |
    x ∈ freshLeftTargetCavityWidth (foodLength := foodLength)
      (fun y r => ω (y, r)) T P k ∧
    let Sx := crossPoolIter foodLength
      (closeTargetBlocks (fun y r => ω (y, r)) (T ∪ {x})) P k
    b ≤ Sx.2.card ∧
      d ≤ (crossViableReactions Sx.1 Sx.2 x).card}
  rw [show {ω : AmbientCoord n → Prop |
      ∃ x ∈ W,
        x ∈ freshLeftTargetCavityWidth (foodLength := foodLength)
          (fun y r => ω (y, r)) T P k ∧
        let Sx := crossPoolIter foodLength
          (closeTargetBlocks (fun y r => ω (y, r)) (T ∪ {x})) P k
        b ≤ Sx.2.card ∧
          d ≤ (crossViableReactions Sx.1 Sx.2 x).card} =
      ⋃ x ∈ W, E x by
    ext ω
    constructor
    · rintro ⟨x, hxW, hxE⟩
      apply Set.mem_iUnion.mpr
      refine ⟨x, ?_⟩
      apply Set.mem_iUnion.mpr
      exact ⟨hxW, hxE⟩
    · intro hω
      rcases Set.mem_iUnion.mp hω with ⟨x, hω⟩
      rcases Set.mem_iUnion.mp hω with ⟨hxW, hxE⟩
      exact ⟨x, hxW, hxE⟩]
  calc
    ambientPiMeasure n lambda (⋃ x ∈ W, E x) ≤
        ∑ x ∈ W, ambientPiMeasure n lambda (E x) :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑ _x ∈ W,
        (toNNReal (σ (catalysisP n lambda)) : ENNReal) ^ (b * d) := by
      apply Finset.sum_le_sum
      intro x hx
      exact measure_freshLeftTargetCavityWidth_mem_and_good_le
        (foodLength := foodLength) (k := k) (b := b) (d := d)
        lambda T P x
    _ = (W.card : ENNReal) *
        (toNNReal (σ (catalysisP n lambda)) : ENNReal) ^ (b * d) := by
      simp

/-- Right-pool block form of the fresh-width estimate. -/
theorem measure_exists_freshRightTargetCavityWidth_good_le
    {n foodLength k b d : Nat} (lambda : ℝ)
    (T W : Finset (Molecule n))
    (P : Finset (Molecule n) × Finset (Molecule n)) :
    ambientPiMeasure n lambda {ω |
      ∃ x ∈ W,
        x ∈ freshRightTargetCavityWidth (foodLength := foodLength)
          (fun y r => ω (y, r)) T P k ∧
        let Sx := crossPoolIter foodLength
          (closeTargetBlocks (fun y r => ω (y, r)) (T ∪ {x})) P k
        b ≤ Sx.1.card ∧
          d ≤ (crossViableReactions Sx.2 Sx.1 x).card} ≤
      (W.card : ENNReal) *
        (toNNReal (σ (catalysisP n lambda)) : ENNReal) ^ (b * d) := by
  simpa only [freshRightTargetCavityWidth_eq_left_swap,
    crossPoolIter_swap] using
    (measure_exists_freshLeftTargetCavityWidth_good_le
      (foodLength := foodLength) (k := k) (b := b) (d := d)
      lambda T W (P.2, P.1))

end HordijkSteelThreshold
