import proofs.HordijkSteelThreshold.CavityWidthProbability
import proofs.HordijkSteelThreshold.TargetFamilyVariance

namespace HordijkSteelThreshold

open MeasureTheory ProbabilityTheory unitInterval
open RAF RAF.Polymer RAF.Concrete

/-- Restricting to a product-target block preserves a reaction-family event
when every reaction in the family has product in that block. -/
theorem catalystPoolFamilyOpen_from_targetBlock_iff
    {n : Nat} (ω : AmbientCoord n → Prop)
    (T C : Finset (Molecule n)) (R : Finset (Reaction n))
    (hprod : ∀ r ∈ R, reactionProduct r ∈ T) :
    catalystPoolFamilyOpen
        (fun z => catalysisFromTargetRestriction T (fun w => ω w) z.1 z.2)
        C R ↔
      catalystPoolFamilyOpen ω C R := by
  constructor
  · rintro ⟨r, hr, y, hy, hcat⟩
    have hcat' := (catalysisFromTargetRestriction_apply T
      (fun w => ω w) y r).mp hcat
    exact ⟨r, hr, y, hy, by simpa using hcat'.choose_spec⟩
  · rintro ⟨r, hr, y, hy, hcat⟩
    refine ⟨r, hr, y, hy, ?_⟩
    apply (catalysisFromTargetRestriction_apply T
      (fun w => ω w) y r).mpr
    exact ⟨hprod r hr, by simpa using hcat⟩

/-- A finite past may adaptively choose a catalyst pool, a target subset, and
pairwise-disjoint reaction families before a fresh product-target block is
read.  If the past is independent of that block, the fixed-state Chebyshev
lower tail survives adaptive mixing with no entropy factor. -/
theorem measure_adaptive_targetBlock_familyCount_le
    {n d K : Nat} (lambda : ℝ) (T : Finset (Molecule n))
    {α ι : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α]
    (X : (AmbientCoord n → Prop) → α)
    (hX : Measurable X)
    (hIndep : IndepFun X
      (fun (ω : AmbientCoord n → Prop)
        (z : catalystPoolTargetBlock
          (Finset.univ : Finset (Molecule n)) T) => ω z)
      (ambientPiMeasure n lambda))
    (C : α → Finset (Molecule n))
    (s : α → Finset ι)
    (R : α → ι → Finset (Reaction n))
    (hs : ∀ a, (s a).card ≤ K)
    (hR : ∀ a, Pairwise fun i j => Disjoint (R a i) (R a j))
    (hcard : ∀ a i, i ∈ s a → d ≤ (R a i).card)
    (hprod : ∀ a i, i ∈ s a → ∀ r ∈ R a i,
      reactionProduct r ∈ T)
    {c : ℝ} (hc : 0 < c) :
    ambientPiMeasure n lambda {ω |
      (∑ i ∈ s (X ω),
        catalystPoolFamilyIndicator (C (X ω)) (R (X ω) i) ω) ≤
      ((s (X ω)).card : ℝ) *
        (1 - (toNNReal (σ (catalysisP n lambda)) : ℝ) ^
          ((C (X ω)).card * d)) - c} ≤
      ENNReal.ofReal ((((K : Nat) : ℝ) / 4) / c ^ 2) := by
  classical
  let Block := catalystPoolTargetBlock
    (Finset.univ : Finset (Molecule n)) T → Prop
  let Y : (AmbientCoord n → Prop) → Block := fun ω z => ω z
  let H : α → Block → Prop := fun a v =>
    (∑ i ∈ s a, catalystPoolFamilyIndicator (C a) (R a i)
      (fun z => catalysisFromTargetRestriction T v z.1 z.2)) ≤
      ((s a).card : ℝ) *
        (1 - (toNNReal (σ (catalysisP n lambda)) : ℝ) ^
          ((C a).card * d)) - c
  have hsec : ∀ a, ambientPiMeasure n lambda {ω | H a (Y ω)} ≤
      ENNReal.ofReal ((((K : Nat) : ℝ) / 4) / c ^ 2) := by
    intro a
    have heq : {ω : AmbientCoord n → Prop | H a (Y ω)} =
        {ω | (∑ i ∈ s a,
          catalystPoolFamilyIndicator (C a) (R a i)) ω ≤
          ((s a).card : ℝ) *
            (1 - (toNNReal (σ (catalysisP n lambda)) : ℝ) ^
              ((C a).card * d)) - c} := by
      ext ω
      simp only [Set.mem_setOf_eq, H, Y, Block]
      have hsum :
          (∑ i ∈ s a, catalystPoolFamilyIndicator (C a) (R a i)
            (fun z => catalysisFromTargetRestriction T (fun z => ω z) z.1 z.2)) =
          (∑ i ∈ s a, catalystPoolFamilyIndicator (C a) (R a i)) ω := by
        rw [Finset.sum_apply]
        apply Finset.sum_congr rfl
        intro i hi
        simp only [catalystPoolFamilyIndicator]
        rw [catalystPoolFamilyOpen_from_targetBlock_iff]
        exact hprod a i hi
      rw [hsum]
    rw [heq]
    calc
      _ ≤ ENNReal.ofReal ((((s a).card : ℝ) / 4) / c ^ 2) :=
        measure_sum_catalystPoolFamilyIndicator_le_card_mul_one_sub_pow_sub
          lambda (C a) (s a) (R a) (hR a) (hcard a) hc
      _ ≤ ENNReal.ofReal ((((K : Nat) : ℝ) / 4) / c ^ 2) := by
        apply ENNReal.ofReal_le_ofReal
        apply div_le_div_of_nonneg_right
        · gcongr
          exact_mod_cast hs a
        · positivity
  have hadaptive := measure_adaptive_of_indep_finite hIndep hX H
    (fun _ => MeasurableSet.of_discrete) hsec
  refine (measure_mono ?_).trans hadaptive
  intro ω hω
  change H (X ω) (Y ω)
  simp only [H, Y, Block]
  have hsum :
      (∑ i ∈ s (X ω), catalystPoolFamilyIndicator (C (X ω)) (R (X ω) i)
        (fun z => catalysisFromTargetRestriction T (fun z => ω z) z.1 z.2)) =
      (∑ i ∈ s (X ω),
        catalystPoolFamilyIndicator (C (X ω)) (R (X ω) i)) ω := by
    rw [Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [catalystPoolFamilyIndicator]
    rw [catalystPoolFamilyOpen_from_targetBlock_iff]
    exact hprod (X ω) i hi
  rw [hsum]
  simpa only [Set.mem_setOf_eq, Finset.sum_apply] using hω

/-- A directly usable deferred-decision form of
`measure_adaptive_targetBlock_familyCount_le`.  The adaptive state is an
arbitrary statistic of every product-target coordinate outside `T`; hence its
independence from the fresh `T` block is automatic. -/
theorem measure_complementAdaptive_targetBlock_familyCount_le
    {n d K : Nat} (lambda : ℝ) (T : Finset (Molecule n))
    {α ι : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α]
    (f : (catalystPoolTargetBlock
      (Finset.univ : Finset (Molecule n))
        ((Finset.univ : Finset (Molecule n)) \ T) → Prop) → α)
    (hf : Measurable f)
    (C : α → Finset (Molecule n))
    (s : α → Finset ι)
    (R : α → ι → Finset (Reaction n))
    (hs : ∀ a, (s a).card ≤ K)
    (hR : ∀ a, Pairwise fun i j => Disjoint (R a i) (R a j))
    (hcard : ∀ a i, i ∈ s a → d ≤ (R a i).card)
    (hprod : ∀ a i, i ∈ s a → ∀ r ∈ R a i,
      reactionProduct r ∈ T)
    {c : ℝ} (hc : 0 < c) :
    ambientPiMeasure n lambda {ω |
      let a := f (fun z : catalystPoolTargetBlock
        (Finset.univ : Finset (Molecule n))
          ((Finset.univ : Finset (Molecule n)) \ T) => ω z)
      (∑ i ∈ s a,
        catalystPoolFamilyIndicator (C a) (R a i) ω) ≤
      ((s a).card : ℝ) *
        (1 - (toNNReal (σ (catalysisP n lambda)) : ℝ) ^
          ((C a).card * d)) - c} ≤
      ENNReal.ofReal ((((K : Nat) : ℝ) / 4) / c ^ 2) := by
  classical
  let V : Finset (Molecule n) :=
    (Finset.univ : Finset (Molecule n)) \ T
  let X : (AmbientCoord n → Prop) → α := fun ω =>
    f (fun z : catalystPoolTargetBlock
      (Finset.univ : Finset (Molecule n)) V => ω z)
  have hVT : Disjoint V T := by
    simp [V, Finset.disjoint_left]
  have hIndep : IndepFun X
      (fun (ω : AmbientCoord n → Prop)
        (z : catalystPoolTargetBlock
          (Finset.univ : Finset (Molecule n)) T) => ω z)
      (ambientPiMeasure n lambda) := by
    simpa [X, V, Function.comp_apply] using
      (catalystPoolTarget_statistics_indep lambda
        (Finset.univ : Finset (Molecule n)) hVT f (fun v => v)
        hf measurable_id)
  simpa only [X, V] using
    (measure_adaptive_targetBlock_familyCount_le lambda T X
      (measurable_of_finite _) hIndep C s R hs hR hcard hprod hc)

/-- Sharp adaptive mixture retaining the closed-family probability.  A
uniform catalyst-pool floor `b` turns the section variance into
`K q^(b*d)`, which is the asymptotically vanishing cost needed at fixed lower
layers. -/
theorem measure_adaptive_targetBlock_familyCount_le_sharp
    {n d K b : Nat} (lambda : ℝ) (T : Finset (Molecule n))
    {α ι : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α]
    (X : (AmbientCoord n → Prop) → α)
    (hX : Measurable X)
    (hIndep : IndepFun X
      (fun (ω : AmbientCoord n → Prop)
        (z : catalystPoolTargetBlock
          (Finset.univ : Finset (Molecule n)) T) => ω z)
      (ambientPiMeasure n lambda))
    (C : α → Finset (Molecule n))
    (s : α → Finset ι)
    (R : α → ι → Finset (Reaction n))
    (hs : ∀ a, (s a).card ≤ K)
    (hb : ∀ a, b ≤ (C a).card)
    (hR : ∀ a, Pairwise fun i j => Disjoint (R a i) (R a j))
    (hcard : ∀ a i, i ∈ s a → d ≤ (R a i).card)
    (hprod : ∀ a i, i ∈ s a → ∀ r ∈ R a i,
      reactionProduct r ∈ T)
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
  let Block := catalystPoolTargetBlock
    (Finset.univ : Finset (Molecule n)) T → Prop
  let Y : (AmbientCoord n → Prop) → Block := fun ω z => ω z
  let H : α → Block → Prop := fun a v =>
    (∑ i ∈ s a, catalystPoolFamilyIndicator (C a) (R a i)
      (fun z => catalysisFromTargetRestriction T v z.1 z.2)) ≤
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
          catalystPoolFamilyIndicator (C a) (R a i)) ω ≤
          ((s a).card : ℝ) *
            (1 - (toNNReal (σ (catalysisP n lambda)) : ℝ) ^
              ((C a).card * d)) - c} := by
      ext ω
      simp only [Set.mem_setOf_eq, H, Y, Block]
      have hsum :
          (∑ i ∈ s a, catalystPoolFamilyIndicator (C a) (R a i)
            (fun z => catalysisFromTargetRestriction T (fun z => ω z) z.1 z.2)) =
          (∑ i ∈ s a, catalystPoolFamilyIndicator (C a) (R a i)) ω := by
        rw [Finset.sum_apply]
        apply Finset.sum_congr rfl
        intro i hi
        simp only [catalystPoolFamilyIndicator]
        rw [catalystPoolFamilyOpen_from_targetBlock_iff]
        exact hprod a i hi
      rw [hsum]
    rw [heq]
    refine (measure_sum_catalystPoolFamilyIndicator_le_card_mul_one_sub_pow_sub_sharp
      lambda (C a) (s a) (R a) (hR a) (hcard a) hc).trans ?_
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
  simp only [H, Y, Block]
  have hsum :
      (∑ i ∈ s (X ω), catalystPoolFamilyIndicator (C (X ω)) (R (X ω) i)
        (fun z => catalysisFromTargetRestriction T (fun z => ω z) z.1 z.2)) =
      (∑ i ∈ s (X ω),
        catalystPoolFamilyIndicator (C (X ω)) (R (X ω) i)) ω := by
    rw [Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [catalystPoolFamilyIndicator]
    rw [catalystPoolFamilyOpen_from_targetBlock_iff]
    exact hprod (X ω) i hi
  rw [hsum]
  simpa only [Set.mem_setOf_eq, Finset.sum_apply] using hω

/-- Conditional sharp adaptive mixture.  Unlike the uniform-floor version,
this theorem charges only states whose selected catalyst pool actually has
size at least `b`; states below the floor make the event false.  This is the
usable interface at a first profile exit. -/
theorem measure_adaptive_targetBlock_familyCount_and_poolFloor_le_sharp
    {n d K b : Nat} (lambda : ℝ) (T : Finset (Molecule n))
    {α ι : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α]
    (X : (AmbientCoord n → Prop) → α)
    (hX : Measurable X)
    (hIndep : IndepFun X
      (fun (ω : AmbientCoord n → Prop)
        (z : catalystPoolTargetBlock
          (Finset.univ : Finset (Molecule n)) T) => ω z)
      (ambientPiMeasure n lambda))
    (C : α → Finset (Molecule n))
    (s : α → Finset ι)
    (R : α → ι → Finset (Reaction n))
    (hs : ∀ a, (s a).card ≤ K)
    (hR : ∀ a, Pairwise fun i j => Disjoint (R a i) (R a j))
    (hcard : ∀ a i, i ∈ s a → d ≤ (R a i).card)
    (hprod : ∀ a i, i ∈ s a → ∀ r ∈ R a i,
      reactionProduct r ∈ T)
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
  let Block := catalystPoolTargetBlock
    (Finset.univ : Finset (Molecule n)) T → Prop
  let Y : (AmbientCoord n → Prop) → Block := fun ω z => ω z
  let H : α → Block → Prop := fun a v =>
    b ≤ (C a).card ∧
    (∑ i ∈ s a, catalystPoolFamilyIndicator (C a) (R a i)
      (fun z => catalysisFromTargetRestriction T v z.1 z.2)) ≤
      ((s a).card : ℝ) *
        (1 - (toNNReal (σ (catalysisP n lambda)) : ℝ) ^
          ((C a).card * d)) - c
  have hsec : ∀ a, ambientPiMeasure n lambda {ω | H a (Y ω)} ≤
      ENNReal.ofReal ((((K : Nat) : ℝ) *
        (toNNReal (σ (catalysisP n lambda)) : ℝ) ^ (b * d)) /
          c ^ 2) := by
    intro a
    by_cases hb : b ≤ (C a).card
    · have heq : {ω : AmbientCoord n → Prop | H a (Y ω)} =
          {ω | (∑ i ∈ s a,
            catalystPoolFamilyIndicator (C a) (R a i)) ω ≤
            ((s a).card : ℝ) *
              (1 - (toNNReal (σ (catalysisP n lambda)) : ℝ) ^
                ((C a).card * d)) - c} := by
        ext ω
        simp only [Set.mem_setOf_eq, H, Y, Block, hb, true_and]
        have hsum :
            (∑ i ∈ s a, catalystPoolFamilyIndicator (C a) (R a i)
              (fun z => catalysisFromTargetRestriction T
                (fun z => ω z) z.1 z.2)) =
            (∑ i ∈ s a,
              catalystPoolFamilyIndicator (C a) (R a i)) ω := by
          rw [Finset.sum_apply]
          apply Finset.sum_congr rfl
          intro i hi
          simp only [catalystPoolFamilyIndicator]
          rw [catalystPoolFamilyOpen_from_targetBlock_iff]
          exact hprod a i hi
        rw [hsum]
      rw [heq]
      refine (measure_sum_catalystPoolFamilyIndicator_le_card_mul_one_sub_pow_sub_sharp
        lambda (C a) (s a) (R a) (hR a) (hcard a) hc).trans ?_
      apply ENNReal.ofReal_le_ofReal
      apply div_le_div_of_nonneg_right
      · apply mul_le_mul
        · exact_mod_cast hs a
        · apply pow_le_pow_of_le_one
          · positivity
          · simpa using (σ (catalysisP n lambda)).2.2
          · exact Nat.mul_le_mul_right d hb
        · positivity
        · positivity
      · exact sq_nonneg c
    · simp [H, hb]
  have hadaptive := measure_adaptive_of_indep_finite hIndep hX H
    (fun _ => MeasurableSet.of_discrete) hsec
  refine (measure_mono ?_).trans hadaptive
  intro ω hω
  change H (X ω) (Y ω)
  refine ⟨hω.1, ?_⟩
  simp only [Y, Block]
  have hsum :
      (∑ i ∈ s (X ω), catalystPoolFamilyIndicator (C (X ω)) (R (X ω) i)
        (fun z => catalysisFromTargetRestriction T (fun z => ω z) z.1 z.2)) =
      (∑ i ∈ s (X ω),
        catalystPoolFamilyIndicator (C (X ω)) (R (X ω) i)) ω := by
    rw [Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [catalystPoolFamilyIndicator]
    rw [catalystPoolFamilyOpen_from_targetBlock_iff]
    exact hprod (X ω) i hi
  rw [hsum]
  simpa only [Finset.sum_apply] using hω.2

/-- Complement-restriction form of the conditional sharp mixture. -/
theorem measure_complementAdaptive_targetBlock_familyCount_and_poolFloor_le_sharp
    {n d K b : Nat} (lambda : ℝ) (T : Finset (Molecule n))
    {α ι : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α]
    (f : (catalystPoolTargetBlock
      (Finset.univ : Finset (Molecule n))
        ((Finset.univ : Finset (Molecule n)) \ T) → Prop) → α)
    (hf : Measurable f)
    (C : α → Finset (Molecule n))
    (s : α → Finset ι)
    (R : α → ι → Finset (Reaction n))
    (hs : ∀ a, (s a).card ≤ K)
    (hR : ∀ a, Pairwise fun i j => Disjoint (R a i) (R a j))
    (hcard : ∀ a i, i ∈ s a → d ≤ (R a i).card)
    (hprod : ∀ a i, i ∈ s a → ∀ r ∈ R a i,
      reactionProduct r ∈ T)
    {c : ℝ} (hc : 0 < c) :
    ambientPiMeasure n lambda {ω |
      let a := f (fun z : catalystPoolTargetBlock
        (Finset.univ : Finset (Molecule n))
          ((Finset.univ : Finset (Molecule n)) \ T) => ω z)
      b ≤ (C a).card ∧
      (∑ i ∈ s a,
        catalystPoolFamilyIndicator (C a) (R a i) ω) ≤
      ((s a).card : ℝ) *
        (1 - (toNNReal (σ (catalysisP n lambda)) : ℝ) ^
          ((C a).card * d)) - c} ≤
      ENNReal.ofReal ((((K : Nat) : ℝ) *
        (toNNReal (σ (catalysisP n lambda)) : ℝ) ^ (b * d)) /
          c ^ 2) := by
  classical
  let V : Finset (Molecule n) :=
    (Finset.univ : Finset (Molecule n)) \ T
  let X : (AmbientCoord n → Prop) → α := fun ω =>
    f (fun z : catalystPoolTargetBlock
      (Finset.univ : Finset (Molecule n)) V => ω z)
  have hVT : Disjoint V T := by
    simp [V, Finset.disjoint_left]
  have hIndep : IndepFun X
      (fun (ω : AmbientCoord n → Prop)
        (z : catalystPoolTargetBlock
          (Finset.univ : Finset (Molecule n)) T) => ω z)
      (ambientPiMeasure n lambda) := by
    simpa [X, V, Function.comp_apply] using
      (catalystPoolTarget_statistics_indep lambda
        (Finset.univ : Finset (Molecule n)) hVT f (fun v => v)
        hf measurable_id)
  simpa only [X, V] using
    (measure_adaptive_targetBlock_familyCount_and_poolFloor_le_sharp
      lambda T X (measurable_of_finite _) hIndep C s R hs hR hcard hprod hc)

/-- Complement-restriction specialization of the sharp adaptive bound. -/
theorem measure_complementAdaptive_targetBlock_familyCount_le_sharp
    {n d K b : Nat} (lambda : ℝ) (T : Finset (Molecule n))
    {α ι : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α]
    (f : (catalystPoolTargetBlock
      (Finset.univ : Finset (Molecule n))
        ((Finset.univ : Finset (Molecule n)) \ T) → Prop) → α)
    (hf : Measurable f)
    (C : α → Finset (Molecule n))
    (s : α → Finset ι)
    (R : α → ι → Finset (Reaction n))
    (hs : ∀ a, (s a).card ≤ K)
    (hb : ∀ a, b ≤ (C a).card)
    (hR : ∀ a, Pairwise fun i j => Disjoint (R a i) (R a j))
    (hcard : ∀ a i, i ∈ s a → d ≤ (R a i).card)
    (hprod : ∀ a i, i ∈ s a → ∀ r ∈ R a i,
      reactionProduct r ∈ T)
    {c : ℝ} (hc : 0 < c) :
    ambientPiMeasure n lambda {ω |
      let a := f (fun z : catalystPoolTargetBlock
        (Finset.univ : Finset (Molecule n))
          ((Finset.univ : Finset (Molecule n)) \ T) => ω z)
      (∑ i ∈ s a,
        catalystPoolFamilyIndicator (C a) (R a i) ω) ≤
      ((s a).card : ℝ) *
        (1 - (toNNReal (σ (catalysisP n lambda)) : ℝ) ^
          ((C a).card * d)) - c} ≤
      ENNReal.ofReal ((((K : Nat) : ℝ) *
        (toNNReal (σ (catalysisP n lambda)) : ℝ) ^ (b * d)) /
          c ^ 2) := by
  classical
  let V : Finset (Molecule n) :=
    (Finset.univ : Finset (Molecule n)) \ T
  let X : (AmbientCoord n → Prop) → α := fun ω =>
    f (fun z : catalystPoolTargetBlock
      (Finset.univ : Finset (Molecule n)) V => ω z)
  have hVT : Disjoint V T := by
    simp [V, Finset.disjoint_left]
  have hIndep : IndepFun X
      (fun (ω : AmbientCoord n → Prop)
        (z : catalystPoolTargetBlock
          (Finset.univ : Finset (Molecule n)) T) => ω z)
      (ambientPiMeasure n lambda) := by
    simpa [X, V, Function.comp_apply] using
      (catalystPoolTarget_statistics_indep lambda
        (Finset.univ : Finset (Molecule n)) hVT f (fun v => v)
        hf measurable_id)
  simpa only [X, V] using
    (measure_adaptive_targetBlock_familyCount_le_sharp lambda T X
      (measurable_of_finite _) hIndep C s R hs hb hR hcard hprod hc)

end HordijkSteelThreshold
