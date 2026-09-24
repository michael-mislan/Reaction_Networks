import proofs.HordijkSteelThreshold.MarkedSplitReservoir
import proofs.HordijkSteelThreshold.TerminalMissingBarrier

namespace HordijkSteelThreshold

open MeasureTheory ProbabilityTheory unitInterval
open RAF RAF.Polymer RAF.Concrete

/-- Molecules with at least `k` available split positions.  This is exactly
the high band of molecule lengths at least `k+1`. -/
abbrev SplitEligibleMolecule (n k : Nat) :=
  {x : Molecule n // k ≤ x.1.val}

def eligibleReactionAt {n k : Nat} (x : SplitEligibleMolecule n k)
    (i : Fin k) : Reaction n :=
  reactionAtSplit x.1 ⟨i.val, i.2.trans_le x.2⟩

theorem eligibleReactionAt_injective {n k : Nat}
    (x : SplitEligibleMolecule n k) :
    Function.Injective (eligibleReactionAt x) := by
  intro i j hij
  apply Fin.ext
  exact congrArg (fun r : Reaction n => r.2.2.val) hij

/-- The first `k` target-local reactions for an arbitrary high-band molecule. -/
noncomputable def eligibleInitialSplitReactions {n k : Nat}
    (x : SplitEligibleMolecule n k) : Finset (Reaction n) := by
  classical
  exact Finset.univ.image (eligibleReactionAt x)

@[simp] theorem card_eligibleInitialSplitReactions {n k : Nat}
    (x : SplitEligibleMolecule n k) :
    (eligibleInitialSplitReactions x).card = k := by
  classical
  rw [eligibleInitialSplitReactions,
    Finset.card_image_of_injective _ (eligibleReactionAt_injective x)]
  simp

theorem reactionProduct_eligibleReactionAt {n k : Nat}
    (x : SplitEligibleMolecule n k) (i : Fin k) :
    reactionProduct (eligibleReactionAt x i) = x.1 := by
  rfl

theorem eligibleInitialSplitReactions_disjoint {n k : Nat}
    {x y : SplitEligibleMolecule n k} (hxy : x ≠ y) :
    Disjoint (eligibleInitialSplitReactions x)
      (eligibleInitialSplitReactions y) := by
  classical
  rw [Finset.disjoint_left]
  intro r hrx hry
  obtain ⟨i, hi, hir⟩ := Finset.mem_image.mp hrx
  obtain ⟨j, hj, hjr⟩ := Finset.mem_image.mp hry
  have hprod := congrArg reactionProduct (hir.trans hjr.symm)
  apply hxy
  apply Subtype.ext
  simpa [reactionProduct_eligibleReactionAt] using hprod

/-- Viable support reactions after discarding a high-band target's reserved
label coordinates. -/
noncomputable def eligibleUnreservedCrossViableReactions {n k : Nat}
    (A B : Finset (Molecule n)) (x : SplitEligibleMolecule n k) :
    Finset (Reaction n) :=
  crossViableReactions A B x.1 \ eligibleInitialSplitReactions x

noncomputable def eligibleInitialSplitReactionUnion {n k : Nat}
    (E : Finset (SplitEligibleMolecule n k)) : Finset (Reaction n) :=
  E.biUnion eligibleInitialSplitReactions

noncomputable def eligibleUnreservedReactionUnion {n k : Nat}
    (A B : Finset (Molecule n))
    (E : Finset (SplitEligibleMolecule n k)) : Finset (Reaction n) :=
  E.biUnion (eligibleUnreservedCrossViableReactions A B)

/-- Global reaction-coordinate separation for two arbitrary high-band target
sets.  Different targets are separated by product and equal targets by the
set difference. -/
theorem eligibleInitialSplitReactionUnion_disjoint_unreservedUnion
    {n k : Nat} (A B : Finset (Molecule n))
    (E F : Finset (SplitEligibleMolecule n k)) :
    Disjoint (eligibleInitialSplitReactionUnion E)
      (eligibleUnreservedReactionUnion A B F) := by
  classical
  rw [Finset.disjoint_left]
  intro r hrReserved hrSupport
  obtain ⟨x, hxE, hrx⟩ := Finset.mem_biUnion.mp hrReserved
  obtain ⟨y, hyF, hry⟩ := Finset.mem_biUnion.mp hrSupport
  obtain ⟨i, hi, hir⟩ := Finset.mem_image.mp hrx
  have hprodReserved : reactionProduct r = x.1 := by
    rw [← hir]
    rfl
  have hryCross : r ∈ crossViableReactions A B y.1 :=
    (Finset.mem_sdiff.mp hry).1
  have hprodSupport : reactionProduct r = y.1 :=
    (mem_crossViableReactions A B y.1 r).mp hryCross |>.1
  have hxy : x = y := by
    apply Subtype.ext
    exact hprodReserved.symm.trans hprodSupport
  subst y
  exact (Finset.mem_sdiff.mp hry).2 hrx

noncomputable def eligibleReservedMarkBlock {n k : Nat}
    (C : Finset (Molecule n))
    (E : Finset (SplitEligibleMolecule n k)) : Finset (AmbientCoord n) :=
  catalystPoolFamilyBlock C (eligibleInitialSplitReactionUnion E)

noncomputable def eligibleUnreservedSupportBlock {n k : Nat}
    (D A B : Finset (Molecule n))
    (E : Finset (SplitEligibleMolecule n k)) : Finset (AmbientCoord n) :=
  catalystPoolFamilyBlock D (eligibleUnreservedReactionUnion A B E)

theorem eligibleReservedMarkBlock_disjoint_unreservedSupportBlock
    {n k : Nat} (C D A B : Finset (Molecule n))
    (E F : Finset (SplitEligibleMolecule n k)) :
    Disjoint (eligibleReservedMarkBlock C E)
      (eligibleUnreservedSupportBlock D A B F) := by
  rw [Finset.disjoint_left]
  intro z hzReserved hzSupport
  exact Finset.disjoint_left.mp
    (eligibleInitialSplitReactionUnion_disjoint_unreservedUnion A B E F)
    (Finset.mem_product.mp hzReserved).2
    (Finset.mem_product.mp hzSupport).2

theorem eligibleReservedMarkField_indep_unreservedSupportField
    {n k : Nat} (lambda : ℝ) (C D A B : Finset (Molecule n))
    (E F : Finset (SplitEligibleMolecule n k)) :
    IndepFun
      (fun (ω : AmbientCoord n → Prop)
        (z : eligibleReservedMarkBlock C E) => ω z)
      (fun (ω : AmbientCoord n → Prop)
        (z : eligibleUnreservedSupportBlock D A B F) => ω z)
      (ambientPiMeasure n lambda) := by
  exact (ambientCoordinate_iIndep n lambda).indepFun_finset
    (eligibleReservedMarkBlock C E)
    (eligibleUnreservedSupportBlock D A B F)
    (eligibleReservedMarkBlock_disjoint_unreservedSupportBlock C D A B E F)
    (fun _ => measurable_pi_apply _)

local instance eligibleSetMeasurableSpace (n k : Nat) :
    MeasurableSpace (Finset (SplitEligibleMolecule n k)) := ⊤

noncomputable def eligibleMarkedSet {n k : Nat}
    (C : Finset (Molecule n)) (E : Finset (SplitEligibleMolecule n k))
    (ω : AmbientCoord n → Prop) : Finset (SplitEligibleMolecule n k) := by
  classical
  exact E.filter fun x => catalystPoolFamilyOpen ω C
    (eligibleInitialSplitReactions x)

noncomputable def eligibleMarkedSetFromField {n k : Nat}
    (C : Finset (Molecule n)) (E : Finset (SplitEligibleMolecule n k))
    (v : eligibleReservedMarkBlock C E → Prop) :
    Finset (SplitEligibleMolecule n k) := by
  classical
  exact E.filter fun x => ∃ z : eligibleReservedMarkBlock C E,
    z.1.2 ∈ eligibleInitialSplitReactions x ∧ v z

theorem eligibleMarkedSet_eq_fromField {n k : Nat}
    (C : Finset (Molecule n)) (E : Finset (SplitEligibleMolecule n k))
    (ω : AmbientCoord n → Prop) :
    eligibleMarkedSet C E ω =
      eligibleMarkedSetFromField C E (fun z => ω z) := by
  classical
  ext x
  simp only [eligibleMarkedSet, eligibleMarkedSetFromField,
    Finset.mem_filter, and_congr_right_iff]
  intro hxE
  constructor
  · rintro ⟨r, hr, y, hy, hω⟩
    refine ⟨⟨(y, r), ?_⟩, hr, hω⟩
    show (y, r) ∈ C.product (eligibleInitialSplitReactionUnion E)
    exact Finset.mem_product.mpr
      ⟨hy, Finset.mem_biUnion.mpr ⟨x, hxE, hr⟩⟩
  · rintro ⟨z, hr, hω⟩
    have hz := Finset.mem_product.mp z.property
    exact ⟨z.1.2, hr, z.1.1, hz.1, hω⟩

theorem eligibleMarkedSet_measurable {n k : Nat}
    (C : Finset (Molecule n)) (E : Finset (SplitEligibleMolecule n k)) :
    Measurable (eligibleMarkedSet C E) := measurable_of_finite _

theorem eligibleMarkedSet_indep_unreservedSupportField
    {n k : Nat} (lambda : ℝ) (C D A B : Finset (Molecule n))
    (E F : Finset (SplitEligibleMolecule n k)) :
    IndepFun (eligibleMarkedSet C E)
      (fun (ω : AmbientCoord n → Prop)
        (z : eligibleUnreservedSupportBlock D A B F) => ω z)
      (ambientPiMeasure n lambda) := by
  have hfield := eligibleReservedMarkField_indep_unreservedSupportField
    lambda C D A B E F
  have hcomp := hfield.comp
    (measurable_of_finite (eligibleMarkedSetFromField C E)) measurable_id
  have heq : eligibleMarkedSet C E =
      eligibleMarkedSetFromField C E ∘
        (fun (ω : AmbientCoord n → Prop)
          (z : eligibleReservedMarkBlock C E) => ω z) := by
    funext ω
    exact eligibleMarkedSet_eq_fromField C E ω
  rw [heq]
  simpa [Function.comp_apply] using hcomp

noncomputable def eligibleMoleculeValues {n k : Nat}
    (E : Finset (SplitEligibleMolecule n k)) : Finset (Molecule n) :=
  E.image Subtype.val

@[simp] theorem card_eligibleMoleculeValues {n k : Nat}
    (E : Finset (SplitEligibleMolecule n k)) :
    (eligibleMoleculeValues E).card = E.card := by
  classical
  exact Finset.card_image_of_injective E Subtype.val_injective

/-- Conditional sharp support barrier for the entire marked high band. -/
theorem measure_eligibleMarkedGoodSupportCount_and_poolFloor_le_sharp
    {n k d b : Nat} (lambda : ℝ) (Cmark A B : Finset (Molecule n))
    (E : Finset (SplitEligibleMolecule n k)) {c : ℝ} (hc : 0 < c) :
    ambientPiMeasure n lambda {ω |
      let M := eligibleMarkedSet Cmark E ω
      let ME := M ∩ E
      let G := ME.filter fun x => d ≤
        (eligibleUnreservedCrossViableReactions A B x).card
      b ≤ (eligibleMoleculeValues ME).card ∧
      (∑ x ∈ G, catalystPoolFamilyIndicator
        (eligibleMoleculeValues ME)
        (eligibleUnreservedCrossViableReactions A B x) ω) ≤
      (G.card : ℝ) *
        (1 - (toNNReal (σ (catalysisP n lambda)) : ℝ) ^
          ((eligibleMoleculeValues ME).card * d)) - c} ≤
      ENNReal.ofReal ((((E.card : Nat) : ℝ) *
        (toNNReal (σ (catalysisP n lambda)) : ℝ) ^ (b * d)) /
          c ^ 2) := by
  classical
  let State := Finset (SplitEligibleMolecule n k)
  let X : (AmbientCoord n → Prop) → State := eligibleMarkedSet Cmark E
  let S : Finset (AmbientCoord n) := eligibleUnreservedSupportBlock
    (Finset.univ : Finset (Molecule n)) A B E
  let Cstate : State → Finset (Molecule n) := fun M =>
    eligibleMoleculeValues (M ∩ E)
  let sstate : State → Finset (SplitEligibleMolecule n k) := fun M =>
    (M ∩ E).filter fun x => d ≤
      (eligibleUnreservedCrossViableReactions A B x).card
  let Rstate : State → SplitEligibleMolecule n k → Finset (Reaction n) :=
    fun _ x => eligibleUnreservedCrossViableReactions A B x
  have hs : ∀ M, (sstate M).card ≤ E.card := by
    intro M
    apply Finset.card_le_card
    intro x hx
    exact Finset.inter_subset_right (Finset.mem_filter.mp hx).1
  have hR : ∀ M, Pairwise fun x y =>
      Disjoint (Rstate M x) (Rstate M y) := by
    intro M x y hxy
    rw [Finset.disjoint_left]
    intro r hrx hry
    have hxyVal : x.1 ≠ y.1 := fun h => hxy (Subtype.ext h)
    exact Finset.disjoint_left.mp
      (crossViableReactions_disjoint A B hxyVal)
      (Finset.mem_sdiff.mp hrx).1 (Finset.mem_sdiff.mp hry).1
  have hcard : ∀ M x, x ∈ sstate M →
      d ≤ (Rstate M x).card := by
    intro M x hx
    exact (Finset.mem_filter.mp hx).2
  have hblock : ∀ M x, x ∈ sstate M →
      catalystPoolFamilyBlock (Cstate M) (Rstate M x) ⊆ S := by
    intro M x hx z hz
    have hzprod := Finset.mem_product.mp hz
    have hxE : x ∈ E :=
      Finset.inter_subset_right (Finset.mem_filter.mp hx).1
    show z ∈ (Finset.univ : Finset (Molecule n)).product
      (eligibleUnreservedReactionUnion A B E)
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _,
      Finset.mem_biUnion.mpr ⟨x, hxE, hzprod.2⟩⟩
  have hIndep : IndepFun X
      (fun (ω : AmbientCoord n → Prop) (z : S) => ω z)
      (ambientPiMeasure n lambda) := by
    simpa only [X, S] using
      (eligibleMarkedSet_indep_unreservedSupportField lambda Cmark
        (Finset.univ : Finset (Molecule n)) A B E E)
  have htail :=
    measure_adaptive_finiteBlock_familyCount_and_poolFloor_le_sharp
      (n := n) (d := d) (K := E.card) (b := b) lambda S X
      (eligibleMarkedSet_measurable Cmark E) hIndep
      Cstate sstate Rstate hs hR hcard hblock hc
  simpa only [State, X, S, Cstate, sstate, Rstate] using htail

/-- Close an auxiliary reaction set after it has served to generate labels. -/
def closeReactionSet {n : Nat}
    (Cat : Catalysis (Molecule n) (Reaction n))
    (R0 : Finset (Reaction n)) : Catalysis (Molecule n) (Reaction n) :=
  fun y r => r ∉ R0 ∧ Cat y r

/-- With a fixed set of reaction labels disabled, a target cavity still depends
only on coordinates outside that target-product block. -/
theorem reservedPreclosedTargetIter_statistics_indep
    {n foodLength iter : Nat} (lambda : ℝ)
    (R0 : Finset (Reaction n)) (U : Finset (Molecule n))
    (P : Finset (Molecule n) × Finset (Molecule n))
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (f : (Finset (Molecule n) × Finset (Molecule n)) → α)
    (g : (catalystPoolTargetBlock
      (Finset.univ : Finset (Molecule n)) U → Prop) → β)
    (hf : Measurable (fun v => f (crossPoolIter foodLength
      (closeReactionSet
        (catalysisFromTargetRestriction
          ((Finset.univ : Finset (Molecule n)) \ U) v) R0) P iter)))
    (hg : Measurable g) :
    IndepFun
      (fun (ω : AmbientCoord n → Prop) =>
        f (crossPoolIter foodLength
          (closeTargetBlocks
            (closeReactionSet (fun y r => ω (y, r)) R0) U) P iter))
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
      (closeReactionSet (catalysisFromTargetRestriction V v) R0) P iter))
    g hf hg
  have hclose (ω : AmbientCoord n → Prop) :
      closeTargetBlocks
          (closeReactionSet (fun y r => ω (y, r)) R0) U =
        closeReactionSet
          (catalysisFromTargetRestriction
            ((Finset.univ : Finset (Molecule n)) \ U) (fun z => ω z)) R0 := by
    funext y r
    simp only [closeTargetBlocks, closeReactionSet]
    by_cases hrU : reactionProduct r ∈ U
    · simp [hrU, catalysisFromTargetRestriction]
    · simp [hrU, catalysisFromTargetRestriction]
  simpa only [V, Function.comp_apply, hclose] using hind

/-- Uniform section bounds survive a target cavity when an additional fixed
set of reserved label reactions is disabled throughout the pruning state. -/
theorem measure_adaptive_reservedPreclosedTargetIter_le
    {n foodLength iter : Nat} (lambda : ℝ)
    (R0 : Finset (Reaction n)) (U : Finset (Molecule n))
    (P : Finset (Molecule n) × Finset (Molecule n))
    (H : (Finset (Molecule n) × Finset (Molecule n)) →
      (catalystPoolTargetBlock
        (Finset.univ : Finset (Molecule n)) U → Prop) → Prop)
    (hH : ∀ S, MeasurableSet {v | H S v}) {p : ENNReal}
    (hsec : ∀ S,
      ambientPiMeasure n lambda {ω | H S (fun z => ω z)} ≤ p) :
    ambientPiMeasure n lambda {ω |
      H (crossPoolIter foodLength
          (closeTargetBlocks
            (closeReactionSet (fun y r => ω (y, r)) R0) U) P iter)
        (fun z => ω z)} ≤ p := by
  let State := Finset (Molecule n) × Finset (Molecule n)
  letI : MeasurableSpace State := ⊤
  let X : (AmbientCoord n → Prop) → State := fun ω =>
    crossPoolIter foodLength
      (closeTargetBlocks
        (closeReactionSet (fun y r => ω (y, r)) R0) U) P iter
  let Y : (AmbientCoord n → Prop) →
      (catalystPoolTargetBlock
        (Finset.univ : Finset (Molecule n)) U → Prop) :=
    fun ω z => ω z
  have hind : IndepFun X Y (ambientPiMeasure n lambda) := by
    simpa [X, Y, State] using reservedPreclosedTargetIter_statistics_indep
      lambda R0 U P (fun S => S) (fun v => v)
      (measurable_of_finite _) measurable_id
  exact measure_adaptive_of_indep_finite hind (measurable_of_finite _) H hH hsec

theorem card_biUnion_eligibleUnreservedCrossViableReactions_ge
    {n k d : Nat} (A B : Finset (Molecule n))
    (U : Finset (SplitEligibleMolecule n k))
    (hcard : ∀ x ∈ U,
      d ≤ (eligibleUnreservedCrossViableReactions A B x).card) :
    d * U.card ≤
      (U.biUnion (eligibleUnreservedCrossViableReactions A B)).card := by
  classical
  have hpair : (U : Set (SplitEligibleMolecule n k)).PairwiseDisjoint
      (eligibleUnreservedCrossViableReactions A B) := by
    intro x hx y hy hxy
    have hval : x.1 ≠ y.1 := by
      intro h
      exact hxy (Subtype.ext h)
    exact (crossViableReactions_disjoint A B hval).mono
      Finset.sdiff_subset Finset.sdiff_subset
  rw [Finset.card_biUnion hpair]
  calc
    d * U.card = ∑ x ∈ U, d := by simp [Nat.mul_comm]
    _ ≤ ∑ x ∈ U,
        (eligibleUnreservedCrossViableReactions A B x).card := by
      exact Finset.sum_le_sum fun x hx => hcard x hx

theorem catalystPoolFamiliesClosed_eligible_restriction_iff
    {n k : Nat} (ω : AmbientCoord n → Prop)
    (U : Finset (SplitEligibleMolecule n k))
    (C : Finset (Molecule n))
    (R : SplitEligibleMolecule n k → Finset (Reaction n))
    (hprod : ∀ x ∈ U, ∀ r ∈ R x, reactionProduct r = x.1) :
    catalystPoolFamiliesClosed
        (fun z => catalysisFromTargetRestriction (eligibleMoleculeValues U)
          (fun w => ω w) z.1 z.2) C U R ↔
      catalystPoolFamiliesClosed ω C U R := by
  constructor
  · intro hclosed x hx hopen
    apply hclosed x hx
    rw [catalystPoolFamilyOpen_target_restriction_iff ω
      (eligibleMoleculeValues U) C x.1]
    · exact hopen
    · exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
    · exact hprod x hx
  · intro hclosed x hx hopen
    apply hclosed x hx
    rw [← catalystPoolFamilyOpen_target_restriction_iff ω
      (eligibleMoleculeValues U) C x.1]
    · exact hopen
    · exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
    · exact hprod x hx

/-- A fixed eligible target batch in a pruning cavity with reserved labels
disabled pays the complete unreserved family-closure energy. -/
theorem measure_adaptive_reservedPreclosed_eligibleFamiliesClosed_le
    {n k foodLength iter b d : Nat} (lambda : ℝ)
    (R0 : Finset (Reaction n))
    (U : Finset (SplitEligibleMolecule n k))
    (P : Finset (Molecule n) × Finset (Molecule n)) :
    ambientPiMeasure n lambda {ω |
      let S := crossPoolIter foodLength
        (closeTargetBlocks
          (closeReactionSet (fun y r => ω (y, r)) R0)
          (eligibleMoleculeValues U)) P iter
      b ≤ S.2.card ∧
        (∀ x ∈ U, d ≤
          (eligibleUnreservedCrossViableReactions S.1 S.2 x).card) ∧
        catalystPoolFamiliesClosed ω S.2 U
          (eligibleUnreservedCrossViableReactions S.1 S.2)} ≤
      (toNNReal (σ (catalysisP n lambda)) : ENNReal) ^
        (b * (d * U.card)) := by
  classical
  let H := fun (S : Finset (Molecule n) × Finset (Molecule n))
      (v : catalystPoolTargetBlock
        (Finset.univ : Finset (Molecule n))
          (eligibleMoleculeValues U) → Prop) =>
    b ≤ S.2.card ∧
      (∀ x ∈ U, d ≤
        (eligibleUnreservedCrossViableReactions S.1 S.2 x).card) ∧
      catalystPoolFamiliesClosed
        (fun z => catalysisFromTargetRestriction (eligibleMoleculeValues U)
          v z.1 z.2) S.2 U
        (eligibleUnreservedCrossViableReactions S.1 S.2)
  have hsec : ∀ S,
      ambientPiMeasure n lambda {ω | H S (fun z => ω z)} ≤
        (toNNReal (σ (catalysisP n lambda)) : ENNReal) ^
          (b * (d * U.card)) := by
    intro S
    by_cases hbS : b ≤ S.2.card
    · by_cases hdS : ∀ x ∈ U, d ≤
          (eligibleUnreservedCrossViableReactions S.1 S.2 x).card
      · have hevent : {ω : AmbientCoord n → Prop | H S (fun z => ω z)} =
            {ω | catalystPoolFamiliesClosed ω S.2 U
              (eligibleUnreservedCrossViableReactions S.1 S.2)} := by
          ext ω
          simp only [Set.mem_setOf_eq, H, hbS, true_and]
          have hrestr := catalystPoolFamiliesClosed_eligible_restriction_iff
            ω U S.2 (eligibleUnreservedCrossViableReactions S.1 S.2)
            (fun x hx r hr =>
              (mem_crossViableReactions S.1 S.2 x.1 r).mp
                (Finset.mem_sdiff.mp hr).1 |>.1)
          rw [hrestr]
          exact and_iff_right hdS
        rw [hevent, measure_catalystPoolFamiliesClosed]
        apply pow_le_pow_right_of_le_one'
        · exact_mod_cast (σ (catalysisP n lambda)).2.2
        · apply Nat.mul_le_mul hbS
          exact card_biUnion_eligibleUnreservedCrossViableReactions_ge
            S.1 S.2 U hdS
      · rw [show {ω : AmbientCoord n → Prop | H S (fun z => ω z)} = ∅ by
          ext ω
          change (H S (fun z => ω z) ↔ False)
          constructor
          · intro h
            exact (hdS h.2.1).elim
          · intro h
            exact h.elim]
        simp
    · simp [H, hbS]
  have hadaptive := measure_adaptive_reservedPreclosedTargetIter_le
    (foodLength := foodLength) (iter := iter)
    lambda R0 (eligibleMoleculeValues U) P H
    (fun _ => (Set.toFinite _).measurableSet) hsec
  rw [show {ω : AmbientCoord n → Prop |
      let S := crossPoolIter foodLength
        (closeTargetBlocks
          (closeReactionSet (fun y r => ω (y, r)) R0)
          (eligibleMoleculeValues U)) P iter
      b ≤ S.2.card ∧
        (∀ x ∈ U, d ≤
          (eligibleUnreservedCrossViableReactions S.1 S.2 x).card) ∧
        catalystPoolFamiliesClosed ω S.2 U
          (eligibleUnreservedCrossViableReactions S.1 S.2)} =
      {ω | H (crossPoolIter foodLength
          (closeTargetBlocks
            (closeReactionSet (fun y r => ω (y, r)) R0)
            (eligibleMoleculeValues U)) P iter) (fun z => ω z)} by
    ext ω
    simp only [Set.mem_setOf_eq, H]
    let S := crossPoolIter foodLength
      (closeTargetBlocks
        (closeReactionSet (fun y r => ω (y, r)) R0)
        (eligibleMoleculeValues U)) P iter
    have hrestr := catalystPoolFamiliesClosed_eligible_restriction_iff
      ω U S.2 (eligibleUnreservedCrossViableReactions S.1 S.2)
      (fun x hx r hr =>
        (mem_crossViableReactions S.1 S.2 x.1 r).mp
          (Finset.mem_sdiff.mp hr).1 |>.1)
    rw [hrestr]]
  exact hadaptive

/-- At a stabilized pruning core that ignores all reserved band reactions,
every absent eligible target has its entire unreserved viable family closed
against the terminal catalyst pool. -/
theorem terminal_absent_eligibleUnreservedFamilyClosed
    {n k foodLength iter : Nat}
    (ω : AmbientCoord n → Prop)
    (E : Finset (SplitEligibleMolecule n k))
    (A0 : Finset (Molecule n))
    (hfix : crossPoolIter foodLength
      (closeReactionSet (fun y r => ω (y, r))
        (eligibleInitialSplitReactionUnion E)) (A0, A0) (iter + 1) =
      crossPoolIter foodLength
        (closeReactionSet (fun y r => ω (y, r))
          (eligibleInitialSplitReactionUnion E)) (A0, A0) iter)
    {x : SplitEligibleMolecule n k} (hxA : x.1 ∈ A0)
    (hxAbsent : x.1 ∉ (crossPoolIter foodLength
      (closeReactionSet (fun y r => ω (y, r))
        (eligibleInitialSplitReactionUnion E)) (A0, A0) iter).1) :
    ¬ catalystPoolFamilyOpen ω
      (crossPoolIter foodLength
        (closeReactionSet (fun y r => ω (y, r))
          (eligibleInitialSplitReactionUnion E)) (A0, A0) iter).2
      (eligibleUnreservedCrossViableReactions
        (crossPoolIter foodLength
          (closeReactionSet (fun y r => ω (y, r))
            (eligibleInitialSplitReactionUnion E)) (A0, A0) iter).1
        (crossPoolIter foodLength
          (closeReactionSet (fun y r => ω (y, r))
            (eligibleInitialSplitReactionUnion E)) (A0, A0) iter).2 x) := by
  let Cat' := closeReactionSet (fun y r => ω (y, r))
    (eligibleInitialSplitReactionUnion E)
  let S := crossPoolIter foodLength Cat' (A0, A0) iter
  have hclosed := terminal_absent_familyClosed Cat' A0 hfix hxA hxAbsent
  intro hopen
  apply hclosed
  rcases hopen with ⟨r, hr, y, hy, hcat⟩
  have hrUnion : r ∈ eligibleUnreservedReactionUnion S.1 S.2 {x} :=
    Finset.mem_biUnion.mpr ⟨x, by simp, hr⟩
  have hrNotReserved : r ∉ eligibleInitialSplitReactionUnion E := by
    intro hrReserved
    exact Finset.disjoint_left.mp
      (eligibleInitialSplitReactionUnion_disjoint_unreservedUnion
        S.1 S.2 E {x}) hrReserved hrUnion
  refine ⟨r, (Finset.mem_sdiff.mp hr).1, y, hy, ?_⟩
  exact ⟨hrNotReserved, hcat⟩

/-- A whole eligible batch absent from the stabilized core has every
unreserved viable reaction family closed against the terminal catalyst pool. -/
theorem terminal_absent_eligibleUnreservedFamiliesClosed
    {n k foodLength iter : Nat}
    (ω : AmbientCoord n → Prop)
    (E U : Finset (SplitEligibleMolecule n k))
    (A0 : Finset (Molecule n))
    (hfix : crossPoolIter foodLength
      (closeReactionSet (fun y r => ω (y, r))
        (eligibleInitialSplitReactionUnion E)) (A0, A0) (iter + 1) =
      crossPoolIter foodLength
        (closeReactionSet (fun y r => ω (y, r))
          (eligibleInitialSplitReactionUnion E)) (A0, A0) iter)
    (hUA : ∀ x ∈ U, x.1 ∈ A0)
    (hUAbsent : ∀ x ∈ U, x.1 ∉ (crossPoolIter foodLength
      (closeReactionSet (fun y r => ω (y, r))
        (eligibleInitialSplitReactionUnion E)) (A0, A0) iter).1) :
    catalystPoolFamiliesClosed ω
      (crossPoolIter foodLength
        (closeReactionSet (fun y r => ω (y, r))
          (eligibleInitialSplitReactionUnion E)) (A0, A0) iter).2 U
      (eligibleUnreservedCrossViableReactions
        (crossPoolIter foodLength
          (closeReactionSet (fun y r => ω (y, r))
            (eligibleInitialSplitReactionUnion E)) (A0, A0) iter).1
        (crossPoolIter foodLength
          (closeReactionSet (fun y r => ω (y, r))
            (eligibleInitialSplitReactionUnion E)) (A0, A0) iter).2) := by
  intro x hxU
  exact terminal_absent_eligibleUnreservedFamilyClosed ω E A0 hfix
    (hUA x hxU) (hUAbsent x hxU)

/-- A fixed eligible batch missing from a stabilized high-band pruning core
pays its full unreserved closure energy, with all label reactions disabled. -/
theorem measure_terminal_absent_eligibleBatch_good_le
    {n k foodLength iter b d : Nat} (lambda : ℝ)
    (E U : Finset (SplitEligibleMolecule n k))
    (A0 : Finset (Molecule n)) (hUA : ∀ x ∈ U, x.1 ∈ A0) :
    ambientPiMeasure n lambda {ω |
      let Cat := closeReactionSet (fun y r => ω (y, r))
        (eligibleInitialSplitReactionUnion E)
      let S := crossPoolIter foodLength Cat (A0, A0) iter
      crossPoolIter foodLength Cat (A0, A0) (iter + 1) = S ∧
        (∀ x ∈ U, x.1 ∉ S.1) ∧ b ≤ S.2.card ∧
        ∀ x ∈ U, d ≤
          (eligibleUnreservedCrossViableReactions S.1 S.2 x).card} ≤
      (toNNReal (σ (catalysisP n lambda)) : ENNReal) ^
        (b * (d * U.card)) := by
  have hprob := measure_adaptive_reservedPreclosed_eligibleFamiliesClosed_le
    (foodLength := foodLength) (iter := iter) (b := b) (d := d)
    lambda (eligibleInitialSplitReactionUnion E) U (A0, A0)
  refine (measure_mono ?_).trans hprob
  intro ω hω
  let Cat := closeReactionSet (fun y r => ω (y, r))
    (eligibleInitialSplitReactionUnion E)
  let S := crossPoolIter foodLength Cat (A0, A0) iter
  have hdisj : Disjoint (eligibleMoleculeValues U) S.1 := by
    rw [Finset.disjoint_left]
    intro z hzU hzS
    obtain ⟨x, hxU, rfl⟩ := Finset.mem_image.mp hzU
    exact hω.2.1 x hxU hzS
  have heq := crossPoolIter_close_terminalAbsent_eq
    Cat A0 (eligibleMoleculeValues U) hω.1 hdisj
  have hclosed := terminal_absent_eligibleUnreservedFamiliesClosed
    ω E U A0 hω.1 hUA hω.2.1
  have hgoal :
      b ≤ (crossPoolIter foodLength
        (closeTargetBlocks Cat (eligibleMoleculeValues U))
        (A0, A0) iter).2.card ∧
      (∀ x ∈ U, d ≤
        (eligibleUnreservedCrossViableReactions
          (crossPoolIter foodLength
            (closeTargetBlocks Cat (eligibleMoleculeValues U))
            (A0, A0) iter).1
          (crossPoolIter foodLength
            (closeTargetBlocks Cat (eligibleMoleculeValues U))
            (A0, A0) iter).2 x).card) ∧
      catalystPoolFamiliesClosed ω
        (crossPoolIter foodLength
          (closeTargetBlocks Cat (eligibleMoleculeValues U))
          (A0, A0) iter).2 U
        (eligibleUnreservedCrossViableReactions
          (crossPoolIter foodLength
            (closeTargetBlocks Cat (eligibleMoleculeValues U))
            (A0, A0) iter).1
          (crossPoolIter foodLength
            (closeTargetBlocks Cat (eligibleMoleculeValues U))
            (A0, A0) iter).2) := by
    rw [heq]
    exact ⟨hω.2.2.1, hω.2.2.2, hclosed⟩
  simpa only [Cat] using hgoal

/-- Exact binomial union over eligible terminal-hole batches for a fixed
reserved high-band label set. -/
theorem measure_exists_terminal_absent_eligibleBatch_good_exact_le
    {n k foodLength iter b d t : Nat} (lambda : ℝ)
    (E W : Finset (SplitEligibleMolecule n k))
    (A0 : Finset (Molecule n)) (hWA : ∀ x ∈ W, x.1 ∈ A0) :
    ambientPiMeasure n lambda {ω |
      ∃ U ∈ W.powersetCard t,
        let Cat := closeReactionSet (fun y r => ω (y, r))
          (eligibleInitialSplitReactionUnion E)
        let S := crossPoolIter foodLength Cat (A0, A0) iter
        crossPoolIter foodLength Cat (A0, A0) (iter + 1) = S ∧
          (∀ x ∈ U, x.1 ∉ S.1) ∧ b ≤ S.2.card ∧
          ∀ x ∈ U, d ≤
            (eligibleUnreservedCrossViableReactions S.1 S.2 x).card} ≤
      (Nat.choose W.card t : ENNReal) *
        (toNNReal (σ (catalysisP n lambda)) : ENNReal) ^
          (b * (d * t)) := by
  classical
  let Candidates := W.powersetCard t
  let Event : Finset (SplitEligibleMolecule n k) →
      Set (AmbientCoord n → Prop) := fun U => {ω |
    let Cat := closeReactionSet (fun y r => ω (y, r))
      (eligibleInitialSplitReactionUnion E)
    let S := crossPoolIter foodLength Cat (A0, A0) iter
    crossPoolIter foodLength Cat (A0, A0) (iter + 1) = S ∧
      (∀ x ∈ U, x.1 ∉ S.1) ∧ b ≤ S.2.card ∧
      ∀ x ∈ U, d ≤
        (eligibleUnreservedCrossViableReactions S.1 S.2 x).card}
  rw [show {ω : AmbientCoord n → Prop |
      ∃ U ∈ W.powersetCard t,
        let Cat := closeReactionSet (fun y r => ω (y, r))
          (eligibleInitialSplitReactionUnion E)
        let S := crossPoolIter foodLength Cat (A0, A0) iter
        crossPoolIter foodLength Cat (A0, A0) (iter + 1) = S ∧
          (∀ x ∈ U, x.1 ∉ S.1) ∧ b ≤ S.2.card ∧
          ∀ x ∈ U, d ≤
            (eligibleUnreservedCrossViableReactions S.1 S.2 x).card} =
      ⋃ U ∈ Candidates, Event U by
    ext ω
    constructor
    · rintro ⟨U, hUC, hUE⟩
      exact Set.mem_iUnion.mpr ⟨U, Set.mem_iUnion.mpr
        ⟨by simpa [Candidates] using hUC, hUE⟩⟩
    · intro hω
      rcases Set.mem_iUnion.mp hω with ⟨U, hω⟩
      rcases Set.mem_iUnion.mp hω with ⟨hUC, hUE⟩
      exact ⟨U, by simpa [Candidates] using hUC, hUE⟩]
  calc
    ambientPiMeasure n lambda (⋃ U ∈ Candidates, Event U) ≤
        ∑ U ∈ Candidates, ambientPiMeasure n lambda (Event U) :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑ _U ∈ Candidates,
        (toNNReal (σ (catalysisP n lambda)) : ENNReal) ^
          (b * (d * t)) := by
      apply Finset.sum_le_sum
      intro U hU
      have hdata := Finset.mem_powersetCard.mp hU
      have hUA : ∀ x ∈ U, x.1 ∈ A0 := by
        intro x hx
        exact hWA x (hdata.1 hx)
      simpa only [Event, hdata.2] using
        (measure_terminal_absent_eligibleBatch_good_le
          (foodLength := foodLength) (iter := iter) (b := b) (d := d)
          lambda E U A0 hUA)
    _ = (Candidates.card : ENNReal) *
        (toNNReal (σ (catalysisP n lambda)) : ENNReal) ^
          (b * (d * t)) := by simp
    _ = (Nat.choose W.card t : ENNReal) *
        (toNNReal (σ (catalysisP n lambda)) : ENNReal) ^
          (b * (d * t)) := by
      rw [show Candidates.card = Nat.choose W.card t by
        simp [Candidates]]

/-- Sharp mark-count concentration over an arbitrary high-band molecule set. -/
theorem measure_eligibleInitialSplitMarkCount_le_sharp {n k : Nat}
    (lambda : ℝ) (C : Finset (Molecule n))
    (E : Finset (SplitEligibleMolecule n k)) {c : ℝ} (hc : 0 < c) :
    ambientPiMeasure n lambda {ω |
      (∑ x ∈ E, catalystPoolFamilyIndicator C
        (eligibleInitialSplitReactions x) ω) ≤
      (E.card : ℝ) *
        (1 - (toNNReal (σ (catalysisP n lambda)) : ℝ) ^
          (C.card * k)) - c} ≤
      ENNReal.ofReal (((E.card : ℝ) *
        (toNNReal (σ (catalysisP n lambda)) : ℝ) ^
          (C.card * k)) / c ^ 2) := by
  have hR : Pairwise fun (x y : SplitEligibleMolecule n k) =>
      Disjoint (eligibleInitialSplitReactions x)
        (eligibleInitialSplitReactions y) := by
    intro x y hxy
    exact eligibleInitialSplitReactions_disjoint hxy
  have hcard : ∀ x ∈ E, k ≤ (eligibleInitialSplitReactions x).card := by
    intro x _
    simp
  simpa using
    (measure_sum_catalystPoolFamilyIndicator_le_card_mul_one_sub_pow_sub_sharp
      lambda C E eligibleInitialSplitReactions hR hcard hc)

end HordijkSteelThreshold
