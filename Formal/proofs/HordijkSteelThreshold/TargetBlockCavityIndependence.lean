import proofs.HordijkSteelThreshold.TargetLayerDeferred
import proofs.HordijkSteelThreshold.TwoPoolPruning
import proofs.HordijkSteelThreshold.AdaptiveMixtureBound

namespace HordijkSteelThreshold

open MeasureTheory ProbabilityTheory
open RAF RAF.Polymer RAF.Concrete

/-- Reconstruct a catalysis sample using only coordinates whose reaction
product lies in `U`, setting every other coordinate to false. -/
def catalysisFromTargetRestriction {n : Nat} (U : Finset (Molecule n))
    (v : catalystPoolTargetBlock (Finset.univ : Finset (Molecule n)) U → Prop) :
    Catalysis (Molecule n) (Reaction n) :=
  fun y r => if h : reactionProduct r ∈ U then
    v ⟨(y, r), by simp [catalystPoolTargetBlock, h]⟩ else False

@[simp] theorem catalysisFromTargetRestriction_apply {n : Nat}
    (U : Finset (Molecule n))
    (v : catalystPoolTargetBlock (Finset.univ : Finset (Molecule n)) U → Prop)
    (y : Molecule n) (r : Reaction n) :
    catalysisFromTargetRestriction U v y r ↔
      ∃ h : reactionProduct r ∈ U, v ⟨(y, r), by
        simp [catalystPoolTargetBlock, h]⟩ := by
  by_cases h : reactionProduct r ∈ U <;>
    simp [catalysisFromTargetRestriction, h]

/-- Closing `T` in a full sample is exactly reconstruction from the
complementary product-target restriction. -/
theorem closeTargetBlocks_eq_from_complement {n : Nat}
    (ω : AmbientCoord n → Prop) (T : Finset (Molecule n)) :
    closeTargetBlocks (fun y r => ω (y, r)) T =
      catalysisFromTargetRestriction
        ((Finset.univ : Finset (Molecule n)) \ T)
        (fun z => ω z) := by
  funext y r
  apply propext
  simp [closeTargetBlocks, catalysisFromTargetRestriction, and_comm]

/-- The full closed-cavity pruning history is independent of the held-out
target block: it factors through the complementary product-target
restriction, which is a disjoint Bernoulli coordinate block. -/
theorem closedTargetIter_statistics_indep {n foodLength k : Nat}
    (lambda : ℝ) (T : Finset (Molecule n))
    (P : Finset (Molecule n) × Finset (Molecule n))
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (f : (Finset (Molecule n) × Finset (Molecule n)) → α)
    (g : (catalystPoolTargetBlock
      (Finset.univ : Finset (Molecule n)) T → Prop) → β)
    (hf : Measurable (fun v => f (crossPoolIter foodLength
      (catalysisFromTargetRestriction
        ((Finset.univ : Finset (Molecule n)) \ T) v) P k)))
    (hg : Measurable g) :
    IndepFun
      (fun (ω : AmbientCoord n → Prop) =>
        f (crossPoolIter foodLength
          (closeTargetBlocks (fun y r => ω (y, r)) T) P k))
      (fun (ω : AmbientCoord n → Prop) =>
        g (fun z : catalystPoolTargetBlock
          (Finset.univ : Finset (Molecule n)) T => ω z))
      (ambientPiMeasure n lambda) := by
  let U : Finset (Molecule n) :=
    (Finset.univ : Finset (Molecule n)) \ T
  have hUT : Disjoint U T := by
    simp [U, Finset.disjoint_left]
  have hind := catalystPoolTarget_statistics_indep lambda
    (Finset.univ : Finset (Molecule n)) hUT
    (fun v => f (crossPoolIter foodLength
      (catalysisFromTargetRestriction U v) P k)) g hf hg
  simpa only [U, Function.comp_apply,
    closeTargetBlocks_eq_from_complement] using hind

/-- A uniform fixed-state estimate for a held-out target block remains valid
when the state is the adaptively generated closed-cavity pruning history.  No
union bound over possible pruning states is paid. -/
theorem measure_adaptive_closedTargetIter_le {n foodLength k : Nat}
    (lambda : ℝ) (T : Finset (Molecule n))
    (P : Finset (Molecule n) × Finset (Molecule n))
    (H : (Finset (Molecule n) × Finset (Molecule n)) →
      (catalystPoolTargetBlock
        (Finset.univ : Finset (Molecule n)) T → Prop) → Prop)
    (hH : ∀ S, MeasurableSet {v | H S v}) {p : ENNReal}
    (hsec : ∀ S,
      ambientPiMeasure n lambda {ω | H S (fun z => ω z)} ≤ p) :
    ambientPiMeasure n lambda {ω |
      H (crossPoolIter foodLength
          (closeTargetBlocks (fun y r => ω (y, r)) T) P k)
        (fun z => ω z)} ≤ p := by
  let State := Finset (Molecule n) × Finset (Molecule n)
  letI : MeasurableSpace State := ⊤
  let X : (AmbientCoord n → Prop) → State := fun ω =>
    crossPoolIter foodLength
      (closeTargetBlocks (fun y r => ω (y, r)) T) P k
  let Y : (AmbientCoord n → Prop) →
      (catalystPoolTargetBlock
        (Finset.univ : Finset (Molecule n)) T → Prop) :=
    fun ω z => ω z
  have hind : IndepFun X Y (ambientPiMeasure n lambda) := by
    simpa [X, Y, State] using closedTargetIter_statistics_indep
      lambda T P (fun S => S) (fun v => v) (measurable_of_finite _) measurable_id
  exact measure_adaptive_of_indep_finite hind (measurable_of_finite _) H hH hsec

end HordijkSteelThreshold
