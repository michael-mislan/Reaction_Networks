import proofs.HordijkSteelThreshold.TargetLayerDeferred
import proofs.HordijkSteelThreshold.AdaptiveChainBound

namespace HordijkSteelThreshold

open MeasureTheory ProbabilityTheory
open RAF RAF.Polymer RAF.Concrete

/-- Weighted deferred decision on two disjoint product-target blocks.  The
event `K` may inspect the complete complementary restriction, not merely a
summary pruning state.  Hence it can encode every later reveal in an ordered
target sequence, while the uniform section cost for the current block
multiplies its probability. -/
theorem measure_targetRestriction_adaptive_inter_le
    {n : Nat} (lambda : ℝ)
    (C : Finset (Molecule n)) {T U : Finset (Molecule n)}
    (hTU : Disjoint T U)
    (K : (catalystPoolTargetBlock C T → Prop) → Prop)
    (H : (catalystPoolTargetBlock C T → Prop) →
      (catalystPoolTargetBlock C U → Prop) → Prop)
    (hH : ∀ v, MeasurableSet {w | H v w}) {p : ENNReal}
    (hsec : ∀ v,
      ambientPiMeasure n lambda {ω | H v (fun z => ω z)} ≤ p) :
    ambientPiMeasure n lambda {ω |
      K (fun z : catalystPoolTargetBlock C T => ω z) ∧
        H (fun z : catalystPoolTargetBlock C T => ω z)
          (fun z : catalystPoolTargetBlock C U => ω z)} ≤
      p * ambientPiMeasure n lambda {ω |
        K (fun z : catalystPoolTargetBlock C T => ω z)} := by
  let X : (AmbientCoord n → Prop) →
      (catalystPoolTargetBlock C T → Prop) := fun ω z => ω z
  let Y : (AmbientCoord n → Prop) →
      (catalystPoolTargetBlock C U → Prop) := fun ω z => ω z
  have hind : IndepFun X Y (ambientPiMeasure n lambda) := by
    simpa [X, Y] using catalystPoolTarget_restrictions_indep lambda C hTU
  simpa [X, Y] using measure_adaptive_of_indep_finite_inter_le hind
    (measurable_of_finite _) K H hH hsec

end HordijkSteelThreshold
