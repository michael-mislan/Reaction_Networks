import proofs.HordijkSteelThreshold.CatalystPoolFamilyBlocks

namespace HordijkSteelThreshold

open MeasureTheory ProbabilityTheory
open RAF RAF.Polymer RAF.Concrete

/-- All catalysis coordinates from a fixed prospective pool into reactions
whose product lies in a prescribed target set. -/
def catalystPoolTargetBlock {n : Nat} (C T : Finset (Molecule n)) :
    Finset (AmbientCoord n) :=
  C.product (Finset.univ.filter fun r : Reaction n => reactionProduct r ∈ T)

/-- Disjoint product-target layers expose disjoint Bernoulli coordinate
blocks, even though their factor-generation cones may overlap. -/
theorem catalystPoolTargetBlock_disjoint {n : Nat}
    (C : Finset (Molecule n)) {T U : Finset (Molecule n)}
    (hTU : Disjoint T U) :
    Disjoint (catalystPoolTargetBlock C T)
      (catalystPoolTargetBlock C U) := by
  rw [Finset.disjoint_left]
  intro z hzT hzU
  have hrT := (Finset.mem_filter.mp (Finset.mem_product.mp hzT).2).2
  have hrU := (Finset.mem_filter.mp (Finset.mem_product.mp hzU).2).2
  exact Finset.disjoint_left.mp hTU hrT hrU

/-- The complete coordinate restrictions of two disjoint target layers are
independent. This is the deferred-decision interface: an arbitrary measurable
past statistic may be built from one block before the other block is exposed. -/
theorem catalystPoolTarget_restrictions_indep {n : Nat} (lambda : ℝ)
    (C : Finset (Molecule n)) {T U : Finset (Molecule n)}
    (hTU : Disjoint T U) :
    IndepFun
      (fun (ω : AmbientCoord n → Prop)
        (z : catalystPoolTargetBlock C T) => ω z)
      (fun (ω : AmbientCoord n → Prop)
        (z : catalystPoolTargetBlock C U) => ω z)
      (ambientPiMeasure n lambda) := by
  exact (ambientCoordinate_iIndep n lambda).indepFun_finset
    (catalystPoolTargetBlock C T) (catalystPoolTargetBlock C U)
    (catalystPoolTargetBlock_disjoint C hTU)
    (fun _ => measurable_pi_apply _)

/-- Any measurable statistics of two disjoint product-target blocks remain
independent. In applications the first statistic is the complete generated
past and the second is the supported-target count in the fresh layer. -/
theorem catalystPoolTarget_statistics_indep {n : Nat} (lambda : ℝ)
    (C : Finset (Molecule n)) {T U : Finset (Molecule n)}
    (hTU : Disjoint T U) {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (f : (catalystPoolTargetBlock C T → Prop) → α)
    (g : (catalystPoolTargetBlock C U → Prop) → β)
    (hf : Measurable f) (hg : Measurable g) :
    IndepFun
      (f ∘ fun (ω : AmbientCoord n → Prop)
        (z : catalystPoolTargetBlock C T) => ω z)
      (g ∘ fun (ω : AmbientCoord n → Prop)
        (z : catalystPoolTargetBlock C U) => ω z)
      (ambientPiMeasure n lambda) := by
  exact (catalystPoolTarget_restrictions_indep lambda C hTU).comp hf hg

end HordijkSteelThreshold
