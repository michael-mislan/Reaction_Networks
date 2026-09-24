import proofs.HordijkSteelThreshold.ComponentDeletion
import proofs.HordijkSteelThreshold.FamilyOpenProbability

namespace HordijkSteelThreshold

open RAF RAF.Polymer RAF.Concrete
open MeasureTheory ProbabilityTheory unitInterval

/-- The source-coordinate consequence of an actual closed-block schedule. -/
theorem componentDeletionClosed_subset_rectangle {n L h : Nat}
    (S : Finset (Reaction n)) (rank : Molecule n → Nat) :
    {ω : AmbientCoord n → Prop |
      ComponentDeletionClosed L (fun x r => ω (x,r)) S rank h} ⊆
    {ω | catalystBlockClosed ω ((deletionPool rank h).product
      (deletionForbiddenEdges L S rank h))} := by
  intro ω hc z hz
  obtain ⟨hx, hr⟩ := Finset.mem_product.mp hz
  have hn := componentDeletion_forbidden_absent hc hx hr
  exact propext ⟨fun hp => (hn hp).elim, False.elim⟩

/-- Fixed-schedule bound: no conditioning on a random selected catalyst pool. -/
theorem measure_componentDeletionClosed_le {n L h : Nat} (lambda : ℝ)
    (S : Finset (Reaction n)) (rank : Molecule n → Nat) :
    ambientPiMeasure n lambda {ω : AmbientCoord n → Prop |
      ComponentDeletionClosed L (fun x r => ω (x,r)) S rank h} ≤
    (toNNReal (σ (catalysisP n lambda)) : ENNReal) ^
      ((deletionPool rank h).card * (deletionForbiddenEdges L S rank h).card) := by
  calc
    _ ≤ ambientPiMeasure n lambda {ω | catalystBlockClosed ω
        ((deletionPool rank h).product (deletionForbiddenEdges L S rank h))} :=
      measure_mono (componentDeletionClosed_subset_rectangle S rank)
    _ = _ := by rw [measure_catalystBlockClosed_card]; simp

/-- A finite family may cover adaptively selected schedules. The union cost is
explicit; proving an affordable covering family remains a mathematical task. -/
theorem measure_exists_componentDeletionClosed_le {n L h : Nat} {ι : Type*}
    [DecidableEq ι] (lambda : ℝ) (S : Finset (Reaction n))
    (T : Finset ι) (rank : ι → Molecule n → Nat) :
    ambientPiMeasure n lambda {ω : AmbientCoord n → Prop |
      ∃ i ∈ T, ComponentDeletionClosed L (fun x r => ω (x,r)) S (rank i) h} ≤
    ∑ i ∈ T, (toNNReal (σ (catalysisP n lambda)) : ENNReal) ^
      ((deletionPool (rank i) h).card *
        (deletionForbiddenEdges L S (rank i) h).card) := by
  classical
  rw [show {ω : AmbientCoord n → Prop |
      ∃ i ∈ T, ComponentDeletionClosed L (fun x r => ω (x,r)) S (rank i) h} =
      ⋃ i ∈ T, {ω : AmbientCoord n → Prop |
        ComponentDeletionClosed L (fun x r => ω (x,r)) S (rank i) h} by
    ext ω; simp]
  exact (measure_biUnion_finset_le T _).trans
    (Finset.sum_le_sum fun i _ => measure_componentDeletionClosed_le lambda S (rank i))

end HordijkSteelThreshold
