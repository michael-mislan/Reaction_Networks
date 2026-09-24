import proofs.OptimalAffinityRealizability.GlobalBoundary
import proofs.OptimalAffinityRealizability.GlobalAccessibility

namespace OptimalAffinityRealizability
open scoped BigOperators
noncomputable section

def ResponseRooted {ι : Type*} (T : Matrix ι ι ℝ) : Prop :=
  ∃ root, ∀ i, Relation.ReflTransGen (fun a b => 0 < T b a) i root

theorem responseRooted_accessibleRootedClass {n : ℕ} [Nonempty (Fin n)]
    (source : SquareSource n) (g : Fin n → ℝ)
    (hg : ∀ i, 0 < g i) (hmode : ControlledProductionMode source g)
    (hT : ∀ i j, 0 ≤ responseMatrix source i j)
    (hroot : ResponseRooted (responseMatrix source)) :
    AccessibleRootedResponseClass source := by
  intro f hf
  let q := fun i => OptimalAffinityCorrected.responseRatio (responseMatrix source) f i
  let P := routingMatrix (responseMatrix source) q f
  have hP : ∀ i j, 0 ≤ P i j := by
    intro i j
    exact div_nonneg (mul_nonneg (hT j i) (le_of_lt (hf j).1))
      (le_of_lt (mul_pos (lt_trans zero_lt_one (hf i).2) (hf i).1))
  refine ⟨positiveProduction_controlAccessible source g f hg hmode hf, hP, ?_⟩
  obtain ⟨root, hroot⟩ := hroot
  refine ⟨root, ?_⟩
  intro i
  have hp := hroot i
  clear hroot
  induction hp with
  | refl => exact ⟨0, by simp⟩
  | @tail b c _ hbc ih =>
    obtain ⟨k, hk⟩ := ih
    have hedge : 0 < P b c := div_pos (mul_pos hbc (hf c).1)
      (mul_pos (lt_trans zero_lt_one (hf b).2) (hf b).1)
    refine ⟨k+1, ?_⟩
    rw [pow_succ, Matrix.mul_apply]
    apply lt_of_lt_of_le (mul_pos hk hedge)
    exact Finset.single_le_sum (fun j _ =>
      mul_nonneg (Matrix.pow_apply_nonneg hP k i j) (hP j c)) (Finset.mem_univ b)

/-- Primitive source-checkable version: graph rootedness and nonnegativity
replace a universally quantified accessibility/routing class assumption. -/
theorem rootedSource_globalCapacityEquality {n : ℕ} [Nonempty (Fin n)]
    (source : SquareSource n) (weights : Fin n → ℕ) (J : ℝ) (g : Fin n → ℝ)
    (hroot : ResponseRooted (responseMatrix source))
    (hT : ∀ i j, 0 ≤ responseMatrix source i j)
    (hJ : 0 < J) (hg : ∀ i, 0 < g i) (hmode : ControlledProductionMode source g)
    (hne : ∃ f, ResponseFeasible (responseMatrix source) f) :
    (∃ f, GlobalRealizable source J g f) ∧
    realizationCapacity (responseMatrix source) weights (GlobalRealizable source J g) =
      responseLayerCapacity (responseMatrix source) weights :=
  rawSquareSource_globalCapacityEquality source weights J g
    (responseRooted_accessibleRootedClass source g hg hmode hT hroot) hT hJ hg hmode hne

theorem stronglyConnectedSource_uniqueGlobalCapacityEquality {n : ℕ} [Nonempty (Fin n)]
    (source : SquareSource n) (weights : Fin n → ℕ) (J : ℝ) (g : Fin n → ℝ)
    (hconn : ResponseStronglyConnected (responseMatrix source))
    (hT : ∀ i j, 0 ≤ responseMatrix source i j)
    (hJ : 0 < J) (hg : ∀ i, 0 < g i) (hmode : ControlledProductionMode source g)
    (hne : ∃ f, ResponseFeasible (responseMatrix source) f) :
    (∃ f, UniqueGlobalRealizable source J g f) ∧
    realizationCapacity (responseMatrix source) weights (UniqueGlobalRealizable source J g) =
      responseLayerCapacity (responseMatrix source) weights :=
  rawSquareSource_uniqueGlobalCapacityEquality source weights J g
    (responseRooted_accessibleRootedClass source g hg hmode hT
      ⟨source.controlled, fun i => hconn i source.controlled⟩) hT hconn hJ hg hmode hne

end
end OptimalAffinityRealizability
