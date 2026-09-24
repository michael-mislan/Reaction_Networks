import proofs.RandomViability.BindingTrackedEntry
import proofs.RandomViability.BindingBookkeeping

namespace RandomViability.Binding
noncomputable section
open Classical FiniteCopy
open scoped NNReal

abbrev OutputState := TrackedCounts × Fin 10000001

/-- Covalent product mass exported by one literal reaction. -/
def exportUnits : Fin 18 → ℕ := ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,4,4,8]

theorem exportUnits_real (j : Fin 18) : (exportUnits j:ℝ) = exportMark j := by
  fin_cases j <;> norm_num [exportUnits,exportMark]

def outputNext (enabled : Bool) (X : OutputState) (j : Fin 18) : OutputState :=
  (trackedNext X.1 j,⟨min 10000000 (X.2.val+(if enabled then exportUnits j else 0)),by
    have h := Nat.min_le_left 10000000 (X.2.val+(if enabled then exportUnits j else 0))
    omega⟩)

theorem outputNext_disabled (X : OutputState) (j : Fin 18) : (outputNext false X j).2 = X.2 := by
  apply Fin.ext
  simp only [outputNext,Bool.false_eq_true,if_false,add_zero]
  apply Nat.min_eq_right
  have h := X.2.isLt
  omega

def outputModel (enabled : Bool) (eps k r : ℝ) (heps : 0 ≤ eps) (hk : 0 ≤ k) (hr : 0 ≤ r) :
    FiniteJumpModel OutputState (Fin 18) where
  next := outputNext enabled
  rate X j := if enabled=true ∧ trackedPhase X.1=0 then 0 else (trackedModel eps k r heps hk hr).rate X.1 j
  nonneg X j := by
    split_ifs
    · rfl
    · exact (trackedModel eps k r heps hk hr).nonneg X.1 j

theorem output_generator_project (enabled : Bool) (eps k r : ℝ) (heps : 0 ≤ eps) (hk : 0 ≤ k) (hr : 0 ≤ r)
    (f : TrackedCounts → ℝ) (X : OutputState) (h : ¬(enabled=true ∧ trackedPhase X.1=0)) :
    (outputModel enabled eps k r heps hk hr).generator (fun Z => f Z.1) X =
      (trackedModel eps k r heps hk hr).generator f X.1 := by
  simp only [FiniteJumpModel.generator,outputModel,if_neg h,outputNext]
  rfl

theorem output_generator_deadline_failure (eps k r : ℝ) (heps : 0 ≤ eps) (hk : 0 ≤ k) (hr : 0 ≤ r)
    (f : OutputState → ℝ) (X : OutputState) (h : trackedPhase X.1=0) :
    (outputModel true eps k r heps hk hr).generator f X = 0 := by
  simp [FiniteJumpModel.generator,outputModel,h]

theorem output_total_bound (enabled : Bool) (eps k r : ℝ) (heps : 0 ≤ eps) (heps1 : eps ≤ 1)
    (hk : 0 ≤ k) (hk1 : k ≤ 1/8) (hr : 0 ≤ r) (hr1 : r ≤ 22) (X : OutputState) :
    (outputModel enabled eps k r heps hk hr).total X ≤ 300000000000 := by
  by_cases h : enabled=true ∧ trackedPhase X.1=0
  · simp [FiniteJumpModel.total,outputModel,h]
  · simpa only [FiniteJumpModel.total,outputModel,if_neg h] using
      tracked_total_bound eps k r heps heps1 hk hk1 hr hr1 X.1

def operatingOutputKernel (enabled : Bool) (k r : ℝ) (hk : 0 ≤ k) (hk1 : k ≤ 1/8)
    (hr : 18 ≤ r) (hr1 : r ≤ 22) : FiniteKernel OutputState :=
  (outputModel enabled (1/500000000) k r (by norm_num) hk (by linarith)).uniformize
    300000000000 (by norm_num) (output_total_bound enabled (1/500000000) k r
      (by norm_num) (by norm_num) hk hk1 (by linarith) hr1)

theorem output_step_project (k r : ℝ) (hk : 0 ≤ k) (hk1 : k ≤ 1/8)
    (hr : 18 ≤ r) (hr1 : r ≤ 22) (f : TrackedCounts → ℝ) (X : OutputState) :
    (operatingOutputKernel false k r hk hk1 hr hr1).step (fun Z => f Z.1) X =
      (operatingTrackedKernel k r hk hk1 hr hr1).step f X.1 := by
  simp only [operatingOutputKernel,operatingTrackedKernel,FiniteJumpModel.uniformize_step]
  rw [output_generator_project false _ _ _ _ _ _ f X (by simp)]

theorem output_steps_project (k r : ℝ) (hk : 0 ≤ k) (hk1 : k ≤ 1/8)
    (hr : 18 ≤ r) (hr1 : r ≤ 22) (f : TrackedCounts → ℝ) (n : ℕ) (X : OutputState) :
    (operatingOutputKernel false k r hk hk1 hr hr1).steps n (fun Z => f Z.1) X =
      (operatingTrackedKernel k r hk hk1 hr hr1).steps n f X.1 := by
  induction n generalizing X with
  | zero => rfl
  | succ n ih =>
    rw [FiniteKernel.steps,show (operatingOutputKernel false k r hk hk1 hr hr1).steps n (fun Z => f Z.1) =
      (fun Z => (operatingTrackedKernel k r hk hk1 hr hr1).steps n f Z.1) from funext ih]
    exact output_step_project k r hk hk1 hr hr1 _ X

theorem output_poisson_project (k r : ℝ) (hk : 0 ≤ k) (hk1 : k ≤ 1/8)
    (hr : 18 ≤ r) (hr1 : r ≤ 22) (f : TrackedCounts → ℝ) (t : ℝ≥0) (X : OutputState) :
    (operatingOutputKernel false k r hk hk1 hr hr1).poissonized t (fun Z => f Z.1) X =
      (operatingTrackedKernel k r hk hk1 hr hr1).poissonized t f X.1 := by
  unfold FiniteKernel.poissonized
  apply tsum_congr
  intro n
  rw [output_steps_project]

def outputInitial : OutputState := (trackedInitial,0)

end
end RandomViability.Binding
