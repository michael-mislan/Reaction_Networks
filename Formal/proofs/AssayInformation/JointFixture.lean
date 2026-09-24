import proofs.AssayInformation.IdentityRescue

noncomputable section
namespace AssayInformation
open DiagnosticWindows FiniteCopy
open scoped BigOperators

theorem miss5_nonneg (t : NNReal) : 0 ≤ miss5 t := by
  unfold miss5 loadedSurvival
  apply tsum_nonneg
  intro n
  apply mul_nonneg (poissonWeight_nonneg _ _)
  rw [uncalled_indicator]
  exact (kernel5.poissonized_event_bounds _ _ _).1

def blankJoint : Fin 3 → ℝ := ![
  (1/100)*blank5 7, (99/100)*blank5 7, 1-blank5 7]
def loadedJoint : Fin 3 → ℝ := ![
  (99/100)*occupiedHit 7+(1/100)*Real.exp (-4)*blank5 7,
  (1/100)*occupiedHit 7+(99/100)*Real.exp (-4)*blank5 7,
  miss5 7]

/-- Categories: hit/marker-positive, hit/marker-negative, no hit.
Each law retains the original crossing probability and the empty-loading component. -/
theorem joint_fixture_valid :
    (∀ i, 0 ≤ blankJoint i) ∧ (∑ i, blankJoint i) = 1 ∧
    (∀ i, 0 ≤ loadedJoint i) ∧ (∑ i, loadedJoint i) = 1 ∧
    blankJoint 0 + blankJoint 1 = blank5 7 ∧
    loadedJoint 0 + loadedJoint 1 = 1-miss5 7 := by
  have hb := blank5_nonneg 7
  have hb1 := rescue_source_bounds.1
  have hc : 0 ≤ occupiedHit 7 := by linarith [occupiedHit_seven]
  have hm := miss5_nonneg 7
  have he := (Real.exp_pos (-4)).le
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro i
    fin_cases i <;> norm_num [blankJoint] <;> nlinarith
  · norm_num [blankJoint,Fin.sum_univ_succ]
    ring
  · intro i
    fin_cases i <;> norm_num [loadedJoint] <;> positivity
  · norm_num [loadedJoint,Fin.sum_univ_succ,occupiedHit]
    ring
  · norm_num [blankJoint]
    ring
  · norm_num [loadedJoint,occupiedHit]
    ring

/-- A concrete source-conditional channel succeeds without changing total-count chemistry. -/
theorem concrete_joint_rescue :
    blankJoint 0 < 3/10000 ∧ 1-loadedJoint 0 < 422443/10000000 := by
  apply identity_rescue
  · norm_num [blankJoint]
  · have hb := blank5_nonneg 7
    have he := (Real.exp_pos (-4)).le
    norm_num [loadedJoint]
    nlinarith [mul_nonneg he hb]

end AssayInformation
