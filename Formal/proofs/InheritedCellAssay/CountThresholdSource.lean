import proofs.CompositionalMemory.FiniteTimeDependentCertificate
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp

namespace InheritedCellAssay.CountThreshold
open FiniteCopy CompositionalMemory

/-- Exact backward solutions determine the already constructed finite CT law. -/
theorem backward_solution_expectation {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] (M : FiniteJumpModel α β) (v : ℝ → α → ℝ)
    (hv : ∀ t x, HasDerivAt (fun s => v s x) (M.generator (v t) x) t)
    (T : NNReal) (x : α) : finiteTimeExpectation M T (v 0) x = v T x := by
  let F := fun t : ℝ => (NormedSpace.exp (t • jumpGeneratorMatrix M)).mulVec
    (v ((T : ℝ)-t)) x
  have hd (t : ℝ) : HasDerivAt F 0 t := by
    have hh := finite_dynamic_expectation_derivative M
      (fun s => v ((T : ℝ)-s))
      (fun s y => -M.generator (v ((T : ℝ)-s)) y) t
      (fun y => by
        have h := (hv ((T : ℝ)-t) y).comp t ((hasDerivAt_id t).const_sub (T : ℝ))
        simpa only [mul_neg_one] using h) x
    simpa [F, Matrix.mulVec, dotProduct] using hh
  have hc := is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt)
    (fun t => (hd t).deriv) (T : ℝ) 0
  simpa [F, finiteTimeExpectation] using hc

/-- Counts 1,2,3,4-or-more. Rates are per ten days. Beyond the observation
    threshold every birth is silent; the last state is observationally absorbing. -/
def birthNext (n : Fin 4) : Fin 4 := ⟨min (n.val+1) 3, by omega⟩

noncomputable def birthSource : FiniteJumpModel (Fin 4) Unit where
  next n _ := birthNext n
  rate n _ := (n.val+1 : ℝ)
  nonneg n _ := by positivity

noncomputable def belowTwo (t : ℝ) : Fin 4 → ℝ :=
  ![2*Real.exp (-t) - Real.exp (-t)^2, Real.exp (-t)^2, 0, 0]

noncomputable def belowThree (t : ℝ) : Fin 4 → ℝ :=
  ![3*Real.exp (-t)-3*Real.exp (-t)^2+Real.exp (-t)^3,
    3*Real.exp (-t)^2-2*Real.exp (-t)^3, Real.exp (-t)^3, 0]

theorem belowTwo_backward (t : ℝ) (n : Fin 4) :
    HasDerivAt (fun s => belowTwo s n) (birthSource.generator (belowTwo t) n) t := by
  have he : HasDerivAt (fun s : ℝ => Real.exp (-s)) (-Real.exp (-t)) t := by
    simpa using (hasDerivAt_id t).neg.exp
  fin_cases n <;> simp [belowTwo, birthSource, birthNext, FiniteJumpModel.generator]
  all_goals first
  | solve | convert ((he.const_mul 2).sub (he.pow 2)) using 1 <;> norm_num <;>
      ring
  | solve | convert he.pow 2 using 1 <;> norm_num <;> ring
  | solve | exact hasDerivAt_const t (0 : ℝ)

theorem belowThree_backward (t : ℝ) (n : Fin 4) :
    HasDerivAt (fun s => belowThree s n) (birthSource.generator (belowThree t) n) t := by
  have he : HasDerivAt (fun s : ℝ => Real.exp (-s)) (-Real.exp (-t)) t := by
    simpa using (hasDerivAt_id t).neg.exp
  fin_cases n <;> simp [belowThree, birthSource, birthNext, FiniteJumpModel.generator]
  all_goals first
  | solve | convert (((he.const_mul 3).sub ((he.pow 2).const_mul 3)).add
      (he.pow 3)) using 1 <;> norm_num <;> ring
  | solve | convert (((he.pow 2).const_mul 3).sub ((he.pow 3).const_mul 2))
      using 1 <;> norm_num <;> ring
  | solve | convert he.pow 3 using 1 <;> norm_num <;> ring
  | solve | exact hasDerivAt_const t (0 : ℝ)

noncomputable def horizon : NNReal := ⟨Real.log 2, Real.log_nonneg (by norm_num)⟩

theorem source_below_two : finiteTimeExpectation birthSource horizon
    (fun n : Fin 4 => if n.val < 2 then 1 else 0) 0 = 3/4 := by
  have hv : (fun n : Fin 4 => if n.val < 2 then (1 : ℝ) else 0) = belowTwo 0 := by
    funext n
    fin_cases n <;> norm_num [belowTwo]
  rw [hv, backward_solution_expectation birthSource belowTwo belowTwo_backward]
  change belowTwo (Real.log 2) 0 = 3/4
  norm_num [belowTwo, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]

theorem source_below_three : finiteTimeExpectation birthSource horizon
    (fun n : Fin 4 => if n.val < 3 then 1 else 0) 0 = 7/8 := by
  have hv : (fun n : Fin 4 => if n.val < 3 then (1 : ℝ) else 0) = belowThree 0 := by
    funext n
    fin_cases n <;> norm_num [belowThree]
  rw [hv, backward_solution_expectation birthSource belowThree belowThree_backward]
  change belowThree (Real.log 2) 0 = 7/8
  norm_num [belowThree, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]

/-- Sensitive families have count at most one and so always belong to either
    prediction interval. This is the explicit mixture of the two observed laws. -/
noncomputable def mixedCoverage (k : ℕ) : ℝ := 19/24 + (5/24) *
  finiteTimeExpectation birthSource horizon (fun n : Fin 4 => if n.val < k then 1 else 0) 0

theorem source_coverage_failure_and_repair :
    mixedCoverage 2 = 91/96 ∧ mixedCoverage 2 < 19/20 ∧
    mixedCoverage 3 = 187/192 ∧ 19/20 < mixedCoverage 3 := by
  simp only [mixedCoverage, source_below_two, source_below_three]
  norm_num

end InheritedCellAssay.CountThreshold
