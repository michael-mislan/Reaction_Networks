import proofs.OscillatoryCores.Linearization
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Prod

namespace OscillatoryCores

open DUnstableCores Polynomial
open scoped BigOperators

noncomputable def pathMonomial (u : State) (j : Fin 5) : ℝ[X] :=
  ∏ i : Fin 4, (1 + X * C (u i)) ^ source.reactant i j

noncomputable def pathField (t : ℝ) (u : State) (i : Fin 4) : ℝ[X] :=
  ∑ j : Fin 5, C (normalizedCoefficient t i j) * pathMonomial u j

theorem eval_pathMonomial (u : State) (j : Fin 5) (r : ℝ) :
    (pathMonomial u j).eval r =
      massActionMonomial source (fun i => 1 + r * u i) j := by
  simp only [pathMonomial, massActionMonomial, Polynomial.eval_prod,
    Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_one, Polynomial.eval_X, Polynomial.eval_C]

theorem eval_pathField (t : ℝ) (u : State) (i : Fin 4) (r : ℝ) :
    (pathField t u i).eval r = normalizedField t (fun k => 1 + r*u k) i := by
  simp [pathField, normalizedField, Polynomial.eval_finsetSum, eval_pathMonomial]

theorem normalizedField_one (t : ℝ) (i : Fin 4) :
    normalizedField t (fun _ => 1) i = 0 := by
  have hb := congrArg (fun r : ℝ => r / equilibrium t i) (balanced i)
  simpa [normalizedField, normalizedCoefficient, massActionMonomial, Finset.sum_div] using hb

theorem pathField_coeff_zero (t : ℝ) (u : State) (i : Fin 4) :
    (pathField t u i).coeff 0 = 0 := by
  rw [Polynomial.coeff_zero_eq_eval_zero, eval_pathField]
  simpa using normalizedField_one t i

/-- Polynomial amplitude division, defined even at amplitude zero. -/
noncomputable def amplitudeField (t r : ℝ) (u : State) : State :=
  fun i => (pathField t u i).divX.eval r

theorem amplitudeField_source (t r : ℝ) (u : State) (i : Fin 4) :
    r * amplitudeField t r u i = normalizedField t (fun k => 1+r*u k) i := by
  have h := congrArg (fun p : ℝ[X] => p.eval r) (divX_mul_X_add (pathField t u i))
  simpa [amplitudeField, pathField_coeff_zero, eval_pathField, mul_comm] using h

theorem pathField_coeff_one (t : ℝ) (u : State) (i : Fin 4) :
    (pathField t u i).coeff 1 = normalizedLinear t u i := by
  have hpath : HasDerivAt (fun r : ℝ => fun k : Fin 4 => 1+r*u k) u 0 := by
    apply hasDerivAt_pi.mpr
    intro k
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (u k)).const_add 1
  have hcurve := (normalizedField_hasFDerivAt_one t).comp_hasDerivAt_of_eq
    0 hpath (by funext k; simp)
  have hcoord := (hasDerivAt_pi.mp hcurve) i
  have hsame : HasDerivAt (fun r : ℝ => (pathField t u i).eval r)
      (normalizedLinear t u i) 0 := by
    simpa only [eval_pathField, Function.comp_apply] using hcoord
  have heq := ((pathField t u i).hasDerivAt 0).unique hsame
  simpa [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_derivative] using heq

theorem amplitudeField_zero (t : ℝ) (u : State) :
    amplitudeField t 0 u = normalizedLinear t u := by
  funext i
  simpa [amplitudeField, ← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_divX] using
    pathField_coeff_one t u i

end OscillatoryCores
