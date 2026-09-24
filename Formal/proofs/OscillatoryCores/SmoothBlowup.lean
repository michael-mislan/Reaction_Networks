import proofs.OscillatoryCores.Blowup
import Mathlib.Analysis.Calculus.ContDiff.Operations

namespace OscillatoryCores

open Polynomial
open scoped BigOperators ContDiff

private theorem divX_mul_formula (p q : ℝ[X]) :
    (p*q).divX = p.divX*q + C (p.coeff 0)*q.divX := by
  have hx (a : ℝ[X]) : (a*X).divX = a := by
    ext n
    simp [coeff_mul_X]
  have he : p*q = (p.divX*q)*X + C (p.coeff 0)*q := by
    linear_combination -(divX_mul_X_add p)*q
  rw [he, divX_add, hx, divX_C_mul]

section Families
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A finite polynomial family, tracked only through the three evaluations
needed for smooth division by the amplitude variable. -/
private structure SmoothEval (r : E → ℝ) (p : E → ℝ[X]) : Prop where
  zero : ContDiff ℝ ∞ (fun x => (p x).coeff 0)
  value : ContDiff ℝ ∞ (fun x => (p x).eval (r x))
  quotient : ContDiff ℝ ∞ (fun x => (p x).divX.eval (r x))

private theorem smoothEval_C {r a : E → ℝ} (ha : ContDiff ℝ ∞ a) :
    SmoothEval r (fun x => C (a x)) := by
  constructor
  · simpa using ha
  · simpa using ha
  · simpa using (contDiff_const : ContDiff ℝ ∞ (fun _ : E => (0 : ℝ)))

private theorem smoothEval_X {r : E → ℝ} (hr : ContDiff ℝ ∞ r) :
    SmoothEval r (fun _ => X) := by
  have hx : (X : ℝ[X]).divX = 1 := by
    simpa using (divX_X_pow (R := ℝ) (n := 1))
  constructor
  · simpa using (contDiff_const : ContDiff ℝ ∞ (fun _ : E => (0 : ℝ)))
  · simpa using hr
  · simpa [hx] using (contDiff_const : ContDiff ℝ ∞ (fun _ : E => (1 : ℝ)))

private theorem SmoothEval.add {r : E → ℝ} {p q : E → ℝ[X]}
    (hp : SmoothEval r p) (hq : SmoothEval r q) :
    SmoothEval r (fun x => p x + q x) := by
  constructor
  · simpa using hp.zero.add hq.zero
  · simpa using hp.value.add hq.value
  · simpa [divX_add] using hp.quotient.add hq.quotient

private theorem SmoothEval.mul {r : E → ℝ} {p q : E → ℝ[X]}
    (hp : SmoothEval r p) (hq : SmoothEval r q) :
    SmoothEval r (fun x => p x * q x) := by
  constructor
  · simpa using hp.zero.mul hq.zero
  · simpa using hp.value.mul hq.value
  · simpa [divX_mul_formula] using
      (hp.quotient.mul hq.value).add (hp.zero.mul hq.quotient)

private theorem SmoothEval.pow {r : E → ℝ} {p : E → ℝ[X]}
    (hp : SmoothEval r p) (n : ℕ) : SmoothEval r (fun x => p x ^ n) := by
  induction n with
  | zero => simpa using (smoothEval_C (r := r) (a := fun _ => 1) contDiff_const)
  | succ n ih => simpa [pow_succ] using ih.mul hp

private theorem smoothEval_sum {r : E → ℝ} {ι : Type*}
    (s : Finset ι) (p : ι → E → ℝ[X]) (hp : ∀ i ∈ s, SmoothEval r (p i)) :
    SmoothEval r (fun x => ∑ i ∈ s, p i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (smoothEval_C (r := r) (a := fun _ => 0) contDiff_const)
  | @insert i s hi ih =>
    simpa [Finset.sum_insert hi] using
      (hp i (Finset.mem_insert_self ..)).add (ih (fun j hj => hp j (Finset.mem_insert_of_mem hj)))

private theorem smoothEval_prod {r : E → ℝ} {ι : Type*}
    (s : Finset ι) (p : ι → E → ℝ[X]) (hp : ∀ i ∈ s, SmoothEval r (p i)) :
    SmoothEval r (fun x => ∏ i ∈ s, p i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (smoothEval_C (r := r) (a := fun _ => 1) contDiff_const)
  | @insert i s hi ih =>
    simpa [Finset.prod_insert hi] using
      (hp i (Finset.mem_insert_self ..)).mul (ih (fun j hj => hp j (Finset.mem_insert_of_mem hj)))

end Families

/-- The amplitude extension is jointly smooth, including at amplitude zero. -/
theorem amplitudeField_contDiff :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ × State => amplitudeField p.1 p.2.1 p.2.2) := by
  have hr : ContDiff ℝ ∞ (fun p : ℝ × ℝ × State => p.2.1) := by fun_prop
  have hm (j : Fin 5) : SmoothEval (fun p : ℝ × ℝ × State => p.2.1)
      (fun p => pathMonomial p.2.2 j) := by
    apply smoothEval_prod
    intro i _
    apply SmoothEval.pow
    apply SmoothEval.add
    · simpa using (smoothEval_C (r := fun p : ℝ × ℝ × State => p.2.1)
        (a := fun _ => 1) contDiff_const)
    · exact (smoothEval_X hr).mul (smoothEval_C (by fun_prop))
  apply contDiff_pi.mpr
  intro i
  have hc (j : Fin 5) : ContDiff ℝ ∞
      (fun p : ℝ × ℝ × State => normalizedCoefficient p.1 i j) := by
    fin_cases i <;>
      norm_num [normalizedCoefficient, equilibrium, div_div_eq_mul_div] <;> fun_prop
  exact (smoothEval_sum Finset.univ
    (fun j (p : ℝ × ℝ × State) => C (normalizedCoefficient p.1 i j) * pathMonomial p.2.2 j)
    (fun j _ => (smoothEval_C (hc j)).mul (hm j))).quotient

end OscillatoryCores
