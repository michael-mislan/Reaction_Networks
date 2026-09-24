import proofs.InheritedCellAssay.PositiveMoments
import proofs.CompositionalMemory.FiniteTimeDependentCertificate
import Mathlib.Tactic.FinCases

namespace InheritedCellAssay.PositiveMoments
open FiniteCopy CompositionalMemory

/-- After removing common growth exp(t/10), the first-moment system is
    a killed two-type Markov chain. States are sensitive, resistant, cemetery. -/
noncomputable def momentChain : FiniteJumpModel (Fin 3) Bool where
  next n b := if n = 0 then (if b then 1 else 2)
    else if n = 1 then (if b then 0 else 2) else 2
  rate n b := if n = 0 then (if b then 1/1000 else 2/5)
    else if n = 1 then (if b then 1/100000 else 0) else 0
  nonneg n b := by split_ifs <;> norm_num

def sensitiveIndicator (n : Fin 3) : ℝ := if n = 0 then 1 else 0
def resistantIndicator (n : Fin 3) : ℝ := if n = 1 then 1 else 0

noncomputable def momentLaw (t : ℝ) (f : Fin 3 → ℝ) : ℝ :=
  (19/24)*(NormedSpace.exp (t • jumpGeneratorMatrix momentChain)).mulVec f 0+
  (5/24)*(NormedSpace.exp (t • jumpGeneratorMatrix momentChain)).mulVec f 1

theorem momentLaw_linear (t a b : ℝ) (f g : Fin 3 → ℝ) :
    momentLaw t (fun n => a*f n+b*g n) = a*momentLaw t f+b*momentLaw t g := by
  simp only [momentLaw, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

theorem sensitive_generator : momentChain.generator sensitiveIndicator =
    fun n => -(401/1000)*sensitiveIndicator n+(1/100000)*resistantIndicator n := by
  funext n
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  fin_cases n <;> norm_num [FiniteJumpModel.generator, momentChain,
    sensitiveIndicator, resistantIndicator, h20, h21]

theorem resistant_generator : momentChain.generator resistantIndicator =
    fun n => (1/1000)*sensitiveIndicator n-(1/100000)*resistantIndicator n := by
  funext n
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  fin_cases n <;> norm_num [FiniteJumpModel.generator, momentChain,
    sensitiveIndicator, resistantIndicator, h20, h21]

theorem momentLaw_derivative (f : Fin 3 → ℝ) (t : ℝ) :
    HasDerivAt (fun s => momentLaw s f) (momentLaw t (momentChain.generator f)) t := by
  have hd (n : Fin 3) := finite_dynamic_expectation_derivative momentChain
    (fun _ => f) (fun _ _ => 0) t (fun y => hasDerivAt_const t (f y)) n
  simpa only [zero_add, momentLaw] using
    ((hd 0).const_mul (19/24)).add ((hd 1).const_mul (5/24))

theorem momentLaw_nonneg (f : Fin 3 → ℝ) (hf : ∀ n, 0 ≤ f n ∧ f n ≤ 1)
    (t : ℝ) (ht : 0 ≤ t) : 0 ≤ momentLaw t f := by
  have h0 := (finite_time_bounds momentChain ⟨t,ht⟩ f hf 0).1
  have h1 := (finite_time_bounds momentChain ⟨t,ht⟩ f hf 1).1
  change 0 ≤ (19/24)*finiteTimeExpectation momentChain ⟨t,ht⟩ f 0+
    (5/24)*finiteTimeExpectation momentChain ⟨t,ht⟩ f 1
  positivity

noncomputable def constructedMoments : MomentODE where
  S t := Real.exp ((1/10)*t)*momentLaw t sensitiveIndicator
  R t := Real.exp ((1/10)*t)*momentLaw t resistantIndicator
  initialS := by norm_num [momentLaw, sensitiveIndicator]
  initialR := by norm_num [momentLaw, resistantIndicator]
  derivS t := by
    have he : HasDerivAt (fun s : ℝ => Real.exp ((1/10)*s))
        ((1/10)*Real.exp ((1/10)*t)) t := by
      convert ((hasDerivAt_id t).const_mul (1/10)).exp using 1
      simp only [id_eq]
      ring
    have hh := he.mul (momentLaw_derivative sensitiveIndicator t)
    rw [sensitive_generator, momentLaw_linear] at hh
    convert hh using 1
    ring
  derivR t := by
    have he : HasDerivAt (fun s : ℝ => Real.exp ((1/10)*s))
        ((1/10)*Real.exp ((1/10)*t)) t := by
      convert ((hasDerivAt_id t).const_mul (1/10)).exp using 1
      simp only [id_eq]
      ring
    have hh := he.mul (momentLaw_derivative resistantIndicator t)
    rw [resistant_generator] at hh
    have hg : (fun n => (1/1000)*sensitiveIndicator n-(1/100000)*resistantIndicator n) =
        (fun n => (1/1000)*sensitiveIndicator n+(-(1/100000))*resistantIndicator n) := by
      funext n
      ring
    rw [hg, momentLaw_linear] at hh
    convert hh using 1
    ring
  nonnegS t ht := mul_nonneg (Real.exp_nonneg _) (momentLaw_nonneg sensitiveIndicator
    (fun n => by unfold sensitiveIndicator; split_ifs <;> norm_num) t ht)
  nonnegR t ht := mul_nonneg (Real.exp_nonneg _) (momentLaw_nonneg resistantIndicator
    (fun n => by unfold resistantIndicator; split_ifs <;> norm_num) t ht)

end InheritedCellAssay.PositiveMoments
