import proofs.FutileCycle.ReciprocalInstability
import proofs.FutileCycle.NegativeCore
import proofs.FutileCycle.FlowerScaledMinimality

namespace FutileCycle
noncomputable section
open Polynomial Matrix DUnstableCores

theorem rhp_of_log_derivative (p : ℂ[X]) (t : ℂ) (ht : t.re=0)
    (hp : p.eval t ≠ 0) (hn : (p.derivative.eval t / p.eval t).re < 0) :
    ∃ z, p.IsRoot z ∧ 0 < z.re := by
  classical
  by_contra h
  push Not at h
  have hroot : ∀ z ∈ p.roots, z.re ≤ 0 := by
    intro z hz
    exact h z ((mem_roots (by intro he; simp [he] at hp)).mp hz)
  have hh := congrArg Complex.re
    ((IsAlgClosed.splits p).eval_derivative_div_eval_of_ne_zero hp)
  have hsum : 0 ≤ (p.roots.map (fun z => (1/(t-z):ℂ).re)).sum := by
    apply Multiset.sum_nonneg
    intro x hx
    obtain ⟨z,hz,rfl⟩ := Multiset.mem_map.mp hx
    simp only [one_div, Complex.inv_re, Complex.sub_re, ht, zero_sub]
    exact div_nonneg (neg_nonneg.mpr (hroot z hz)) (Complex.normSq_nonneg _)
  simp only [re_multiset_sum, Multiset.map_map, Function.comp_def] at hh
  linarith

def negativeFive : Matrix (Fin 5) (Fin 5) ℝ :=
  !![-1,0,0,-1,0; 0,-1,0,0,1; -1,0,-1,0,1;
    0,-1,0,-1,0; 0,0,1,0,-1]

def negativeFiveScale : Fin 5 → ℝ := ![1,1,2,1,2]

def negativeFivePolynomial : ℂ[X] := X^5+C 7*X^4+C 15*X^3+C 13*X^2+C 4*X+C 4

theorem negativeFivePolynomial_rhp : ∃ z, negativeFivePolynomial.IsRoot z ∧ 0 < z.re := by
  apply rhp_of_log_derivative negativeFivePolynomial ((3/5:ℂ)*Complex.I)
  · norm_num
  · intro h
    have hh := congrArg Complex.re h
    norm_num [negativeFivePolynomial, pow_succ, Complex.mul_re, Complex.mul_im] at hh
  · norm_num [negativeFivePolynomial, derivative_add, derivative_mul, derivative_pow,
      Complex.div_re, Complex.normSq_apply, pow_succ, Complex.mul_re, Complex.mul_im]

theorem negativeFive_scaled_unstable :
    HurwitzUnstable (rightScale negativeFive negativeFiveScale) := by
  obtain ⟨z,hz,hre⟩ := negativeFivePolynomial_rhp
  let w := z+1
  let v : Fin 5 → ℂ := ![4,4*w^2,(z+2)*w^3,-4*w,2*w^3]
  refine ⟨z,v,hre,?_,?_⟩
  · intro hh
    have h0 := congrFun hh 0
    norm_num [v] at h0
  · intro i
    have hp : z^5+7*z^4+15*z^3+13*z^2+4*z+4=0 := by
      simpa [negativeFivePolynomial, Polynomial.IsRoot] using hz
    fin_cases i <;>
      simp [negativeFive, negativeFiveScale, rightScale, complexify, Matrix.mulVec,
        dotProduct, Fin.sum_univ_succ, v, w]
    all_goals first | (ring_nf; done) | linear_combination -hp

theorem negativeFive_dUnstable : DUnstable negativeFive := by
  refine ⟨negativeFiveScale,?_,negativeFive_scaled_unstable⟩
  intro i
  fin_cases i <;> norm_num [negativeFiveScale]

end
end FutileCycle
