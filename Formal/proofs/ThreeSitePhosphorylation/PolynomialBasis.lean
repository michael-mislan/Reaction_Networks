import Mathlib

namespace ThreeSitePhosphorylation
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 100000

def powerVector (z : ℂ) : Fin 9 → ℂ := fun j => z^(j:ℕ)

theorem matrix_eq_of_powerVector (M N : Matrix (Fin 9) (Fin 9) ℂ)
    (h : ∀ z : ℂ, M.mulVec (powerVector z) = N.mulVec (powerVector z)) : M=N := by
  ext i j
  let p : Polynomial ℂ := ∑ k : Fin 9, Polynomial.C (M i k-N i k)*Polynomial.X^(k:ℕ)
  have he : p=0 := by
    apply Polynomial.funext
    intro z
    have hh := congrFun (h z) i
    simpa [p,Polynomial.eval_finsetSum,Matrix.mulVec,dotProduct,powerVector,
      sub_mul,Finset.sum_sub_distrib] using sub_eq_zero.mpr hh
  have hc := congrArg (fun f : Polynomial ℂ => f.coeff (j:ℕ)) he
  simp only [p, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
    Polynomial.coeff_zero, Fin.val_inj] at hc
  exact sub_eq_zero.mp (by simpa using hc)

end
end ThreeSitePhosphorylation
