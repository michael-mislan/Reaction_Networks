import Mathlib

namespace PhenotypeIdentification

/- Algebraic cancellation only; the source integral and its invertibility
are established conventionally in the paper. -/
theorem resolvent_generator_recovery {n : Type*} [Fintype n] [DecidableEq n]
    (A X H : Matrix n n ℝ) (l : ℝ)
    (hAX : A * X = 1) (hprod : (l • (1 : Matrix n n ℝ) - H) * A = l • 1) :
    l • (1-X) = H := by
  have hh : l • (1 : Matrix n n ℝ) - H = l • X := by
    calc
      l • (1 : Matrix n n ℝ) - H = (l • (1 : Matrix n n ℝ) - H) * (A * X) := by rw [hAX, Matrix.mul_one]
      _ = ((l • (1 : Matrix n n ℝ) - H) * A) * X := by rw [Matrix.mul_assoc]
      _ = l • X := by rw [hprod, Matrix.smul_mul, Matrix.one_mul]
  rw [smul_sub, ← hh]
  abel

theorem resolvent_exit_recovery {n k : Type*} [Fintype n] [DecidableEq n]
    (X R A : Matrix n n ℝ) (B D : Matrix n k ℝ) (l : ℝ)
    (hXA : X*A=1) (ha : A=l • R) (hd : D=R*B) :
    l • (X*D)=B := by
  calc
    l • (X*D) = (X*(l • R))*B := by
      rw [hd, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
    _ = B := by rw [← ha, hXA, Matrix.one_mul]

theorem direct_target_identity (l pS pT a b c d : ℝ)
    (hpS : pS ≠ 0) (hpT : pT ≠ 0) (hdet : a*d-b*c ≠ 0) :
    l * pT * (pS*b) / ((pS*a)*(pT*d)-(pS*b)*(pT*c)) =
    l*b/(a*d-b*c) := by
  have he : (pS*a)*(pT*d)-(pS*b)*(pT*c) = pS*pT*(a*d-b*c) := by ring
  rw [he]
  field_simp

end PhenotypeIdentification
