import proofs.CompositionalMemory.MatrixBilinearEnergy

namespace CompositionalMemory
open Matrix

theorem matrix_energy_matrix_add {N : ℕ} (P Q : Matrix (Fin N) (Fin N) ℝ) (x : Fin N → ℝ) :
    matrixEnergy (P+Q) x=matrixEnergy P x+matrixEnergy Q x := by
  simp [matrixEnergy,add_mul,Finset.sum_add_distrib]

theorem matrix_energy_identity {N : ℕ} (x : Fin N → ℝ) :
    matrixEnergy (1 : Matrix (Fin N) (Fin N) ℝ) x=vectorSquares x := by
  rw [matrixEnergy_dotProduct,Matrix.one_mulVec]
  simp only [dotProduct,vectorSquares,pow_two]

theorem lyapunov_matrix_energy {N : ℕ} (P Pd J : Matrix (Fin N) (Fin N) ℝ)
    (hp : ∀ i j,P i j=P j i) (x : Fin N → ℝ) :
    matrixEnergy (Pd+J.transpose*P+P*J+(1 : Matrix (Fin N) (Fin N) ℝ)) x=
      matrixEnergy Pd x+2*P.toBilin' x (J.mulVec x)+vectorSquares x := by
  have hleft : matrixEnergy (J.transpose*P) x=P.toBilin' x (J.mulVec x) := by
    rw [matrixEnergy_dotProduct,← Matrix.mulVec_mulVec,Matrix.dotProduct_transpose_mulVec,dotProduct_comm,
      ← Matrix.toBilin'_apply',matrix_bilinear_symmetric P hp]
  have hright : matrixEnergy (P*J) x=P.toBilin' x (J.mulVec x) := by
    rw [matrixEnergy_dotProduct,← Matrix.mulVec_mulVec,Matrix.toBilin'_apply']
  rw [matrix_energy_matrix_add (Pd+J.transpose*P+P*J) 1 x,
    matrix_energy_matrix_add (Pd+J.transpose*P) (P*J) x,
    matrix_energy_matrix_add Pd (J.transpose*P) x,matrix_energy_identity,hleft,hright]
  ring

/-- Algebraic source of the restoring term and the two explicit errors.
The polynomial residual check supplies the matrix on the right. -/
theorem quadratic_recovery_identity {N : ℕ} (P Pd J : Matrix (Fin N) (Fin N) ℝ)
    (hp : ∀ i j,P i j=P j i) (x f f0 zd rem : Fin N → ℝ)
    (hf : f=f0+J.mulVec x+rem) :
    matrixEnergy Pd x+2*P.toBilin' x (f-zd)=
      -vectorSquares x+matrixEnergy (Pd+J.transpose*P+P*J+(1 : Matrix (Fin N) (Fin N) ℝ)) x+
        2*P.toBilin' x (f0-zd)+2*P.toBilin' x rem := by
  rw [hf,lyapunov_matrix_energy P Pd J hp x]
  simp only [map_add,map_sub]
  ring

theorem energy_derivative_expression {N : ℕ} (P Pd : Matrix (Fin N) (Fin N) ℝ)
    (hp : ∀ i j,P i j=P j i) (x zd : Fin N → ℝ) :
    (∑ i,∑ j,((Pd i j*x i+P i j*(-zd i))*x j+(P i j*x i)*(-zd j)))=
      matrixEnergy Pd x-2*P.toBilin' x zd := by
  have hs : (∑ i,∑ j,P i j*zd i*x j)=(∑ i,∑ j,P i j*x i*zd j) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hp j i]
    ring
  have hb : P.toBilin' x zd=(∑ i,∑ j,P i j*x i*zd j) := by
    simp only [Matrix.toBilin'_apply]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp only [add_mul,mul_neg,neg_mul,Finset.sum_add_distrib,Finset.sum_neg_distrib]
  rw [hs,hb]
  unfold matrixEnergy
  ring

theorem hasDerivAt_matrix_energy {N : ℕ} (P : ℝ → Matrix (Fin N) (Fin N) ℝ)
    (z : ℝ → Fin N → ℝ) (Pd : Matrix (Fin N) (Fin N) ℝ) (zd n : Fin N → ℝ) (t : ℝ)
    (hp : ∀ i j,P t i j=P t j i)
    (hdP : ∀ i j,HasDerivAt (fun u => P u i j) (Pd i j) t)
    (hdz : ∀ j,HasDerivAt (fun u => z u j) (zd j) t) :
    HasDerivAt (fun u => matrixEnergy (P u) (n-z u))
      (matrixEnergy Pd (n-z t)-2*(P t).toBilin' (n-z t) zd) t := by
  have hd (j : Fin N) := (hasDerivAt_const t (n j)).sub (hdz j)
  simp only [zero_sub] at hd
  have hs := HasDerivAt.sum (u := Finset.univ) (fun i _ =>
    HasDerivAt.sum (u := Finset.univ) (fun j _ => ((hdP i j).mul (hd i)).mul (hd j)))
  convert hs using 1
  · funext u
    simp only [matrixEnergy,Finset.sum_apply,Pi.mul_apply,Pi.sub_apply]
  · simpa only [Pi.sub_apply,Pi.mul_apply] using (energy_derivative_expression (P t) Pd hp (n-z t) zd).symm

end CompositionalMemory
