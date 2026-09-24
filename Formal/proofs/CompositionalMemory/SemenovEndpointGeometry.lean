import proofs.CompositionalMemory.SemenovNoiseBounds
import proofs.CompositionalMemory.MatrixBilinearEnergy

namespace CompositionalMemory.Semenov
open Matrix

theorem congruence_energy_nonneg (M A : Matrix (Fin 8) (Fin 8) ℝ)
    (hA : A.det ≠ 0) (hAn : 0 < frobeniusSquared A)
    (hs : ∀ i j,(A*M*A.transpose) i j=(A*M*A.transpose) j i)
    (hd : ∀ i,(1/2 : ℝ) ≤ (A*M*A.transpose) i i-
      ∑ j,if j=i then 0 else |(A*M*A.transpose) i j|) (v : Fin 8 → ℝ) :
    0 ≤ matrixEnergy M v := by
  have hh := whitened_metric_coercivity M A hA (1/2) (by norm_num)
    (matrix_energy_diagonal_lower _ hs (1/2) hd) v
  exact (mul_nonneg_iff_of_pos_left hAn).mp
    ((mul_nonneg (by norm_num : (0 : ℝ) ≤ 1/2) (vectorSquares_nonneg v)).trans hh)

theorem rational_congruence_nonneg (M A : Matrix (Fin 8) (Fin 8) ℚ)
    (htri : ∀ i j,i<j → A i j=0) (hdiag : ∀ i,0<A i i)
    (hnorm : 0 < ∑ i,∑ j,(A i j)^2) (hsym : ∀ i j,M i j=M j i)
    (hG : ∀ i,(1/2 : ℚ) ≤ (A*M*A.transpose) i i-
      ∑ j,if j=i then 0 else |(A*M*A.transpose) i j|) (v : Fin 8 → ℝ) :
    0 ≤ matrixEnergy (rationalMatrix M) v := by
  have hA : (rationalMatrix A).det ≠ 0 := lower_triangular_det_ne_zero _
    (fun i j hij => by change (A i j : ℝ)=0; exact_mod_cast htri i j hij)
    (fun i => by change (0 : ℝ) < A i i; exact_mod_cast hdiag i)
  have hAn : 0 < frobeniusSquared (rationalMatrix A) := by
    unfold frobeniusSquared rationalMatrix
    exact_mod_cast hnorm
  have hM : (rationalMatrix M).transpose=rationalMatrix M := by
    ext i j
    exact congrArg (fun q : ℚ => (q : ℝ)) (hsym j i)
  have hGt : (rationalMatrix A*rationalMatrix M*(rationalMatrix A).transpose).transpose=
      rationalMatrix A*rationalMatrix M*(rationalMatrix A).transpose := by
    simp only [Matrix.transpose_mul,Matrix.transpose_transpose,hM,Matrix.mul_assoc]
  have hcast : rationalMatrix (A*M*A.transpose)=
      rationalMatrix A*rationalMatrix M*(rationalMatrix A).transpose := by
    ext i j
    simp only [rationalMatrix,Matrix.mul_apply,Matrix.transpose_apply,Rat.cast_sum,Rat.cast_mul]
  apply congruence_energy_nonneg _ _ hA hAn (fun i j => congrFun (congrFun hGt j) i) ?_ v
  intro i
  rw [← hcast]
  change (1/2 : ℝ) ≤ ((A*M*A.transpose) i i : ℝ)-
    ∑ j,if j=i then 0 else |((A*M*A.transpose) i j : ℝ)|
  have hh := Rat.cast_mono (K := ℝ) (hG i)
  simpa only [Rat.cast_sub,Rat.cast_sum,apply_ite,Rat.cast_zero,
    Rat.cast_abs,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using hh

theorem refill_energy_comparison (P0 PT : Matrix (Fin 8) (Fin 8) ℝ) (r : ℝ)
    (hM : ∀ v,0 ≤ matrixEnergy (fun i j => r*PT i j-P0 i j/4) v) (v : Fin 8 → ℝ) :
    matrixEnergy P0 ((1/2 : ℝ) • v) ≤ r*matrixEnergy PT v := by
  have he : matrixEnergy (fun i j => r*PT i j-P0 i j/4) v=
      r*matrixEnergy PT v-matrixEnergy P0 ((1/2 : ℝ) • v) := by
    simp only [matrixEnergy,Pi.smul_apply,smul_eq_mul,Finset.mul_sum,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hh := hM v
  rw [he] at hh
  linarith only [hh]

theorem terminal_total_upper (z n : Fin 8 → ℝ) (radius : ℝ) (hr : 0 ≤ radius)
    (hx : vectorSquares (n-z) ≤ radius^2) :
    (∑ i,n i) ≤ (∑ i,z i)+8*radius := by
  have hi (i : Fin 8) : n i ≤ z i+radius := by
    have hh := (abs_le.mp (coordinate_deviation_bound (n-z) radius hr hx i)).2
    change n i-z i ≤ radius at hh
    linarith only [hh]
  simpa only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat]
    using Finset.sum_le_sum (s := Finset.univ) (fun i _ => hi i)

theorem terminal_thiol_bounds (z n : Fin 8 → ℝ) (radius : ℝ) (hr : 0 ≤ radius)
    (hx : vectorSquares (n-z) ≤ radius^2) :
    z 1+z 2+z 3-3*radius ≤ n 1+n 2+n 3 ∧
      n 1+n 2+n 3 ≤ z 1+z 2+z 3+3*radius := by
  have h1 := abs_le.mp (coordinate_deviation_bound (n-z) radius hr hx 1)
  have h2 := abs_le.mp (coordinate_deviation_bound (n-z) radius hr hx 2)
  have h3 := abs_le.mp (coordinate_deviation_bound (n-z) radius hr hx 3)
  simp only [Pi.sub_apply] at h1 h2 h3
  constructor <;> linarith only [h1.1,h1.2,h2.1,h2.2,h3.1,h3.2]

end CompositionalMemory.Semenov
