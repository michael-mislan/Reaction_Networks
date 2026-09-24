import proofs.FutileCycle.IntermediateElimination
import proofs.FutileCycle.FlowerMinimality

namespace FutileCycle
open Matrix

abbrev FlowerIndex (k : ℕ) := Fin (k+1) ⊕ Unit

def cycleReduced (k : ℕ) : Matrix (Fin (k+1)) (Fin (k+1)) ℤ :=
  fun i j => if i=0 then (if j = Fin.last k then 1 else 0)
    else (if j.val+1=i.val then 1 else 0) - (if j=i then 1 else 0)

def flowerSpoke (k : ℕ) : Matrix (Fin (k+1)) Unit ℤ :=
  fun i _ => if i=0 then 1 else 0

def flowerMatrix (k : ℕ) : Matrix (FlowerIndex k) (FlowerIndex k) ℤ :=
  fromBlocks (cycleReduced k - flowerSpoke k * (flowerSpoke k).transpose)
    (flowerSpoke k) (flowerSpoke k).transpose (-1)

theorem cycleReduced_det (k : ℕ) : (cycleReduced k).det = (-1)^k := by
  rw [det_succ_row_zero]
  have hminor : ((cycleReduced k).submatrix Fin.succ (Fin.last k).succAbove).det = 1 := by
    rw [det_of_upperTriangular]
    · simp [cycleReduced, submatrix, Fin.ext_iff]
    · intro i j hij
      change j < i at hij
      simp only [cycleReduced, submatrix, Fin.succAbove_last]
      have hne : j.val ≠ i.val := by omega
      have hne' : j.val ≠ i.val+1 := by omega
      simp [Fin.ext_iff, hne, hne']
  simp only [cycleReduced]
  rw [Finset.sum_eq_single (Fin.last k)]
  · simpa using congrArg (fun t : ℤ => (-1)^k*t) hminor
  · intro j _ hj
    simp [hj]
  · simp

theorem flowerMatrix_det (k : ℕ) : (flowerMatrix k).det = (-1)^(k+1) := by
  rw [flowerMatrix, det_intermediate_elimination]
  simp only [sub_add_cancel, Fintype.card_unique, pow_one, cycleReduced_det]
  rw [pow_succ, mul_comm]

end FutileCycle
