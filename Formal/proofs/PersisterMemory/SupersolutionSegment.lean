import proofs.PersisterMemory.BudgetBarrier

namespace PersisterMemory
open Source
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.cons_val_four
  Matrix.vecHead Matrix.vecTail

theorem segment_identity (e a : ℚ) (q : Fin 6 → ℚ) (i : Fin 6) :
    pgfResidual e (fun j => 1-a*(1-q j)) i =
    a*pgfResidual e q i-a*(1-a)*daughterPair (fun j => 1-q j) i/10 := by
  fin_cases i <;> simp [pgfResidual,molecular,daughterPair,death] <;> ring

theorem erasure_segment (a : ℚ) (q : Fin 6 → ℚ) (i : Fin 6) :
    erasureAction (fun j => 1-a*(1-q j)) i = a*erasureAction q i := by
  fin_cases i <;> simp [erasureAction] <;> ring

theorem segment_sign (a p d : ℝ) (ha : 0 ≤ a) (ha' : a ≤ 1)
    (hp : p ≤ 0) (hd : 0 ≤ d) : a*p-a*(1-a)*d ≤ 0 := by
  have h1 := mul_nonpos_of_nonneg_of_nonpos ha hp
  have h2 := mul_nonneg (mul_nonneg ha (sub_nonneg.mpr ha')) hd
  linarith

end PersisterMemory
