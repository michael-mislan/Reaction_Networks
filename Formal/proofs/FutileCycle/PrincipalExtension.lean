import proofs.DUnstableCores.DScaling

namespace FutileCycle
open Matrix

def padded {I : Type*} (A : Matrix I I ℂ) (p : I → Prop) [DecidablePred p] :
    Matrix I I ℂ := fun i j => if p i ∧ p j then A i j else 0

theorem principal_eigenpair_extends {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (p : I → Prop) [DecidablePred p]
    (z : ℂ) (v : {i // p i} → ℂ) (hv : v ≠ 0)
    (he : A.submatrix Subtype.val Subtype.val *ᵥ v = z • v) :
    ∃ w : I → ℂ, w ≠ 0 ∧ padded A p *ᵥ w = z • w := by
  classical
  let w : I → ℂ := fun i => if h : p i then v ⟨i,h⟩ else 0
  refine ⟨w, ?_, ?_⟩
  · intro hw
    apply hv
    funext i
    have hh := congrFun hw i.val
    simpa [w, i.property] using hh
  · ext i
    by_cases hi : p i
    · have ht : ∀ j, padded A p i j * w j =
          if h : p j then A i j * v ⟨j,h⟩ else 0 := by
        intro j
        by_cases hj : p j <;> simp [padded, w, hi, hj]
      change (∑ j, padded A p i j * w j) = z * w i
      simp_rw [ht]
      rw [← (Equiv.sumCompl p).sum_comp]
      have hpos : ∀ j : {j // p j}, p j.val := fun j => j.property
      have hneg : ∀ j : {j // ¬p j}, ¬p j.val := fun j => j.property
      simpa [w, hi, Matrix.mulVec, dotProduct, hpos, hneg] using congrFun he ⟨i,hi⟩
    · simp [padded, Matrix.mulVec, dotProduct, hi, w]

end FutileCycle
