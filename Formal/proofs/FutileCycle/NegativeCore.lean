import proofs.FutileCycle.NegativeMinimality
import proofs.FutileCycle.NegativeEmbedding
import proofs.FutileCycle.NegativeDeterminant

namespace FutileCycle
open DUnstableCores

def MinimalUnstable {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℝ) : Prop :=
  HurwitzUnstable A ∧ ∀ s : Finset I, s ≠ Finset.univ →
    HurwitzNonpositive (A.submatrix (fun i : s => i.val) (fun i : s => i.val))

theorem negative_minimal : MinimalUnstable negativeRealMatrix := by
  refine ⟨negative_unstable, ?_⟩
  intro s hs
  have hp : ∃ i : Fin 6, i ∉ s := by
    by_contra hh
    push Not at hh
    exact hs (Finset.eq_univ_of_forall hh)
  rintro ⟨z,v,hz,hv,he⟩
  apply negative_principal_no_rhp (fun i => i ∈ s) hp z v hv _ hz
  funext i
  calc
    _ = (complexify (negativeRealMatrix.submatrix (fun j : s => j.val)
        (fun j : s => j.val))).mulVec v i := by
      unfold Matrix.mulVec dotProduct
      apply Finset.sum_congr
      · ext j; simp
      · intro j _; rfl
    _ = _ := he i

/-- A literal six-species unstable-negative core exists in every n≥3 source. -/
theorem negative_core_all_n (n : ℕ) (hn : 3 ≤ n) :
    ∃ J : Child (futile n) (Fin 6), J.matrix.det = 1 ∧
      MinimalUnstable (J.matrix.map (fun x : ℤ => (x : ℝ))) := by
  refine ⟨negativeChildAt n hn, ?_, ?_⟩
  · rw [negativeChildAt_matrix, negativeMatrix_det]
  · rw [negativeChildAt_matrix]
    exact negative_minimal

end FutileCycle
