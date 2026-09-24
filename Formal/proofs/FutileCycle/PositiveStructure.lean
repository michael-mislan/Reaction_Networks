import proofs.FutileCycle.PositiveSource
import proofs.FutileCycle.FlowerMatrix

namespace FutileCycle

set_option maxRecDepth 4000
set_option maxHeartbeats 1600000

def positiveSign (n : ℕ) : PositiveIndex n → ℤ
  | .inl i => if i=0 then -1 else 1
  | .inr _ => -1

theorem positiveSign_sq (n : ℕ) (i : PositiveIndex n) :
    positiveSign n i * positiveSign n i = 1 := by
  cases i with
  | inl i => dsimp [positiveSign]; split_ifs <;> norm_num
  | inr i => norm_num [positiveSign]

/-- The signed source adapter; both rows and their owned columns are conjugated. -/
theorem positive_source_flower (n : ℕ) (hn : 2 ≤ n) (i j : PositiveIndex n) :
    (positiveChild n hn).matrix i j =
      positiveSign n i * flowerMatrix (2*n-1) i j * positiveSign n j := by
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      simp only [Child.matrix, positiveChild, positiveSpecies, positiveReactions,
        positiveSign, flowerMatrix, Matrix.fromBlocks_apply₁₁, Matrix.sub_apply,
        Matrix.mul_apply, Fintype.sum_unique, flowerSpoke, Matrix.transpose_apply]
      simp only [cycleReduced]
      simp only [Fin.ext_iff, Fin.val_zero, Fin.val_last]
      split_ifs <;> simp [stoich, product, reactant, futile, Fin.ext_iff] <;> (try split_ifs) <;> omega
    | inr j =>
      simp only [Child.matrix, positiveChild, positiveSpecies, positiveReactions,
        positiveSign, flowerMatrix, Matrix.fromBlocks_apply₁₂, flowerSpoke]
      simp only [Fin.ext_iff, Fin.val_zero]
      by_cases h0 : i.val=0
      · simp only [if_pos h0]
        norm_num [stoich, product, reactant, futile]
        simp
      · simp only [if_neg h0]
        by_cases ho : i.val%2=1
        · simp only [if_pos ho]
          have hv : (i.val+1)/2 ≠ 0 := by omega
          norm_num [stoich, product, reactant, futile, Fin.ext_iff, hv]
          simp
        · simp only [if_neg ho]
          norm_num [stoich, product, reactant, futile]
          simp
  | inr i =>
    cases j with
    | inl j =>
      simp only [Child.matrix, positiveChild, positiveSpecies, positiveReactions,
        positiveSign, flowerMatrix, Matrix.fromBlocks_apply₂₁, flowerSpoke,
        Matrix.transpose_apply]
      simp only [Fin.ext_iff, Fin.val_zero]
      split_ifs <;> simp [stoich, product, reactant, futile, Fin.ext_iff]
      omega
    | inr j =>
      cases i; cases j
      simp [Child.matrix, positiveChild, positiveSpecies, positiveReactions,
        positiveSign, flowerMatrix, stoich, product, reactant]

end FutileCycle

