import proofs.FutileCycle.Source

namespace FutileCycle

open Matrix

/-- Integral elimination: no inverse and no nonsingularity assumption. -/
theorem det_intermediate_elimination {U V : Type*} [Fintype U] [Fintype V]
    [DecidableEq U] [DecidableEq V] (B : Matrix U U ℤ) (W : Matrix U V ℤ)
    (C : Matrix V U ℤ) :
    (fromBlocks B W C (-1)).det = (-1) ^ Fintype.card V * (B + W * C).det := by
  have hmul : fromBlocks B W C (-1) * fromBlocks 1 0 C 1 =
      fromBlocks (B + W * C) W 0 (-1) := by
    simp [fromBlocks_multiply]
  have hdet := congrArg Matrix.det hmul
  simpa [det_mul, det_fromBlocks_zero₁₂, det_fromBlocks_zero₂₁, det_neg,
    mul_comm] using hdet

end FutileCycle
