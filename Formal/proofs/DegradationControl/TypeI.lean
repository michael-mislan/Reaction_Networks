import proofs.DegradationControl.Reaction

namespace DegradationControl

def typeIForward (k m : ℝ) : UnaryReaction (Fin 2) where
  substrate := 0
  products := fun i => if i = 1 then m else 0
  rate := k

def typeIReturn (k : ℝ) : UnaryReaction (Fin 2) where
  substrate := 1
  products := fun i => if i = 0 then 1 else 0
  rate := k

/-- Exact source-derived matrix for `X₀ -> m X₁`, `X₁ -> X₀`, with
species-wise degradation. -/
def typeISourceMatrix (k₁ k₂ m d₁ d₂ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (typeIForward k₁ m).matrix + (typeIReturn k₂).matrix +
    degradationMatrix ![d₁, d₂]

theorem typeISourceMatrix_eq (k₁ k₂ m d₁ d₂ : ℝ) :
    typeISourceMatrix k₁ k₂ m d₁ d₂ =
      ![![-(k₁ + d₁), k₂], ![m * k₁, -(k₂ + d₂)]] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [typeISourceMatrix, typeIForward, typeIReturn, UnaryReaction.matrix,
      degradationMatrix] <;> ring

/-- The exact threshold polynomial obtained from the source matrix. -/
theorem typeI_threshold_polynomial (k₁ k₂ m d₁ d₂ : ℝ) :
    (-(k₁ + d₁)) * (-(k₂ + d₂)) - k₂ * (m * k₁) =
      (k₁ + d₁) * (k₂ + d₂) - m * k₁ * k₂ := by
  ring

/-- At equality, the advertised positive-vector coordinates form an exact
zero-eigenvalue certificate. -/
theorem typeI_critical_vector
    (k₁ k₂ m d₁ d₂ v₀ v₁ : ℝ)
    (h0 : -(k₁ + d₁) * v₀ + k₂ * v₁ = 0)
    (h1 : m * k₁ * v₀ - (k₂ + d₂) * v₁ = 0) :
    Matrix.mulVec (typeISourceMatrix k₁ k₂ m d₁ d₂) ![v₀, v₁] = 0 := by
  rw [typeISourceMatrix_eq]
  ext i
  fin_cases i
  · simpa [Matrix.mulVec, Fin.sum_univ_two] using h0
  · have h1' : m * k₁ * v₀ + (-d₂ + -k₂) * v₁ = 0 := by
      calc
        m * k₁ * v₀ + (-d₂ + -k₂) * v₁ =
            m * k₁ * v₀ - (k₂ + d₂) * v₁ := by ring
        _ = 0 := h1
    simpa [Matrix.mulVec, Fin.sum_univ_two] using h1'

end DegradationControl
