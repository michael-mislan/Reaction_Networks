import proofs.CompositionalMemory.SemenovPolynomialDrift
import proofs.CompositionalMemory.SemenovSixthDrift
import proofs.CompositionalMemory.SemenovCombinedGenerator

namespace CompositionalMemory.Semenov
open Matrix

noncomputable def pieceQuadratic (z : Fin 8 → QCoefficients) (P : Fin 8 → Fin 8 → QCoefficients)
    (scale : ℚ) (volume eta t : ℝ) (n : Fin 8 → ℕ) : ℝ :=
  matrixEnergy (polynomialMatrix P (-1+(scale : ℝ)*t))
    ((fun j => (n j : ℝ)/volume)-polynomialVector z (-1+(scale : ℝ)*t))/eta

noncomputable def pieceQuadraticSlope (z : Fin 8 → QCoefficients) (P : Fin 8 → Fin 8 → QCoefficients)
    (scale : ℚ) (volume eta t : ℝ) (n : Fin 8 → ℕ) : ℝ :=
  quadraticTimeSlope (polynomialMatrix P (-1+(scale : ℝ)*t))
    (polynomialMatrixSlope P scale (-1+(scale : ℝ)*t)) (polynomialVector z (-1+(scale : ℝ)*t))
    (polynomialVectorSlope z scale (-1+(scale : ℝ)*t)) (fun j => (n j : ℝ)/volume) eta

theorem piece_quadratic_derivative (z : Fin 8 → QCoefficients) (P : Fin 8 → Fin 8 → QCoefficients)
    (hp : ∀ i j,P i j=P j i) (scale : ℚ) (volume eta t : ℝ) (n : Fin 8 → ℕ) :
    HasDerivAt (fun u => pieceQuadratic z P scale volume eta u n)
      (pieceQuadraticSlope z P scale volume eta t n) t := by
  have hh := hasDerivAt_matrix_energy
    (fun u => polynomialMatrix P (-1+(scale : ℝ)*u))
    (fun u => polynomialVector z (-1+(scale : ℝ)*u))
    (polynomialMatrixSlope P scale (-1+(scale : ℝ)*t))
    (polynomialVectorSlope z scale (-1+(scale : ℝ)*t)) (fun j => (n j : ℝ)/volume) t
    (fun i j => congrArg (fun p => Polynomial.aeval (-1+(scale : ℝ)*t) (qpolynomial p)) (hp i j))
    (fun i j => time_polynomial_derivative (P i j) scale t)
    (fun j => time_polynomial_derivative (z j) scale t)
  exact hh.div_const eta

noncomputable def pieceCombinedEnergy {B K : ℕ}
    (z : Fin 8 → QCoefficients) (P : Fin 8 → Fin 8 → QCoefficients)
    (scale : ℚ) (volume eta m0 rate left t : ℝ) : ReactorState B K → ℝ :=
  reactorCombinedEnergy (fun n => (pieceQuadratic z P scale volume eta t n)^6) m0 rate (left+t)

noncomputable def pieceCombinedSlope {B K : ℕ}
    (z : Fin 8 → QCoefficients) (P : Fin 8 → Fin 8 → QCoefficients)
    (scale : ℚ) (volume eta m0 rate left t : ℝ) : ReactorState B K → ℝ
  | none => 0
  | some (n,c) =>
      6*(pieceQuadratic z P scale volume eta t (fun j => (n j).val))^5*
        pieceQuadraticSlope z P scale volume eta t (fun j => (n j).val)-
        8*rate*(c.val-(m0+rate*(left+t)))/(K : ℝ)^2

theorem piece_combined_derivative {B K : ℕ}
    (z : Fin 8 → QCoefficients) (P : Fin 8 → Fin 8 → QCoefficients)
    (hp : ∀ i j,P i j=P j i) (scale : ℚ) (volume eta m0 rate left t : ℝ) (s : ReactorState B K) :
    HasDerivAt (fun u => pieceCombinedEnergy z P scale volume eta m0 rate left u s)
      (pieceCombinedSlope z P scale volume eta m0 rate left t s) t := by
  cases s with
  | none => exact hasDerivAt_const t 1
  | some pair =>
    rcases pair with ⟨n,c⟩
    have hq := (piece_quadratic_derivative z P hp scale volume eta t (fun j => (n j).val)).pow 6
    have hc := (centeredInventory_derivative (K : ℝ) m0 rate (left+t) c.val).comp t
      ((hasDerivAt_id t).const_add left)
    convert hq.add hc using 1
    dsimp only [pieceCombinedSlope]
    ring

end CompositionalMemory.Semenov
