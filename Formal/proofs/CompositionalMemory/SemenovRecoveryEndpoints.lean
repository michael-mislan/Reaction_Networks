import proofs.CompositionalMemory.SemenovRecoveryPiece

namespace CompositionalMemory.Semenov
open Polynomial Matrix

noncomputable def boundaryEnergy (high : Bool) (z : Fin 8 → ℚ) (P : Fin 8 → Fin 8 → ℚ) (t : ℝ) :
    ReactorState recoveryCountCap recoveryFeedQuota → ℝ :=
  reactorCombinedEnergy
    (fun n => (matrixEnergy (rationalMatrix P)
      ((fun j => (n j : ℝ)/(recoveryVolume : ℝ))-(fun j => (z j : ℝ)))/(recoveryEta high : ℝ))^6)
    ((recoveryVolume : ℝ)*(15231/100000)/2)
    ((recoveryVolume : ℝ)*(1/500)*(15231/100000)) t

theorem polynomial_matrix_endpoint (P : Fin 8 → Fin 8 → QCoefficients)
    (q : ℚ) (M : Fin 8 → Fin 8 → ℚ) (h : ∀ i j,qeval q (P i j)=M i j) :
    polynomialMatrix P (q : ℝ)=rationalMatrix M := by
  ext i j
  simp only [polynomialMatrix,qeval_real_semantics,h,rationalMatrix]

theorem polynomial_vector_endpoint (z : Fin 8 → QCoefficients)
    (q : ℚ) (v : Fin 8 → ℚ) (h : ∀ j,qeval q (z j)=v j) :
    polynomialVector z (q : ℝ)=(fun j => (v j : ℝ)) := by
  funext j
  simp only [polynomialVector,qeval_real_semantics,h]

namespace RecoveryPiece
variable {high : Bool}

theorem energy_left (p : RecoveryPiece high) : p.energy 0=boundaryEnergy high p.zLeft p.pLeft p.left := by
  have hp : polynomialMatrix p.P (-1 : ℝ)=rationalMatrix p.pLeft := by
    simpa only [Rat.cast_neg,Rat.cast_one] using
      polynomial_matrix_endpoint p.P (-1) p.pLeft (fun i j => (p.p_endpoints i j).1)
  have hz : polynomialVector p.z (-1 : ℝ)=(fun j => (p.zLeft j : ℝ)) := by
    simpa only [Rat.cast_neg,Rat.cast_one] using
      polynomial_vector_endpoint p.z (-1) p.zLeft (fun j => (p.z_endpoints j).1)
  simp only [energy,pieceCombinedEnergy,pieceQuadratic,mul_zero,add_zero,hp,hz,boundaryEnergy]

theorem energy_right (p : RecoveryPiece high) :
    p.energy p.duration=boundaryEnergy high p.zRight p.pRight p.right := by
  have hd : (p.duration : ℝ) ≠ 0 := ne_of_gt (show (0 : ℝ) < p.duration from by
    change (0 : ℝ) < ((p.right-p.left : ℚ) : ℝ)
    exact_mod_cast sub_pos.mpr p.timing.2.1)
  have hs : (p.scale : ℝ)=2/(p.duration : ℝ) := by
    change (p.scale : ℝ)=2/((p.right-p.left : ℚ) : ℝ)
    exact_mod_cast p.timing.2.2.2
  have ht : -1+(p.scale : ℝ)*(p.duration : ℝ)=1 := by
    rw [hs,div_mul_cancel₀ _ hd]
    norm_num
  have htime : (p.left : ℝ)+(p.duration : ℝ)=(p.right : ℝ) := by
    change (p.left : ℝ)+((p.right-p.left : ℚ) : ℝ)=(p.right : ℝ)
    rw [Rat.cast_sub]
    ring
  have hp : polynomialMatrix p.P (1 : ℝ)=rationalMatrix p.pRight := by
    simpa only [Rat.cast_one] using
      polynomial_matrix_endpoint p.P 1 p.pRight (fun i j => (p.p_endpoints i j).2)
  have hz : polynomialVector p.z (1 : ℝ)=(fun j => (p.zRight j : ℝ)) := by
    simpa only [Rat.cast_one] using
      polynomial_vector_endpoint p.z 1 p.zRight (fun j => (p.z_endpoints j).2)
  simp only [energy,pieceCombinedEnergy,pieceQuadratic,ht,htime,hp,hz,boundaryEnergy]

theorem boundary_recovery_bound (p : RecoveryPiece high)
    (s : ReactorState recoveryCountCap recoveryFeedQuota) :
    finiteTimeExpectation (nominalReactor recoveryCountCap recoveryFeedQuota recoveryVolume (Nat.cast_nonneg _))
      p.duration (fun y => smoothQuadraticCap (boundaryEnergy high p.zRight p.pRight p.right y)) s ≤
      smoothQuadraticCap (boundaryEnergy high p.zLeft p.pLeft p.left s)+2*(p.duration : ℝ)*driftCost := by
  simpa only [p.energy_left,p.energy_right] using p.recovery_bound s

end RecoveryPiece
end CompositionalMemory.Semenov
