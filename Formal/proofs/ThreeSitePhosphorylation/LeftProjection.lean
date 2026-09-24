import proofs.ThreeSitePhosphorylation.Eigenbasis

namespace ThreeSitePhosphorylation
noncomputable section
set_option maxHeartbeats 300000

def sourceLeft (r : ℝ) (z : ℂ) : (Fin 9 → ℂ) →ₗ[ℂ] ℂ :=
  (candidateSlope r z)⁻¹ •
    ((dotProductEquiv ℂ (Fin 9) (companionLeft r z)).comp companionInverse.mulVecLin)

theorem sourceLeft_apply (r : ℝ) (z : ℂ) (v : Fin 9 → ℂ) :
    sourceLeft r z v = (candidateSlope r z)⁻¹*
      dotProduct (companionLeft r z) (companionInverse.mulVec v) := rfl

theorem inverse_adjugate (z : ℂ) : companionInverse.mulVec (adjugateVector z)=powerVector z := by
  rw [← basis_powerVector,Matrix.mulVec_mulVec,companion_inverse_complex,Matrix.one_mulVec]

theorem sourceLeft_normalized (r : ℝ) (z : ℂ) (hs : candidateSlope r z ≠ 0) :
    sourceLeft r z (adjugateVector z)=1 := by
  rw [sourceLeft_apply,inverse_adjugate,companion_left_pairing]
  exact inv_mul_cancel₀ hs

theorem sourceLeft_eigen (r : ℝ) (z : ℂ) (hp : candidatePolynomial r z=0)
    (v : Fin 9 → ℂ) : sourceLeft r z ((complexSource r).mulVec v)=z*sourceLeft r z v := by
  rw [sourceLeft_apply,inverse_source_action,Matrix.dotProduct_mulVec,
    companion_left_residual,hp,Pi.single_zero,sub_zero,smul_dotProduct,sourceLeft_apply]
  change (candidateSlope r z)⁻¹*(z*_) = z*((candidateSlope r z)⁻¹*_)
  ring

theorem sourceLeft_other_eigen (r : ℝ) (z q : ℂ) (hp : candidatePolynomial r z=0)
    (hne : z ≠ q) (v : Fin 9 → ℂ) (he : (complexSource r).mulVec v=q • v) :
    sourceLeft r z v=0 := by
  have hh := sourceLeft_eigen r z hp v
  rw [he,map_smul,smul_eq_mul] at hh
  have hz : (z-q)*sourceLeft r z v=0 := by linear_combination -hh
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hne)

def sourceDelta : Matrix (Fin 9) (Fin 9) ℂ := complexSource 1-complexSource 0

theorem inverse_source_delta (v : Fin 9 → ℂ) :
    companionInverse.mulVec (sourceDelta.mulVec v) =
      (companionSource 1-companionSource 0).mulVec (companionInverse.mulVec v) := by
  simp only [sourceDelta,Matrix.sub_mulVec,Matrix.mulVec_sub,inverse_source_action]

theorem companion_delta_power (z : ℂ) :
    (companionSource 1-companionSource 0).mulVec (powerVector z) =
      -(Pi.single 8 (candidateParameter z)) := by
  rw [Matrix.sub_mulVec,companion_powerVector,companion_powerVector]
  ext i
  by_cases hi : i=8 <;> simp [hi,candidateParameter]

theorem companionLeft_last (r : ℝ) (z : ℂ) : companionLeft r z 8=1 := by
  change (((1/1:ℝ)+r*(0/1:ℝ)):ℂ)*z^0=1
  simp

/-- The normalized left/right parameter pairing is the eigenvalue derivative
quotient, proved directly from the affine companion source. -/
theorem sourceLeft_crossing_pairing (r : ℝ) (z : ℂ) :
    sourceLeft r z (sourceDelta.mulVec (adjugateVector z)) =
      -candidateParameter z/candidateSlope r z := by
  rw [sourceLeft_apply,inverse_source_delta,inverse_adjugate,companion_delta_power,
    dotProduct_neg,dotProduct_single,companionLeft_last,one_mul]
  simp only [div_eq_mul_inv]
  ring

theorem sourceLeft_crossing_real_negative (r w : ℝ) (hw : w ≠ 0)
    (hp : candidatePolynomial r (Complex.I*(w:ℂ))=0) :
    (sourceLeft r (Complex.I*(w:ℂ))
      (sourceDelta.mulVec (adjugateVector (Complex.I*(w:ℂ))))).re < 0 := by
  rw [sourceLeft_crossing_pairing]
  exact candidate_crossing_negative r w hw hp

end
end ThreeSitePhosphorylation
