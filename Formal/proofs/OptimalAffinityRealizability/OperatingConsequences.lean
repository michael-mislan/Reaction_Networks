import proofs.OptimalAffinityRealizability.GlobalResolution

namespace OptimalAffinityRealizability
noncomputable section

theorem fixedEquilibrium_logReference {n : ℕ} (source : SquareSource n)
    (logK logq : Fin n → ℝ) :
    ∃! z, source.netStoich.transpose.mulVec z = logK - logq := by
  letI : Invertible source.netStoich.transpose :=
    Matrix.invertibleOfIsUnitDet _ (by simpa using source.netStoich_det_isUnit)
  refine ⟨source.netStoich.transpose⁻¹.mulVec (logK-logq), ?_, ?_⟩
  · dsimp only
    rw [Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible, Matrix.one_mulVec]
  · intro z hz
    apply (Matrix.mulVec_injective_iff_isUnit.mpr
      (source.netStoich.transpose.isUnit_iff_isUnit_det.mpr (by
        simpa using source.netStoich_det_isUnit)))
    rw [hz, Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible, Matrix.one_mulVec]

theorem fixedEquilibrium_rateRatio (K q a b v : ℝ)
    (hK : 0 < K) (hq : 0 < q) (hv : 0 < v)
    (hlog : b-a = Real.log K-Real.log q) :
    (v*q*Real.exp (-a))/(v*Real.exp (-b)) = K := by
  have he : Real.exp (b-a) = K/q := by
    rw [hlog, Real.exp_sub, Real.exp_log hK, Real.exp_log hq]
  have he' : Real.exp (-a) / Real.exp (-b) = K/q := by
    rw [← Real.exp_sub]
    convert he using 1
    congr 1
    ring
  calc
    (v*q*Real.exp (-a))/(v*Real.exp (-b)) =
        q*(Real.exp (-a)/Real.exp (-b)) := by field_simp
    _ = K := by rw [he']; field_simp

theorem reverseBudget_iff_ratio (J g q B : ℝ)
    (hq : 1 < q) (hB : 0 < B) :
    J*g/(q-1) ≤ B ↔ 1+J*g/B ≤ q := by
  rw [div_le_iff₀ (sub_pos.mpr hq)]
  constructor
  · intro h
    have : J*g/B ≤ q-1 := (div_le_iff₀ hB).mpr (by nlinarith)
    linarith
  · intro h
    have : J*g/B ≤ q-1 := by linarith
    have := (div_le_iff₀ hB).mp this
    nlinarith

theorem recycling_twoBudget_feasible_iff (J m B₁ B₂ : ℝ)
    (hB₁ : 0 < B₁) (hden : 0 < B₂+m*J) :
    1+J/B₁ ≤ 2*B₂/(B₂+m*J) ↔
      J*B₂+m*J*B₁+m*J^2 ≤ B₁*B₂ := by
  rw [le_div_iff₀ hden]
  constructor
  · intro h
    have := (mul_le_mul_iff_of_pos_left hB₁).mpr h
    field_simp at this
    nlinarith
  · intro h
    apply (mul_le_mul_iff_of_pos_left hB₁).mp
    field_simp
    nlinarith

theorem recycling_capacity_gap_turnover (m r J : ℝ)
    (hm : 1 < m) (hr : 1 < r) :
    (J/(r-1))*((r+(2-r)/m)-(1+1/m)) = J*(1-1/m) := by
  field_simp [ne_of_gt (lt_trans zero_lt_one hm), ne_of_gt (sub_pos.mpr hr)]
  ring

theorem recycling_controlled_vectorfield (y : ℝ) :
    (3-2*y)-(7*y^2-6*y) = -(y-1)*(7*y+3) := by ring

theorem recycling_controlled_sign (y : ℝ) (hy : 0 < y) :
    (y < 1 → 0 < (3-2*y)-(7*y^2-6*y)) ∧
    (1 < y → (3-2*y)-(7*y^2-6*y) < 0) := by
  rw [recycling_controlled_vectorfield]
  constructor
  · intro h
    exact mul_pos (by linarith) (by positivity)
  · intro h
    exact mul_neg_of_neg_of_pos (by linarith) (by positivity)

end
end OptimalAffinityRealizability
