import proofs.CoreCouplingGlobal.ResponseCurve

namespace CoreCouplingGlobal
open CoreCouplingCAC Set

noncomputable def curveEnergy (e : ℝ) (p : PotentialPrimitives e) (z : ℝ) : ℝ :=
  responsePotential e p (60/(z+2)) z (naturalH z) 0

theorem curve_B_bounds (z : ℝ) (hz : z ∈ Icc (9/10:ℝ) (31/10)) :
    60/(z+2) ∈ Icc (2:ℝ) 34 := by
  have hd : 0 < z+2 := by linarith [hz.1]
  constructor
  · apply (le_div_iff₀ hd).2
    linarith [hz.2]
  · apply (div_le_iff₀ hd).2
    linarith [hz.1]

theorem curveEnergy_hasDerivAt (e : ℝ) (p : PotentialPrimitives e)
    (he : 0 ≤ e) (hu : e ≤ 1/50000) (z : ℝ) (hz : z ∈ Icc (9/10:ℝ) (31/10)) :
    HasDerivAt (curveEnergy e p)
      (-reducedZ e (60/(z+2)) z/((z+1)*(z+2))) z := by
  have hz0 : 0 ≤ z := by linarith [hz.1]
  have hzm : z ≤ 12 := by linarith [hz.2]
  have hd : z+2 ≠ 0 := by positivity
  have hB := curve_B_bounds z hz
  have hH : naturalH z ∈ Icc (0:ℝ) (1536/7) := by
    constructor
    · exact (naturalH_bounds z ⟨hz0,hzm⟩).1
    · unfold naturalH
      apply (div_le_iff₀ (by norm_num : (0:ℝ) < 20001/10000)).2
      nlinarith [hz.1,hz.2,sq_nonneg (z-31/10)]
  have dB := (hasDerivAt_const z (60:ℝ)).div ((hasDerivAt_id z).add_const 2) hd
  have dH : HasDerivAt naturalH ((16+4*z)/(20001/10000)) z := by
    convert (((hasDerivAt_id z).const_mul 16).add
      (((hasDerivAt_id z).pow 2).const_mul 2)).div_const (20001/10000) using 1
    dsimp [naturalH]
    ring
  have hv := responsePotential_hasDerivAt e p he hu (fun t => 60/(t+2)) id naturalH
    (fun _ => 0) z _ 1 _ 0 hB ⟨hz0,hzm⟩ hH dB (hasDerivAt_id z) dH (hasDerivAt_const z 0)
  have hratio : 60/(60/(z+2)) = z+2 := by field_simp
  have hgrad : Real.log (z+2)-responseSlope e (60/(z+2))*responseLog z+
      responsePIntegrand e (60/(z+2)) = 0 := by
    unfold responsePIntegrand
    rw [hratio]
    simp only [add_sub_cancel_right]
    ring
  dsimp only [id_eq] at hv
  rw [hgrad,responsePhi_naturalH z hz0] at hv
  convert hv using 1
  dsimp [reducedZ,naturalH]
  field_simp
  ring

theorem curve_reducedZ_identity (e z : ℝ) :
    reducedZ e (60/(z+2)) z = responseA e (reducedB (varyRates e) z)-reducedA (varyRates e) z := by
  norm_num [reducedZ,responseTotal,reducedB,reducedA,reducedK,varyRates,witnessRates]
  ring

theorem curveEnergy_derivative_sign (e z : ℝ) (he : 0 ≤ e) (hu : e ≤ 1/50000)
    (hz : z ∈ Icc (9/10:ℝ) (31/10)) :
    (0 < -reducedZ e (60/(z+2)) z/((z+1)*(z+2)) ↔ 0 < residual (varyRates e) z) ∧
    (-reducedZ e (60/(z+2)) z/((z+1)*(z+2)) < 0 ↔ residual (varyRates e) z < 0) := by
  have hz0 : 0 < z := by linarith [hz.1]
  have hz8 : z ≤ 4 := by linarith [hz.2]
  have hA := (witness_lift_positive z hz0 hz8).1.le
  have hB : reducedB (varyRates e) z ∈ Icc (2:ℝ) 34 := by
    norm_num [reducedB,varyRates,witnessRates]
    exact curve_B_bounds z hz
  have hf := response_curve_factor_positive e z he hu hB.1 hB.2 hA
  have heq := response_curve_factorization e z he hu hB.1 hB.2 (by positivity)
  have hw : 0 < (z+1)*(z+2) := by positivity
  rw [curve_reducedZ_identity,heq]
  constructor
  · rw [div_pos_iff_of_pos_right hw,mul_pos_iff_of_pos_right hf]
    constructor <;> intro h <;> linarith
  · constructor
    · intro h
      have hh := (div_lt_iff₀ hw).1 h
      exact mul_neg_of_neg_of_pos (by linarith) hf
    · intro h
      apply (div_lt_iff₀ hw).2
      have hn : reducedA (varyRates e) z-responseA e (reducedB (varyRates e) z) < 0 := by
        by_contra hnot
        have hp := mul_nonneg (le_of_not_gt hnot) hf.le
        linarith
      linarith

end CoreCouplingGlobal
