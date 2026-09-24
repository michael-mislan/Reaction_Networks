import proofs.StartupCount.AffineRenewal
import proofs.RandomViability.CensoredExponentialClock
import proofs.RandomViability.JumpLaplace
import Mathlib.MeasureTheory.Integral.Lebesgue.Sub

namespace StartupCount
open Classical MeasureTheory ProbabilityTheory RandomViability Set
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 50000
set_option Elab.async false

def residualIntegral (R c T : ℝ) : ℝ :=
  Real.exp (-c*T)*(R/(R-c))*(1-Real.exp (-(R-c)*T))

theorem residualIntegral_nonneg (R c T : ℝ) (hR : 0 < R) (hcR : c < R)
    (hT : 0 ≤ T) : 0 ≤ residualIntegral R c T := by
  have he : Real.exp (-(R-c)*T) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  unfold residualIntegral
  positivity

theorem residualIntegral_eq (R c T : ℝ) (hR : 0 < R) (hcR : c < R) (hT : 0 ≤ T) :
    (∫⁻ u in Iic T,ENNReal.ofReal (Real.exp (-c*(T-u))) ∂expMeasure R) =
      ENNReal.ofReal (residualIntegral R c T) := by
  have he (u : ℝ) : Real.exp (-c*(T-u)) = Real.exp (-c*T)*Real.exp (-(-c)*u) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simp_rw [he,ENNReal.ofReal_mul (Real.exp_pos _).le]
  rw [lintegral_const_mul _ (by fun_prop),exponential_truncated_laplace R (-c) T hR (by linarith) hT]
  rw [← ENNReal.ofReal_mul (div_nonneg hR.le (by linarith)),
    ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  congr 1
  unfold residualIntegral
  simp only [sub_eq_add_neg]
  ring

theorem residualIntegral_le_probability (R c T : ℝ) (hR : 0 < R)
    (hc : 0 ≤ c) (hcR : c < R) (hT : 0 ≤ T) :
    residualIntegral R c T ≤ 1-Real.exp (-R*T) := by
  have hh : (∫⁻ u in Iic T,ENNReal.ofReal (Real.exp (-c*(T-u))) ∂expMeasure R) ≤
      ∫⁻ _ in Iic T,(1 : ℝ≥0∞) ∂expMeasure R := by
    apply lintegral_mono_ae
    apply (ae_restrict_iff' measurableSet_Iic).mpr
    filter_upwards [] with u hu
    apply ENNReal.ofReal_le_one.mpr
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc) (sub_nonneg.mpr hu)
  rw [residualIntegral_eq R c T hR hcR hT,lintegral_const,one_mul,
    Measure.restrict_apply_univ,exponential_Iic R T hR hT] at hh
  exact (ENNReal.ofReal_le_ofReal_iff (by
    have he := Real.exp_le_one_iff.mpr (show -R*T ≤ 0 by nlinarith)
    linarith)).mp hh

theorem truncated_affine_integral (R c b f T : ℝ) (hR : 0 < R)
    (hc : 0 ≤ c) (hcR : c < R) (hb : 0 ≤ b) (hf : 0 ≤ f) (hT : 0 ≤ T) :
    (∫⁻ u in Iic T,ENNReal.ofReal (affineEnvelope c b f (T-u)) ∂expMeasure R) =
      ENNReal.ofReal (residualIntegral R c T*f+
        (1-Real.exp (-R*T)-residualIntegral R c T)*b) := by
  let E : ℝ → ℝ≥0∞ := fun u => ENNReal.ofReal (Real.exp (-c*(T-u)))
  have hEm : Measurable E := by dsimp [E]; fun_prop
  have hE : E ≤ᵐ[(expMeasure R).restrict (Iic T)] (fun _ => 1) := by
    apply (ae_restrict_iff' measurableSet_Iic).mpr
    filter_upwards [] with u hu
    exact ENNReal.ofReal_le_one.mpr (Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc) (sub_nonneg.mpr hu)))
  have hEi : (∫⁻ u in Iic T,E u ∂expMeasure R) = ENNReal.ofReal (residualIntegral R c T) :=
    residualIntegral_eq R c T hR hcR hT
  have hpoint : ∀ᵐ u ∂(expMeasure R).restrict (Iic T),
      ENNReal.ofReal (affineEnvelope c b f (T-u)) = E u*ENNReal.ofReal f+(1-E u)*ENNReal.ofReal b := by
    apply (ae_restrict_iff' measurableSet_Iic).mpr
    filter_upwards [] with u hu
    have he : 0 ≤ 1-Real.exp (-c*(T-u)) := sub_nonneg.mpr
      (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr hc) (sub_nonneg.mpr hu)))
    rw [affineEnvelope,ENNReal.ofReal_add (mul_nonneg (Real.exp_pos _).le hf) (mul_nonneg he hb),
      ENNReal.ofReal_mul (Real.exp_pos _).le,ENNReal.ofReal_mul he,
      ENNReal.ofReal_sub 1 (Real.exp_pos _).le,ENNReal.ofReal_one]
  rw [lintegral_congr_ae hpoint,lintegral_add_left (hEm.mul_const _),
    lintegral_mul_const _ hEm,lintegral_mul_const _ (measurable_const.sub hEm),
    lintegral_sub hEm (by rw [hEi]; exact ENNReal.ofReal_ne_top) hE,hEi,
    lintegral_const,one_mul,Measure.restrict_apply_univ,exponential_Iic R T hR hT]
  have hj := residualIntegral_nonneg R c T hR hcR hT
  have hp := sub_nonneg.mpr (residualIntegral_le_probability R c T hR hc hcR hT)
  rw [← ENNReal.ofReal_sub _ hj,← ENNReal.ofReal_mul hj,← ENNReal.ofReal_mul hp,
    ← ENNReal.ofReal_add (mul_nonneg hj hf) (mul_nonneg hp hb)]

theorem censored_affine_integral (R c b f₀ f₁ T : ℝ) (hR : 0 < R)
    (hc : 0 ≤ c) (hcR : c < R) (hb : 0 ≤ b) (hf₀ : 0 ≤ f₀) (hf₁ : 0 ≤ f₁)
    (hT : 0 ≤ T) :
    (∫⁻ u,if T < u then ENNReal.ofReal f₀ else
      ENNReal.ofReal (affineEnvelope c b f₁ (T-u)) ∂expMeasure R) =
    ENNReal.ofReal (Real.exp (-R*T)*f₀+residualIntegral R c T*f₁+
      (1-Real.exp (-R*T)-residualIntegral R c T)*b) := by
  change (∫⁻ u,(Ioi T).piecewise (fun _ => ENNReal.ofReal f₀)
    (fun u => ENNReal.ofReal (affineEnvelope c b f₁ (T-u))) u ∂expMeasure R) = _
  rw [lintegral_piecewise measurableSet_Ioi,compl_Ioi,lintegral_const,
    Measure.restrict_apply_univ,exponential_Ioi R T hR hT,
    truncated_affine_integral R c b f₁ T hR hc hcR hb hf₁ hT,
    ← ENNReal.ofReal_mul hf₀]
  have hj := residualIntegral_nonneg R c T hR hcR hT
  have hp := sub_nonneg.mpr (residualIntegral_le_probability R c T hR hc hcR hT)
  rw [← ENNReal.ofReal_add (mul_nonneg hf₀ (Real.exp_pos _).le)
    (add_nonneg (mul_nonneg hj hf₁) (mul_nonneg hp hb))]
  congr 1
  ring

set_option maxHeartbeats 5000 in
theorem residualIntegral_balance (R c T : ℝ) (hcR : c < R) :
    (R-c)*residualIntegral R c T = R*(Real.exp (-c*T)-Real.exp (-R*T)) := by
  have he : Real.exp (-c*T)*Real.exp (-(R-c)*T) = Real.exp (-R*T) := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold residualIntegral
  field_simp [ne_of_gt (sub_pos.mpr hcR)]
  simp only [neg_mul] at he ⊢
  linear_combination -R*he

set_option maxHeartbeats 5000 in
theorem censored_affine_scalar_bound (R c b f S T : ℝ) (hR : 0 < R)
    (hcR : c < R) (hT : 0 ≤ T) (hS : S ≤ (R-c)*f+c*b) :
    Real.exp (-R*T)*f+residualIntegral R c T*(S/R)+
      (1-Real.exp (-R*T)-residualIntegral R c T)*b ≤ affineEnvelope c b f T := by
  have hj := residualIntegral_nonneg R c T hR hcR hT
  have hm := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hS hR.le) hj
  have he : Real.exp (-R*T)*f+residualIntegral R c T*(((R-c)*f+c*b)/R)+
      (1-Real.exp (-R*T)-residualIntegral R c T)*b = affineEnvelope c b f T := by
    unfold affineEnvelope
    field_simp [ne_of_gt hR]
    have hbal := residualIntegral_balance R c T hcR
    simp only [neg_mul] at hbal ⊢
    ring_nf at hbal ⊢
    linear_combination (f-b)*hbal
  linarith only [hm,he]

variable {β : Type*} [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]

/-- Complete censored first-jump supersolution under the physical exponential
clock and its actual rate-weighted channel distribution. -/
theorem jumpClock_affine_bound (rate : β → ℝ) (hr : ∀ j,0 ≤ rate j)
    (hR : 0 < ∑ j,rate j) (f : β → ℝ) (hf : ∀ j,0 ≤ f j)
    (c b f₀ T : ℝ) (hc : 0 ≤ c) (hcR : c < ∑ j,rate j)
    (hb : 0 ≤ b) (hf₀ : 0 ≤ f₀) (hT : 0 ≤ T)
    (hgen : (∑ j,rate j*f j) ≤ ((∑ j,rate j)-c)*f₀+c*b) :
    (∫⁻ y,if T < y.2 then ENNReal.ofReal f₀ else
      ENNReal.ofReal (affineEnvelope c b (f y.1) (T-y.2))
      ∂jumpClockMeasure rate hr hR) ≤ ENNReal.ofReal (affineEnvelope c b f₀ T) := by
  let R := ∑ j,rate j
  let J := residualIntegral R c T
  let D := Real.exp (-R*T)
  letI := isProbabilityMeasure_expMeasure hR
  have hJ : 0 ≤ J := residualIntegral_nonneg R c T hR hcR hT
  have hp : 0 ≤ 1-D-J := sub_nonneg.mpr (residualIntegral_le_probability R c T hR hc hcR hT)
  have hw (j) : 0 ≤ D*f₀+J*f j+(1-D-J)*b := by
    exact add_nonneg (add_nonneg (mul_nonneg (Real.exp_pos _).le hf₀)
      (mul_nonneg hJ (hf j))) (mul_nonneg hp hb)
  unfold jumpClockMeasure
  rw [lintegral_prod _ (by
    apply Measurable.aemeasurable
    apply Measurable.ite (measurableSet_lt measurable_const measurable_snd)
      measurable_const
    unfold affineEnvelope
    exact (((by fun_prop : Measurable (fun y : β × ℝ => Real.exp (-c*(T-y.2)))).mul
      ((measurable_of_countable f).comp measurable_fst)).add (by fun_prop)).ennreal_ofReal)]
  change (∫⁻ j, (∫⁻ u,if T < u then ENNReal.ofReal f₀ else
    ENNReal.ofReal (affineEnvelope c b (f j) (T-u)) ∂expMeasure R)
    ∂(jumpLabelPMF rate hr hR).toMeasure) ≤ _
  have hinner (j : β) := censored_affine_integral R c b f₀ (f j) T hR hc hcR hb hf₀ (hf j) hT
  simp_rw [hinner]
  rw [jumpLabel_weight_integral rate hr hR _ hw]
  apply ENNReal.ofReal_le_ofReal
  have he : (∑ j,rate j*(D*f₀+J*f j+(1-D-J)*b))/R =
      D*f₀+J*((∑ j,rate j*f j)/R)+(1-D-J)*b := by
    have hpoint (j : β) : rate j*(D*f₀+J*f j+(1-D-J)*b) =
        rate j*(D*f₀)+J*(rate j*f j)+rate j*((1-D-J)*b) := by ring
    simp_rw [hpoint,Finset.sum_add_distrib,← Finset.sum_mul,← Finset.mul_sum]
    change (R*(D*f₀)+J*(∑ j,rate j*f j)+R*((1-D-J)*b))/R = _
    field_simp [show R ≠ 0 from ne_of_gt hR]
  rw [he]
  exact censored_affine_scalar_bound R c b f₀ _ T hR hcR hT hgen

end
end StartupCount
