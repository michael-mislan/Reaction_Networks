import proofs.CompositionalMemory.CausalExponential
import proofs.RandomViability.CensoredExponentialClock

namespace CompositionalMemory
open Classical RandomViability MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 60000

theorem exponential_future_convolution (r T : ℝ) (hr : 0 < r)
    (H : ℝ → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ u,H (T-u) ∂expMeasure r)=ENNReal.ofReal r*renewalConv (causalExp r) H T := by
  have hp (u : ℝ) : exponentialPDF r u=ENNReal.ofReal r*causalExp r u := by
    by_cases hu : 0 ≤ u
    · rw [exponentialPDF_of_nonneg hu]
      simp only [causalExp,if_pos hu]
      rw [← ENNReal.ofReal_mul hr.le]
      congr 1
      rw [neg_mul]
    · rw [exponentialPDF_of_neg (lt_of_not_ge hu)]
      simp [causalExp,hu]
  change (∫⁻ u,H (T-u) ∂volume.withDensity (exponentialPDF r))=_
  have hm : Measurable (fun u : ℝ => H (T-u)) := hH.comp (measurable_const.sub measurable_id)
  have hd : Measurable (exponentialPDF r) := (measurable_exponentialPDFReal r).ennreal_ofReal
  rw [lintegral_withDensity_eq_lintegral_mul volume hd hm]
  simp only [Pi.mul_apply,hp,mul_assoc]
  exact lintegral_const_mul _ ((causalExp_measurable r).mul (hH.comp (measurable_const.sub measurable_id)))

variable {β : Type*} [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]

theorem jumpClock_future_convolution (rate : β → ℝ) (hr : ∀ b,0 ≤ rate b)
    (ht : 0 < ∑ b,rate b) (H : β → ℝ → ℝ≥0∞) (hH : ∀ b,Measurable (H b)) (T : ℝ) :
    (∫⁻ y,H y.1 (T-y.2) ∂jumpClockMeasure rate hr ht) =
      renewalConv (causalExp (∑ b,rate b)) (fun t => ∑ b,ENNReal.ofReal (rate b)*H b t) T := by
  have hm : Measurable (fun y : β × ℝ => H y.1 (T-y.2)) :=
    measurable_from_prod_countable_right (fun b => (hH b).comp (measurable_const.sub measurable_id))
  letI := isProbabilityMeasure_expMeasure ht
  unfold jumpClockMeasure
  rw [lintegral_prod _ hm.aemeasurable,lintegral_fintype]
  simp only [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),jumpLabelPMF,PMF.ofFintype_apply]
  simp_rw [exponential_future_convolution _ T ht _ (hH _)]
  have he (b : β) : ENNReal.ofReal (∑ b,rate b)*ENNReal.ofReal (rate b/(∑ b,rate b))=
      ENNReal.ofReal (rate b) := by
    rw [← ENNReal.ofReal_mul ht.le]
    congr 1
    field_simp
  have hc (b : β) : (ENNReal.ofReal (∑ b,rate b)*renewalConv (causalExp (∑ b,rate b)) (H b) T)*
      ENNReal.ofReal (rate b/(∑ b,rate b))=
      ENNReal.ofReal (rate b)*renewalConv (causalExp (∑ b,rate b)) (H b) T := by
    rw [mul_right_comm,he]
  simp_rw [hc]
  unfold renewalConv
  simp_rw [Finset.mul_sum]
  have hi (b : β) : Measurable (fun u : ℝ => causalExp (∑ b,rate b) u*(ENNReal.ofReal (rate b)*H b (T-u))) :=
    (causalExp_measurable _).mul (measurable_const.mul ((hH b).comp (measurable_const.sub measurable_id)))
  rw [lintegral_finsetSum Finset.univ (fun b _ => hi b)]
  apply Finset.sum_congr rfl
  intro b _
  have ha (u : ℝ) : causalExp (∑ b,rate b) u*(ENNReal.ofReal (rate b)*H b (T-u))=
      ENNReal.ofReal (rate b)*(causalExp (∑ b,rate b) u*H b (T-u)) := by ring
  simp_rw [ha]
  exact (lintegral_const_mul _ ((causalExp_measurable _).mul ((hH b).comp (measurable_const.sub measurable_id)))).symm

end
end CompositionalMemory
