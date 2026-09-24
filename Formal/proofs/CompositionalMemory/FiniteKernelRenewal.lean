import proofs.CompositionalMemory.ClockRenewalMeasure
import proofs.CompositionalMemory.JumpClockConvolution
import proofs.CompositionalMemory.RenewalSelfLoop
import proofs.FiniteCopy.FiniteKernel

namespace CompositionalMemory
open Classical RandomViability FiniteCopy MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 60000
variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]

def clockStatePMF (P : FiniteKernel α) (x : α) : PMF α :=
  PMF.ofFintype (fun y => ENNReal.ofReal (P.prob x y)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun y _ => P.nonneg x y),P.row_sum,ENNReal.ofReal_one])

/-- Explicit finite-kernel form of the future measure used in renewal uniqueness. -/
theorem finiteClockRenewal_future (P : FiniteKernel α) (q : ℝ) (hq : 0 < q) (D : Set α)
    (F : α × ℝ → ℝ≥0∞) (hF : Measurable F) (x : α) (T : ℝ)
    (hx : x ∈ D) (hT : 0 ≤ T) :
    (∫⁻ y,F y ∂clockRenewalMeasure (clockStatePMF P) q D (x,T)) =
      renewalConv (causalExp q) (fun t => ENNReal.ofReal q*∑ y,ENNReal.ofReal (P.prob x y)*F (y,t)) T := by
  letI := isProbabilityMeasure_expMeasure hq
  have hm : Measurable (fun y : α × ℝ => F (y.1,T-y.2)) :=
    hF.comp (measurable_fst.prodMk (measurable_const.sub measurable_snd))
  have hf (y : α) : Measurable (fun t : ℝ => F (y,t)) := hF.comp (measurable_const.prodMk measurable_id)
  unfold clockRenewalMeasure
  rw [if_pos ⟨hx,hT⟩,lintegral_map hF (measurable_fst.prodMk (measurable_const.sub measurable_snd)),
    lintegral_prod _ hm.aemeasurable,lintegral_fintype]
  simp only [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),clockStatePMF,PMF.ofFintype_apply]
  simp_rw [exponential_future_convolution q T hq _ (hf _)]
  unfold renewalConv
  have hi (y : α) : Measurable (fun u : ℝ => causalExp q u*(ENNReal.ofReal q*
      (ENNReal.ofReal (P.prob x y)*F (y,T-u)))) :=
    (causalExp_measurable q).mul (measurable_const.mul (measurable_const.mul
      (hF.comp (measurable_const.prodMk (measurable_const.sub measurable_id)))))
  simp_rw [Finset.mul_sum]
  rw [lintegral_finsetSum Finset.univ (fun y _ => hi y)]
  apply Finset.sum_congr rfl
  intro y _
  have he (u : ℝ) : causalExp q u*(ENNReal.ofReal q*(ENNReal.ofReal (P.prob x y)*F (y,T-u)))=
      (ENNReal.ofReal q*ENNReal.ofReal (P.prob x y))*(causalExp q u*F (y,T-u)) := by ring
  simp_rw [he]
  have hj : Measurable (fun u : ℝ => causalExp q u*F (y,T-u)) :=
    (causalExp_measurable q).mul (hF.comp (measurable_const.prodMk (measurable_const.sub measurable_id)))
  rw [lintegral_const_mul _ hj]
  ring

end
end CompositionalMemory
