import proofs.FiniteCopyReactor.EndpointMeasurability
import proofs.RandomViability.CensoredExponentialClock
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

namespace FiniteCopyReactor
noncomputable section
open Classical MeasureTheory ProbabilityTheory RandomViability
open scoped ENNReal BigOperators
set_option maxHeartbeats 500000

variable {α β : Type*} [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]

theorem jump_label_integral (rate : β → ℝ) (hr : ∀ b,0 ≤ rate b)
    (ht : 0 < ∑ b,rate b) (F : β → ℝ≥0∞) :
    (∫⁻ b,F b ∂(jumpLabelPMF rate hr ht).toMeasure)=
      ∑ b,ENNReal.ofReal (rate b/(∑ c,rate c))*F b := by
  rw [lintegral_fintype]
  simp only [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),jumpLabelPMF,PMF.ofFintype_apply]
  apply Finset.sum_congr rfl
  intro b _
  exact mul_comm _ _

theorem jump_clock_integral (rate : β → ℝ) (hr : ∀ b,0 ≤ rate b)
    (ht : 0 < ∑ b,rate b) (F : β × ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ y,F y ∂jumpClockMeasure rate hr ht)=
      ∑ b,ENNReal.ofReal (rate b/(∑ c,rate c))*(∫⁻ w,F (b,w) ∂expMeasure (∑ c,rate c)) := by
  letI := isProbabilityMeasure_expMeasure ht
  rw [jumpClockMeasure,lintegral_prod _ hF.aemeasurable,jump_label_integral]

theorem exponential_no_event_integral (q T : ℝ) (hq : 0 < q) (hT : 0 ≤ T) (c : ℝ≥0∞) :
    (∫⁻ w,(if T < w then c else 0) ∂expMeasure q)=ENNReal.ofReal (Real.exp (-q*T))*c := by
  change (∫⁻ w,(Set.Ioi T).indicator (fun _ => c) w ∂expMeasure q)=_
  rw [lintegral_indicator measurableSet_Ioi,lintegral_const,Measure.restrict_apply_univ,
    exponential_Ioi q T hq hT,mul_comm]

variable [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]

theorem chronological_endpoint_separated (next : α → β → α) (rate : α → β → ℝ)
    (hr : ∀ x b,0 ≤ rate x b) (ht : ∀ x,0 < ∑ b,rate x b)
    (f : α → ℝ≥0∞) (x : α) (T : ℝ) (hT : 0 ≤ T) :
    chronologicalEndpoint next rate hr ht f x T=
      ENNReal.ofReal (Real.exp (-(∑ b,rate x b)*T))*f x+
        ∑ b,ENNReal.ofReal (rate x b/(∑ c,rate x c))*
          ∫⁻ w,chronologicalEndpoint next rate hr ht f (next x b) (T-w) ∂expMeasure (∑ c,rate x c) := by
  have hm := chronological_endpoint_measurable next rate hr ht f
  have hmap : Measurable (fun y : β × ℝ => (T-y.2,next x y.1)) :=
    (measurable_const.sub measurable_snd).prodMk ((measurable_of_countable (next x)).comp measurable_fst)
  have hcomp := hm.comp hmap
  have hJ : Measurable (fun y : β × ℝ => chronologicalEndpoint next rate hr ht f (next x y.1) (T-y.2)) := hcomp
  have hM : Measurable (fun y : β × ℝ => if T < y.2 then f x else 0) :=
    Measurable.ite (measurableSet_lt measurable_const measurable_snd) measurable_const measurable_const
  have hN : (∫⁻ y : β × ℝ,(if T < y.2 then f x else 0) ∂jumpClockMeasure (rate x) (hr x) (ht x))=
      ENNReal.ofReal (Real.exp (-(∑ b,rate x b)*T))*f x := by
    rw [jump_clock_integral (rate x) (hr x) (ht x) _ hM]
    simp_rw [exponential_no_event_integral _ T (ht x) hT (f x)]
    rw [← Finset.sum_mul,← ENNReal.ofReal_sum_of_nonneg (fun b _ => div_nonneg (hr x b) (ht x).le),
      ← Finset.sum_div,div_self (ne_of_gt (ht x)),ENNReal.ofReal_one,one_mul]
  calc
    _ = ∫⁻ y : β × ℝ,(if T < y.2 then f x else 0)+
        chronologicalEndpoint next rate hr ht f (next x y.1) (T-y.2)
        ∂jumpClockMeasure (rate x) (hr x) (ht x) := by
      simpa only [hT,true_and] using chronological_endpoint_renewal next rate hr ht f x T
    _ = _ := (lintegral_add_left hM _).trans
      (congrArg₂ (fun a b : ℝ≥0∞ => a+b) hN (jump_clock_integral (rate x) (hr x) (ht x) _ hJ))

end
end FiniteCopyReactor
