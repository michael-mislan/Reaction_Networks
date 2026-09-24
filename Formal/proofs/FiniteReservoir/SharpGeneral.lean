import proofs.FiniteReservoir.SharpEnvelope
import proofs.FiniteReservoir.Mission

namespace FiniteReservoir
noncomputable section
open Classical FiniteCopyReactor ProductiveRecovery MeasureTheory ProbabilityTheory RandomViability RandomViability.Binding
open scoped ENNReal

variable {H : Type*} [MeasurableSpace H]

/-- The phase refinement alone: same success event, smaller error, every admitted bath. -/
theorem physical_history_phase_one_cycle {V M : ℕ} {params : Parameters M} {hV}
    (S : PhysicalHistory H V M params hV) (hlarge : 1000000 ≤ V)
    (h : H) (hh : Restart V (S.current h).1) :
    ENNReal.ofReal (1-sharpOneCycleError V) ≤ S.step h (physicalHistorySuccess S) := by
  have hp := literal_cycle_phase_bound (S.current h).1 V M (S.policy h) hh hlarge params
    (S.current h).2 hV
  rw [← S.conditional_law h,Measure.map_apply S.observe_measurable
    (Set.to_countable {X : JointCounts M | CountCycleSuccess V M X}).measurableSet] at hp
  exact hp

theorem physical_history_phase_linear {V M : ℕ} {params : Parameters M} {hV}
    (S : PhysicalHistory H V M params hV) (hscale : 50000000000 ≤ V) (n : ℕ) (h : H)
    (hh : Restart V (S.current h).1) :
    ENNReal.ofReal (1-(n:ℝ)*sharpOneCycleError V) ≤
      successfulHistoryKernel S.step (physicalHistorySuccess S)
        (physical_history_success_measurable S) n h Set.univ := by
  apply history_survival_linear S.step {y | Restart V (S.current y).1} (physicalHistorySuccess S)
    (physical_history_success_measurable S) _ (sharpOneCycleError V) _
    (fun y hy => physical_history_phase_one_cycle S (by omega) y hy) n h hh
  · intro y hy
    change Restart V (S.current y).1
    rw [S.current_return y]
    exact hy.1
  · have hs := sharp_error_small V (by exact_mod_cast hscale)
    have hb := sharpOneCycleError_le_both (V:ℝ)
    linarith

theorem full_returned_phase_success (M : ℕ) (N : CountState M) (V : ℕ) (params : Parameters M)
    (hV : 0 < (V:ℝ)) (policy : ReturnedHistory M → Intervention)
    (hscale : 50000000000 ≤ V) (hN : Restart V N.1) (n : ℕ) :
    ENNReal.ofReal (1-(n:ℝ)*sharpOneCycleError V) ≤
      fullHistoryKernel (returnedHistoryStep M N V params hV policy) n [] (returnedFinal V M n) := by
  have hs := physical_history_phase_linear (returnedPhysicalHistory M N V params hV policy)
    hscale n [] hN
  apply hs.trans
  apply successful_history_event_lower _ _ _ n [] (returnedFinal V M n)
    (Set.to_countable _).measurableSet
  simpa only [List.length_nil,Nat.zero_add] using
    returned_success_support M N V params hV policy n [] (by simp [returnedGood])

/-- Theorem: the full finite-bath mission conclusion at the unrounded phase rate,
for every admitted bath inventory and every admitted parameter set. -/
theorem finite_bath_horizon_sharp (M : ℕ) (N : CountState M) (V : ℕ) (params : Parameters M)
    (hV : 0 < (V:ℝ)) (policy : ReturnedHistory M → Intervention)
    (hscale : 50000000000 ≤ V) (hN : Restart V N.1) (n : ℕ) :
    ENNReal.ofReal (1-(n:ℝ)*sharpOneCycleError V) ≤
      fullHistoryKernel (returnedHistoryStep M N V params hV policy) n []
        (OperationalSuccess M N V n policy) := by
  have ht := full_history_has_trace M N V params hV policy n [] ⟨HistoryTrace.nil⟩
  have he : certifiedPhysicalHistory M N V n policy =ᵐ[
      fullHistoryKernel (returnedHistoryStep M N V params hV policy) n []] returnedFinal V M n := by
    filter_upwards [ht] with h hh
    change (h ∈ returnedFinal V M n ∧ Nonempty (HistoryTrace M N V policy h))=
      (h ∈ returnedFinal V M n)
    simp only [hh,and_true]
  have hlow := full_returned_phase_success M N V params hV policy hscale hN n
  rw [← measure_congr he] at hlow
  exact hlow.trans (measure_mono (certified_history_operational M N V n policy hN))

theorem finite_bath_budget_sharp (M : ℕ) (N : CountState M) (V : ℕ) (params : Parameters M)
    (hV : 0 < (V:ℝ)) (policy : ReturnedHistory M → Intervention)
    (hscale : 50000000000 ≤ V) (hN : Restart V N.1) (n : ℕ) (δ : ℝ)
    (hb : (n:ℝ)*sharpOneCycleError V ≤ δ) :
    ENNReal.ofReal (1-δ) ≤ fullHistoryKernel (returnedHistoryStep M N V params hV policy) n []
      (OperationalSuccess M N V n policy) :=
  (ENNReal.ofReal_le_ofReal (by linarith : 1-δ ≤ 1-(n:ℝ)*sharpOneCycleError V)).trans
    (finite_bath_horizon_sharp M N V params hV policy hscale hN n)

/-- The loaded bath keeps the original service allowance but inherits the phase refinement. -/
theorem loaded_hundred_sharp (R : ℕ) (hR : 0 < R) (policy : ReturnedHistory (2*R) → Intervention) :
    let V : ℕ := 96000000000
    let N : CountState (2*R) := (![0,0,V,0,0,0],loadedFuel R)
    let params := loadedParameters R hR 20 (by norm_num) (by norm_num)
    ENNReal.ofReal (999979/1000000:ℝ) ≤
      fullHistoryKernel (returnedHistoryStep (2*R) N V params (by norm_num) policy) 100 []
        (OperationalSuccess (2*R) N V 100 policy) := by
  dsimp only
  have hN : Restart 96000000000 ![0,0,96000000000,0,0,0] := all_free_restart _
  have hb : (100:ℝ)*sharpOneCycleError 96000000000 ≤ 21/1000000 := by
    have hle := sharpOneCycleError_le_both (96000000000:ℝ)
    linarith [sharp_hundred_budget]
  convert finite_bath_budget_sharp (2*R) (![0,0,96000000000,0,0,0],loadedFuel R) 96000000000
    (loadedParameters R hR 20 (by norm_num) (by norm_num))
    (by norm_num) policy (by norm_num) hN 100 (21/1000000) hb using 1
  norm_num

end
end FiniteReservoir
