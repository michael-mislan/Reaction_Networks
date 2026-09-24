import proofs.FiniteCopyReactor.Resolution

namespace FiniteCopyReactor
noncomputable section
open Classical ProductiveRecovery MeasureTheory ProbabilityTheory RandomViability RandomViability.Binding
open scoped ENNReal

theorem physical_history_product {H : Type*} [MeasurableSpace H]
    {V : ℕ} {r d : ℝ} {hV hr hd} (R : PhysicalHistory H V r d hV hr hd)
    (hscale : 200000000000 ≤ V) (hr19 : 19 ≤ r) (hr21 : r ≤ 21) (hd25 : d ≤ 1/25)
    (n : ℕ) (h : H) (hh : Restart V (R.current h)) :
    ENNReal.ofReal (1-oneCycleError V)^n ≤
      successfulHistoryKernel R.step (physicalHistorySuccess R) (physical_history_success_measurable R) n h Set.univ := by
  apply history_survival_product R.step {y | Restart V (R.current y)} (physicalHistorySuccess R)
    (physical_history_success_measurable R) _ _
    (fun y hy => physical_history_one_cycle R (by omega) hr19 hr21 hd25 y hy) n h hh
  intro y hy
  change Restart V (R.current y)
  rw [R.current_return y]
  exact hy.1

theorem full_operational_product (N : Counts) (V : ℕ) (r d : ℝ)
    (hV : 0 < (V:ℝ)) (hr : 19 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25)
    (policy : ReturnedHistory → Intervention) (hscale : 200000000000 ≤ V) (hN : Restart V N) (n : ℕ) :
    ENNReal.ofReal (1-oneCycleError V)^n ≤
      fullHistoryKernel (returnedHistoryStep N V r d hV (by linarith) hd policy) n []
        (OperationalSuccess N V n policy) := by
  have hp := physical_history_product (returnedPhysicalHistory N V r d hV (by linarith) hd policy)
    hscale hr hr' hd' n [] hN
  have hs : ENNReal.ofReal (1-oneCycleError V)^n ≤
      fullHistoryKernel (returnedHistoryStep N V r d hV (by linarith) hd policy) n [] (returnedFinal V n) := by
    apply hp.trans
    apply successful_history_event_lower _ _ _ n [] (returnedFinal V n) (Set.to_countable _).measurableSet
    simpa only [List.length_nil,Nat.zero_add] using
      returned_success_support N V r d hV (by linarith) hd policy n [] (by simp [returnedGood])
  have ht := full_history_has_trace N V r d hV (by linarith) hd policy n [] ⟨HistoryTrace.nil⟩
  have he : certifiedPhysicalHistory N V n policy =ᵐ[
      fullHistoryKernel (returnedHistoryStep N V r d hV (by linarith) hd policy) n []] returnedFinal V n := by
    filter_upwards [ht] with h hh
    change (h ∈ returnedFinal V n ∧ Nonempty (HistoryTrace N V policy h))=(h ∈ returnedFinal V n)
    simp only [hh,and_true]
  rw [← measure_congr he] at hs
  exact hs.trans (measure_mono (certified_history_operational N V n policy hN))

theorem product_dominates_linear (e : ℝ) (he : e ≤ 1) (n : ℕ) : 1-(n:ℝ)*e ≤ (1-e)^n := by
  have hp := one_add_mul_le_pow (a := -e) (by linarith : (-2:ℝ) ≤ -e) n
  simpa only [mul_neg,sub_eq_add_neg] using hp

/-- All ratios are on the same event; their denominators are strictly positive. -/
theorem operational_ratios (V n : ℕ) (hV : 0 < V) (hn : 0 < n)
    (h : ReturnedHistory) (hh : h ∈ returnedFinal V n) :
    0 < returnedTotal h 1 ∧ 0 < returnedTotal h 0 ∧
    1/224 ≤ returnedTotal h 1/(4*(n:ℝ)*V) ∧
    1/4320 ≤ returnedTotal h 0/(4*(n:ℝ)*V) ∧
    returnedTotal h 2/returnedTotal h 1 ≤ 280 ∧
    returnedTotal h 3/returnedTotal h 1 ≤ 280 ∧
    (returnedTotal h 2+returnedTotal h 3)/returnedTotal h 1 ≤ 560 ∧
    returnedTotal h 4/returnedTotal h 1 ≤ 56/5 ∧
    (returnedTotal h 2+returnedTotal h 3)/returnedTotal h 0 ≤ 10800 ∧
    returnedTotal h 4/returnedTotal h 0 ≤ 216 := by
  obtain ⟨ht,hx,hu,hw,hg⟩ := returned_joint_totals V n h hh
  have hv : 0 < (V:ℝ) := by exact_mod_cast hV
  have hn' : 0 < (n:ℝ) := by exact_mod_cast hn
  have ht' := mul_le_mul_of_nonneg_left (Nat.le_ceil ((V:ℝ)/56)) hn'.le
  have hx' := mul_le_mul_of_nonneg_left (Nat.le_ceil ((V:ℝ)/1080)) hn'.le
  have hg' := mul_le_mul_of_nonneg_left (Nat.floor_le (by positivity : 0 ≤ (V:ℝ)/5)) hn'.le
  have hp : 0 < (n:ℝ)*V := mul_pos hn' hv
  have ht0 : 0 < returnedTotal h 1 := by nlinarith
  have hx0 : 0 < returnedTotal h 0 := by nlinarith
  have hd : 0 < 4*(n:ℝ)*V := by positivity
  refine ⟨ht0,hx0,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · apply (le_div_iff₀ hd).mpr; nlinarith
  · apply (le_div_iff₀ hd).mpr; nlinarith
  · apply (div_le_iff₀ ht0).mpr; nlinarith
  · apply (div_le_iff₀ ht0).mpr; nlinarith
  · apply (div_le_iff₀ ht0).mpr; nlinarith
  · apply (div_le_iff₀ ht0).mpr; nlinarith
  · apply (div_le_iff₀ hx0).mpr; nlinarith
  · apply (div_le_iff₀ hx0).mpr; nlinarith

end
end FiniteCopyReactor
