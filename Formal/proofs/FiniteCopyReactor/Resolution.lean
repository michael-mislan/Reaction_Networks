import proofs.FiniteCopyReactor.PhysicalHistoryInventory

namespace FiniteCopyReactor
noncomputable section
open Classical ProductiveRecovery MeasureTheory ProbabilityTheory RandomViability RandomViability.Binding
open scoped ENNReal

/-- Exact per-cycle success, cumulative accounting, and net synthesis on physical realizations. -/
def OperationalSuccess (N : Counts) (V n : ℕ) (policy : ReturnedHistory → Intervention) : Set ReturnedHistory :=
  {h | h ∈ returnedFinal V n ∧ Nonempty (HistoryTrace N V policy h) ∧
    (n:ℝ)*(Nat.ceil ((V:ℝ)/56):ℝ) ≤ returnedTotal h 1 ∧
    (n:ℝ)*(Nat.ceil ((V:ℝ)/1080):ℝ) ≤ returnedTotal h 0 ∧
    returnedTotal h 2 ≤ (n:ℝ)*(5*(V:ℝ)) ∧ returnedTotal h 3 ≤ (n:ℝ)*(5*(V:ℝ)) ∧
    returnedTotal h 4 ≤ (n:ℝ)*(Nat.floor ((V:ℝ)/5):ℝ) ∧
    ∀ tr : HistoryTrace N V policy h,((n:ℝ)/56-161/160)*(V:ℝ) ≤ tr.produced}

theorem certified_history_operational (N : Counts) (V n : ℕ) (policy : ReturnedHistory → Intervention)
    (hN : Restart V N) : certifiedPhysicalHistory N V n policy ⊆ OperationalSuccess N V n policy := by
  intro h hh
  obtain ⟨ht,hf,hu,hw,hg⟩ := returned_joint_totals V n h hh.1
  exact ⟨hh.1,hh.2,ht,hf,hu,hw,hg,fun tr => tr.certified_net_lower n hN hh.1⟩

/-- C2 finite-horizon source theorem: all outputs, costs and physical inventory share one law. -/
theorem finite_copy_reactor_horizon (N : Counts) (V : ℕ) (r d : ℝ)
    (hV : 0 < (V:ℝ)) (hr : 19 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25)
    (policy : ReturnedHistory → Intervention) (hscale : 200000000000 ≤ V) (hN : Restart V N) (n : ℕ) :
    ENNReal.ofReal (1-(n:ℝ)*oneCycleError V) ≤
      fullHistoryKernel (returnedHistoryStep N V r d hV (by linarith) hd policy) n []
        (OperationalSuccess N V n policy) :=
  (full_source_inventory_success N V r d hV hr hr' hd hd' policy hscale hN n).trans
    (measure_mono (certified_history_operational N V n policy hN))

/-- Explicit integer sizing with a nonempty restart set and uniform physical parameter/policy quantifiers. -/
theorem finite_copy_reactor_result (m : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ N : Counts,Restart (sufficientVolume m δ) N ∧
      ∀ (r d : ℝ) (hr : 19 ≤ r) (_hr' : r ≤ 21) (hd : 1/50 ≤ d) (_hd' : d ≤ 1/25)
        (policy : ReturnedHistory → Intervention),
      ENNReal.ofReal (1-δ) ≤
        fullHistoryKernel (returnedHistoryStep N (sufficientVolume m δ) r d
          (by have hs : 200000000000 ≤ sufficientVolume m δ := le_max_left _ _
              exact_mod_cast (show 0 < sufficientVolume m δ by omega))
          (by linarith) (by linarith) policy) m [] (OperationalSuccess N (sufficientVolume m δ) m policy) := by
  let V := sufficientVolume m δ
  let N : Counts := ![0,0,V,0,0,0]
  have hN : Restart V N := all_free_restart V
  refine ⟨N,hN,?_⟩
  intro r d hr hr' hd hd' policy
  have hs : 200000000000 ≤ V := le_max_left _ _
  have he := sufficient_volume_error m δ hδ
  have hl : 1-δ ≤ 1-(m:ℝ)*oneCycleError V := by linarith
  exact (ENNReal.ofReal_le_ofReal hl).trans (finite_copy_reactor_horizon N V r d
    (by exact_mod_cast (show 0 < V by omega)) hr hr' (by linarith) hd' policy hs hN m)

theorem finite_copy_reactor_hundred (N : Counts) (r d : ℝ)
    (hr : 19 ≤ r) (hr' : r ≤ 21) (hd : 1/50 ≤ d) (hd' : d ≤ 1/25)
    (policy : ReturnedHistory → Intervention) (hN : Restart 200000000000 N) :
    ENNReal.ofReal (99/100:ℝ) ≤
      fullHistoryKernel (returnedHistoryStep N 200000000000 r d (by norm_num) (by linarith) (by linarith) policy)
        100 [] (OperationalSuccess N 200000000000 100 policy) := by
  have he := hundred_cycle_error_budget
  have hl : (99/100:ℝ) ≤ 1-(100:ℝ)*oneCycleError 200000000000 := by linarith
  exact (ENNReal.ofReal_le_ofReal hl).trans (finite_copy_reactor_horizon N 200000000000 r d
    (by norm_num) hr hr' (by linarith) hd' policy (by norm_num) hN 100)

/-- Uniform extension to any measurable observed-history model with the literal conditional cycle law.
The model law is specified by PhysicalHistory; no success probability is assumed. -/
theorem finite_copy_reactor_adapted_history {H : Type*} [MeasurableSpace H]
    {V : ℕ} {r d : ℝ} {hV hr hd} (R : PhysicalHistory H V r d hV hr hd)
    (hscale : 200000000000 ≤ V) (hr19 : 19 ≤ r) (hr21 : r ≤ 21) (hd25 : d ≤ 1/25)
    (m : ℕ) (δ : ℝ) (hbudget : (m:ℝ)*oneCycleError V ≤ δ) (h : H) (hh : Restart V (R.current h)) :
    ENNReal.ofReal (1-δ) ≤ successfulHistoryKernel R.step (physicalHistorySuccess R)
      (physical_history_success_measurable R) m h Set.univ := by
  have hl : 1-δ ≤ 1-(m:ℝ)*oneCycleError V := by linarith
  exact (ENNReal.ofReal_le_ofReal hl).trans (physical_history_success_lower R hscale hr19 hr21 hd25 m h hh)

end
end FiniteCopyReactor
