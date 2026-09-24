import proofs.FiniteReservoir.ReturnedTotals

namespace FiniteReservoir
noncomputable section
open Classical ProductiveRecovery MeasureTheory ProbabilityTheory RandomViability RandomViability.Binding FiniteCopyReactor
open scoped ENNReal

theorem full_returned_history_product (M : ℕ) (N : CountState M) (V : ℕ) (params : Parameters M)
    (hV : 0 < (V:ℝ)) (policy : ReturnedHistory M → Intervention)
    (hlarge : 1000000 ≤ V) (hN : Restart V N.1) (n : ℕ) :
    ENNReal.ofReal (1-oneCycleError V)^n ≤
      fullHistoryKernel (returnedHistoryStep M N V params hV policy) n [] (returnedFinal V M n) := by
  have hp := physical_history_product (returnedPhysicalHistory M N V params hV policy) hlarge n [] hN
  apply hp.trans
  apply successful_history_event_lower _ _ _ n [] (returnedFinal V M n) (Set.to_countable _).measurableSet
  simpa only [List.length_nil,Nat.zero_add] using
    returned_success_support M N V params hV policy n [] (by simp [returnedGood])

end
end FiniteReservoir
