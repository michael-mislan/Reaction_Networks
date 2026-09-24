import proofs.FiniteCopyReactor.ReturnedHistory
import proofs.FiniteCopyReactor.HistoryFullLaw

namespace FiniteCopyReactor
noncomputable section
open Classical ProductiveRecovery MeasureTheory ProbabilityTheory RandomViability RandomViability.Binding
open scoped ENNReal

def returnedGood (V : ℕ) (h : ReturnedHistory) : Prop := ∀ X ∈ h,CountCycleSuccess V X
def returnedFinal (V L : ℕ) : Set ReturnedHistory := {h | h.length=L ∧ returnedGood V h}

theorem returned_success_support (N : Counts) (V : ℕ) (r d : ℝ)
    (hV : 0 < (V:ℝ)) (hr : 0 ≤ r) (hd : 0 ≤ d) (policy : ReturnedHistory → Intervention)
    (n : ℕ) (h : ReturnedHistory) (hh : returnedGood V h) :
    successfulHistoryKernel (returnedHistoryStep N V r d hV hr hd policy)
      (physicalHistorySuccess (returnedPhysicalHistory N V r d hV hr hd policy))
      (physical_history_success_measurable _) n h (returnedFinal V (h.length+n))ᶜ=0 := by
  let K := returnedHistoryStep N V r d hV hr hd policy
  let R := returnedPhysicalHistory N V r d hV hr hd policy
  let S := physicalHistorySuccess R
  have hS := physical_history_success_measurable R
  change successfulHistoryKernel K S hS n h (returnedFinal V (h.length+n))ᶜ=0
  induction n generalizing h with
  | zero =>
    have hm : h ∈ returnedFinal V (h.length+0) := ⟨by omega,hh⟩
    simp only [successfulHistoryKernel,Kernel.id_apply,Measure.dirac_apply'
      (h) (Set.to_countable ((returnedFinal V (h.length+0))ᶜ)).measurableSet]
    exact Set.indicator_of_notMem (not_not.mpr hm) _
  | succ n ih =>
    let A := (returnedFinal V (h.length+(n+1)))ᶜ
    have hA : MeasurableSet A := (Set.to_countable A).measurableSet
    rw [successfulHistoryKernel,Kernel.comp_apply' _ _ _ hA,Kernel.restrict_apply,
      ← lintegral_indicator hS]
    change (∫⁻ y,S.indicator (fun z => successfulHistoryKernel K S hS n z A) y
      ∂(literalPulseCycleMeasure (returnedObservation N h).1 V (policy h) r d hV hr hd).map (fun X => X::h))=0
    rw [lintegral_map (measurable_of_countable _) (measurable_of_countable _)]
    apply (lintegral_eq_zero_iff (measurable_of_countable _)).mpr
    apply Filter.Eventually.of_forall
    intro X
    change S.indicator (fun z => successfulHistoryKernel K S hS n z A) (X::h)=0
    by_cases hx : CountCycleSuccess V X
    · have hs : X::h ∈ S := hx
      rw [Set.indicator_of_mem hs]
      have hg : returnedGood V (X::h) := by
        intro Y hy
        rcases List.mem_cons.mp hy with hY | hY
        · simpa only [hY] using hx
        · exact hh Y hY
      have hi := ih (X::h) hg
      have he : (X::h).length+n=h.length+(n+1) := by simp only [List.length_cons]; omega
      rw [he] at hi
      exact hi
    · have hs : X::h ∉ S := hx
      exact Set.indicator_of_notMem hs _

end
end FiniteCopyReactor
