import proofs.FiniteReservoir.ReturnedHistory
import proofs.FiniteCopyReactor.HistoryFullLaw

namespace FiniteReservoir
noncomputable section
open Classical FiniteCopyReactor ProductiveRecovery MeasureTheory ProbabilityTheory RandomViability RandomViability.Binding
open scoped ENNReal

def returnedGood (V M : ℕ) (h : (ReturnedHistory M)) : Prop := ∀ X ∈ h,CountCycleSuccess V M X
def returnedFinal (V M L : ℕ) : Set (ReturnedHistory M) := {h | h.length=L ∧ returnedGood V M h}

theorem returned_success_support (M : ℕ) (N : CountState M) (V : ℕ) (params : Parameters M)
    (hV : 0 < (V:ℝ))  (policy : (ReturnedHistory M) → Intervention)
    (n : ℕ) (h : (ReturnedHistory M)) (hh : returnedGood V M h) :
    successfulHistoryKernel (returnedHistoryStep M N V params hV policy)
      (physicalHistorySuccess (returnedPhysicalHistory M N V params hV policy))
      (physical_history_success_measurable _) n h (returnedFinal V M (h.length+n))ᶜ=0 := by
  let K := returnedHistoryStep M N V params hV policy
  let R := returnedPhysicalHistory M N V params hV policy
  let S := physicalHistorySuccess R
  have hS := physical_history_success_measurable R
  change successfulHistoryKernel K S hS n h (returnedFinal V M (h.length+n))ᶜ=0
  induction n generalizing h with
  | zero =>
    have hm : h ∈ returnedFinal V M (h.length+0) := ⟨by omega,hh⟩
    simp only [successfulHistoryKernel,Kernel.id_apply,Measure.dirac_apply'
      (h) (Set.to_countable ((returnedFinal V M (h.length+0))ᶜ)).measurableSet]
    exact Set.indicator_of_notMem (not_not.mpr hm) _
  | succ n ih =>
    let A := (returnedFinal V M (h.length+(n+1)))ᶜ
    have hA : MeasurableSet A := (Set.to_countable A).measurableSet
    rw [successfulHistoryKernel,Kernel.comp_apply' _ _ _ hA,Kernel.restrict_apply,
      ← lintegral_indicator hS]
    change (∫⁻ y,S.indicator (fun z => successfulHistoryKernel K S hS n z A) y
      ∂(literalPulseCycleMeasure (returnedObservation N h).1.1 V M (policy h) params (returnedObservation N h).1.2 hV).map (fun X => X::h))=0
    rw [lintegral_map (measurable_of_countable _) (measurable_of_countable _)]
    apply (lintegral_eq_zero_iff (measurable_of_countable _)).mpr
    apply Filter.Eventually.of_forall
    intro X
    change S.indicator (fun z => successfulHistoryKernel K S hS n z A) (X::h)=0
    by_cases hx : CountCycleSuccess V M X
    · have hs : X::h ∈ S := hx
      rw [Set.indicator_of_mem hs]
      have hg : returnedGood V M (X::h) := by
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
end FiniteReservoir
