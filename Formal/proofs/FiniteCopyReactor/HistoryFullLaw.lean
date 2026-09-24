import proofs.FiniteCopyReactor.HistorySurvival

namespace FiniteCopyReactor
noncomputable section
open Classical MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {H : Type*} [MeasurableSpace H]

def fullHistoryKernel (K : Kernel H H) : ℕ → Kernel H H
  | 0 => Kernel.id
  | n+1 => fullHistoryKernel K n ∘ₖ K

instance fullHistoryKernel_markov (K : Kernel H H) [IsMarkovKernel K] (n : ℕ) :
    IsMarkovKernel (fullHistoryKernel K n) := by
  induction n with
  | zero => change IsMarkovKernel Kernel.id; infer_instance
  | succ n ih =>
    letI := ih
    change IsMarkovKernel (fullHistoryKernel K n ∘ₖ K)
    infer_instance

theorem successful_history_le_full (K : Kernel H H) (S : Set H) (hS : MeasurableSet S)
    (n : ℕ) (h : H) : successfulHistoryKernel K S hS n h ≤ fullHistoryKernel K n h := by
  induction n generalizing h with
  | zero => exact le_rfl
  | succ n ih =>
    apply Measure.le_iff.mpr
    intro A hA
    rw [successfulHistoryKernel,fullHistoryKernel,Kernel.comp_apply' _ _ _ hA,
      Kernel.comp_apply' _ _ _ hA,Kernel.restrict_apply]
    exact (lintegral_mono (fun y => ih y A)).trans
      (lintegral_mono' Measure.restrict_le_self le_rfl)

/-- Success mass is bounded by an event of the original probability law whenever it is supported there. -/
theorem successful_history_event_lower (K : Kernel H H) (S : Set H) (hS : MeasurableSet S)
    (n : ℕ) (h : H) (A : Set H) (hA : MeasurableSet A)
    (hsupport : successfulHistoryKernel K S hS n h Aᶜ=0) :
    successfulHistoryKernel K S hS n h Set.univ ≤ fullHistoryKernel K n h A := by
  have he := measure_add_measure_compl (μ := successfulHistoryKernel K S hS n h) hA
  rw [hsupport,add_zero] at he
  rw [← he]
  exact successful_history_le_full K S hS n h A

end
end FiniteCopyReactor
