import proofs.FiniteCopyReactor.ClockSemigroup
import proofs.FiniteCopyReactor.StoppedAgreement
import proofs.FiniteCopyReactor.EndpointOperators

namespace FiniteCopyReactor
noncomputable section
open Classical MeasureTheory ProbabilityTheory RandomViability FiniteCopy
open scoped ENNReal

variable {α β : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
  [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]

theorem stopped_clock_nn (D : Set α) (next : α → β → α) (rate : α → β → ℝ)
    (hr : ∀ x b,0 ≤ rate x b) (ht : ∀ x,0 < ∑ b,rate x b)
    (q : NNReal) (hq : 0 < (q:ℝ)) (hb : ∀ x ∈ D,(∑ b,rate x b) ≤ q)
    (f : α → ℝ≥0∞) (hf : ∀ x,f x ≤ 1) (x : α) (T : NNReal) :
    clockEndpoint (stoppedClockKernel D next rate hr q hq hb) q T
      (fun y => if y ∈ D then f y else 0) x=
      killedChronologicalEndpoint D next rate hr ht f x T := by
  have hh := stopped_clock_eq_killed_chronology D next rate hr ht q hq hb f hf x T
  have hT : (0:ℝ) ≤ (T:ℝ) := T.property
  simpa only [causalClockEndpoint,hT,if_true] using hh

theorem killed_chronological_semigroup (D : Set α) (next : α → β → α) (rate : α → β → ℝ)
    (hr : ∀ x b,0 ≤ rate x b) (ht : ∀ x,0 < ∑ b,rate x b)
    (q : NNReal) (hq : 0 < (q:ℝ)) (hb : ∀ x ∈ D,(∑ b,rate x b) ≤ q)
    (f : α → ℝ≥0∞) (hf : ∀ x,f x ≤ 1) (x : α) (t u : NNReal) :
    killedChronologicalEndpoint D next rate hr ht f x (t+u)=
      killedChronologicalEndpoint D next rate hr ht
        (fun y => killedChronologicalEndpoint D next rate hr ht f y u) x t := by
  let g := fun y => killedChronologicalEndpoint D next rate hr ht f y u
  have hg (y) : g y ≤ 1 := killed_chronological_le_one D next rate hr ht f hf y u
  have hz (y) (hy : y ∉ D) : g y=0 := killed_chronological_outside D next rate hr ht f y u hy
  have hm : (fun y => if y ∈ D then g y else 0)=g := mask_eq_of_zero D g hz
  have hleft := stopped_clock_nn D next rate hr ht q hq hb f hf x (t+u)
  have hright := stopped_clock_nn D next rate hr ht q hq hb g hg x t
  rw [hm] at hright
  have hinner : (fun y => clockEndpoint (stoppedClockKernel D next rate hr q hq hb) q u
      (fun w => if w ∈ D then f w else 0) y)=g := by
    funext y
    exact stopped_clock_nn D next rate hr ht q hq hb f hf y u
  have hs := clock_endpoint_semigroup (stoppedClockKernel D next rate hr q hq hb)
    q t u (fun y => if y ∈ D then f y else 0) x
  rw [hinner] at hs
  exact hleft.symm.trans (hs.trans hright)

end
end FiniteCopyReactor
