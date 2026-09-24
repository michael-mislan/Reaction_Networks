import proofs.FiniteCopyReactor.StoppedClock
import proofs.FiniteCopyReactor.KilledChronology
import proofs.FiniteCopyReactor.KilledEndpointUniqueness

namespace FiniteCopyReactor
noncomputable section
open Classical MeasureTheory ProbabilityTheory RandomViability FiniteCopy
open scoped ENNReal

variable {α β : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
  [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]

/-- Exact agreement before first exit. The original process is unrestricted and may
have unbounded rates away from the safe set. -/
theorem stopped_clock_eq_killed_chronology (D : Set α) (next : α → β → α) (rate : α → β → ℝ)
    (hr : ∀ x b,0 ≤ rate x b) (ht : ∀ x,0 < ∑ b,rate x b)
    (q : ℝ) (hq : 0 < q) (hb : ∀ x ∈ D,(∑ b,rate x b) ≤ q)
    (f : α → ℝ≥0∞) (hf : ∀ x,f x ≤ 1) (x : α) (T : ℝ) :
    causalClockEndpoint (stoppedClockKernel D next rate hr q hq hb) q
      (fun y => if y ∈ D then f y else 0) x T=
      killedChronologicalEndpoint D next rate hr ht f x T := by
  let fm := fun y => if y ∈ D then f y else 0
  let P := stoppedClockKernel D next rate hr q hq hb
  let C := causalClockEndpoint P q fm
  let F := fun p : ℝ × α => C p.2 p.1
  let G := fun p : ℝ × α => killedChronologicalEndpoint D next rate hr ht f p.2 p.1
  let B := fun p : ℝ × α => if p.2 ∈ D then f p.2*survivalKernel (∑ b,rate p.2 b) p.1 else 0
  have hfm1 (y : α) : fm y ≤ 1 := by
    dsimp only [fm]
    split_ifs
    · exact hf y
    · exact zero_le
  have he : F=G := by
    apply killed_endpoint_renewal_unique D next rate hr ht q hq.le hb F G B
      (causal_clock_measurable P q fm) (killed_chronological_measurable D next rate hr ht f)
    · intro p
      exact causal_clock_le_one P q hq.le fm hfm1 p.2 p.1
    · intro p
      exact killed_chronological_le_one D next rate hr ht f hf p.2 p.1
    · intro p hp
      exact if_neg (not_le.mpr hp)
    · intro p hp
      exact killed_chronological_negative D next rate hr ht f p.2 p.1 hp
    · intro p hp
      exact stopped_clock_outside D next rate hr q hq hb fm p.2 hp (if_neg hp) p.1
    · intro p hp
      exact killed_chronological_outside D next rate hr ht f p.2 p.1 hp
    · intro p hp
      exact if_neg hp
    · intro p hp
      change C p.2 p.1=(if p.2 ∈ D then f p.2*survivalKernel (∑ b,rate p.2 b) p.1 else 0)+
        ∫⁻ y,C (next p.2 y.1) (p.1-y.2) ∂jumpClockMeasure (rate p.2) (hr p.2) (ht p.2)
      rw [if_pos hp]
      have hh := stopped_clock_active_renewal D next rate hr q hq hb fm hfm1 p.2 hp (ht p.2) p.1
      change C p.2 p.1=fm p.2*survivalKernel (∑ b,rate p.2 b) p.1+
        ∫⁻ y,C (next p.2 y.1) (p.1-y.2) ∂jumpClockMeasure (rate p.2) (hr p.2) (ht p.2) at hh
      rw [show fm p.2=f p.2 from if_pos hp] at hh
      exact hh
    · intro p hp
      change killedChronologicalEndpoint D next rate hr ht f p.2 p.1=
        (if p.2 ∈ D then f p.2*survivalKernel (∑ b,rate p.2 b) p.1 else 0)+
          ∫⁻ y,killedChronologicalEndpoint D next rate hr ht f (next p.2 y.1) (p.1-y.2)
            ∂jumpClockMeasure (rate p.2) (hr p.2) (ht p.2)
      rw [if_pos hp]
      have hm : Measurable (fun y : β × ℝ => if 0 ≤ p.1 ∧ p.1 < y.2 then f p.2 else 0) :=
        Measurable.ite ((measurableSet_le
          (show Measurable (fun _ : β × ℝ => (0:ℝ)) from measurable_const)
          (show Measurable (fun _ : β × ℝ => p.1) from measurable_const)).inter
          (measurableSet_lt (show Measurable (fun _ : β × ℝ => p.1) from measurable_const) measurable_snd))
          measurable_const measurable_const
      have hh := killed_chronological_renewal D next rate hr ht f p.2 p.1
      rw [if_pos hp] at hh
      exact hh.trans ((lintegral_add_left hm _).trans
        (congrArg₂ (fun a b : ℝ≥0∞ => a+b)
          (jump_no_event_integral (rate p.2) (hr p.2) (ht p.2) (f p.2) p.1) rfl))
  exact congrFun he (T,x)

/-- A safely stopped-clock payoff lower-bounds the same payoff on the unrestricted process. -/
theorem stopped_clock_le_unrestricted (D : Set α) (next : α → β → α) (rate : α → β → ℝ)
    (hr : ∀ x b,0 ≤ rate x b) (ht : ∀ x,0 < ∑ b,rate x b)
    (q : ℝ) (hq : 0 < q) (hb : ∀ x ∈ D,(∑ b,rate x b) ≤ q)
    (f : α → ℝ≥0∞) (hf : ∀ x,f x ≤ 1) (x : α) (T : ℝ) :
    causalClockEndpoint (stoppedClockKernel D next rate hr q hq hb) q
      (fun y => if y ∈ D then f y else 0) x T ≤ chronologicalEndpoint next rate hr ht f x T := by
  rw [stopped_clock_eq_killed_chronology D next rate hr ht q hq hb f hf]
  exact killed_chronological_le D next rate hr ht f x T

end
end FiniteCopyReactor
