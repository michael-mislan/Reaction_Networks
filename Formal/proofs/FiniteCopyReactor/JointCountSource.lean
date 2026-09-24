import proofs.FiniteCopyReactor.IntegerMarks
import proofs.FiniteCopyReactor.StoppingSemantics
import proofs.FiniteCopyReactor.StoppedAgreement

namespace FiniteCopyReactor
noncomputable section
open Classical ProductiveRecovery RandomViability.Binding RandomViability MeasureTheory ProbabilityTheory FiniteCopy
open scoped ENNReal BigOperators

abbrev JointCounts := Counts × IntegerCounters

def jointReactorRate (V r d : ℝ) (X : JointCounts) (j : CompetitionChannel) : ℝ := reactorRate V r d X.1 j

def jointReactorNext (collect : Bool) (X : JointCounts) (j : CompetitionChannel) : JointCounts :=
  (reactorNext X.1 j,fun i => X.2 i+integerCycleMarks collect j i)

theorem joint_reactor_nonneg (V r d : ℝ) (hV : 0 < V) (hr : 0 ≤ r) (hd : 0 ≤ d) :
    ∀ X j,0 ≤ jointReactorRate V r d X j := fun X => reactor_rate_nonneg V r d hV hr hd X.1

theorem joint_reactor_total_pos (V r d : ℝ) (hV : 0 < V) (hr : 0 ≤ r) (hd : 0 ≤ d) :
    ∀ X,0 < ∑ j,jointReactorRate V r d X j := fun X => reactor_total_pos V r d hV hr hd X.1

def countSegmentActive (stopStock : Bool) (V : ℕ) (N : Counts) : Prop :=
  if stopStock then resourceGood N V ∧ (V:ℝ)/20 < weightedCount N else resourceGood N V

def jointCountActive (stopStock : Bool) (V : ℕ) : Set JointCounts := {X | countSegmentActive stopStock V X.1}

theorem count_active_material (b : Bool) (V : ℕ) (N : Counts) (h : countSegmentActive b V N) :
    resourceGood N V := by
  cases b
  · exact h
  · exact h.1

theorem joint_count_rate_bound (b : Bool) (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ))
    (hr : 0 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25) :
    ∀ X ∈ jointCountActive b V,(∑ j,jointReactorRate V r d X j) ≤ 3000*(V:ℝ) := by
  intro X hX
  have ha := count_active_material b V X.1 hX
  apply competition_total_rate_bound X.1 V (1/500000000) (1/10) r d hV
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hr (by linarith) hd (by linarith)
  intro i
  linarith [resource_count_cap X.1 V ha i]

def integerCountState {V : ℕ} (X : BoxCounts V × IntegerCounters) : JointCounts := (boxCounts X.1,X.2)

theorem integer_count_active (b : Bool) (V : ℕ) (X : BoxCounts V × IntegerCounters) :
    integerCountState X ∈ jointCountActive b V ↔ segmentActive b V X.1 := by
  cases b <;> rfl

def jointSourceClock (b collect : Bool) (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ))
    (hr : 0 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25) :=
  stoppedClockKernel (jointCountActive b V) (jointReactorNext collect) (jointReactorRate V r d)
    (joint_reactor_nonneg V r d hV hr hd) (3000*(V:ℝ)) (by positivity)
    (joint_count_rate_bound b V r d hV hr hr' hd hd')

def jointSourceEndpoint (collect : Bool) (V r d : ℝ) (hV : 0 < V) (hr : 0 ≤ r) (hd : 0 ≤ d)
    (f : JointCounts → ℝ≥0∞) (X : JointCounts) (T : ℝ) : ℝ≥0∞ :=
  chronologicalEndpoint (jointReactorNext collect) (jointReactorRate V r d)
    (joint_reactor_nonneg V r d hV hr hd) (joint_reactor_total_pos V r d hV hr hd) f X T

theorem joint_source_clock_le (b collect : Bool) (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ))
    (hr : 0 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25)
    (f : JointCounts → ℝ≥0∞) (hf : ∀ X,f X ≤ 1) (X : JointCounts) (T : ℝ) :
    causalClockEndpoint (jointSourceClock b collect V r d hV hr hr' hd hd') (3000*(V:ℝ))
      (fun Y => if Y ∈ jointCountActive b V then f Y else 0) X T ≤
      jointSourceEndpoint collect V r d hV hr hd f X T :=
  stopped_clock_le_unrestricted (jointCountActive b V) (jointReactorNext collect) (jointReactorRate V r d)
    (joint_reactor_nonneg V r d hV hr hd) (joint_reactor_total_pos V r d hV hr hd)
    (3000*(V:ℝ)) (by positivity) (joint_count_rate_bound b V r d hV hr hr' hd hd') f hf X T

end
end FiniteCopyReactor
