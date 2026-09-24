import proofs.FiniteCopyReactor.JointSourceBridge
import proofs.FiniteCopyReactor.JointTrajectory
import proofs.FiniteCopyReactor.EndpointOperators

namespace FiniteCopyReactor
noncomputable section
open Classical MeasureTheory ProbabilityTheory RandomViability FiniteCopy
open scoped ENNReal

def sourceStoppedCycle (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ))
    (hr : 0 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25)
    (f : JointCounts → ℝ≥0∞) (X : JointCounts) : ℝ≥0∞ :=
  causalClockEndpoint (jointSourceClock false false V r d hV hr hr' hd hd') (3000*(V:ℝ))
    (fun Y => causalClockEndpoint (jointSourceClock true false V r d hV hr hr' hd hd') (3000*(V:ℝ))
      (fun Z => causalClockEndpoint (jointSourceClock true true V r d hV hr hr' hd hd') (3000*(V:ℝ)) f Z 1)
      Y (1/4)) X (11/4)

/-- Unrestricted chronological phases retain the actual population and all five counters. -/
def jointSourceCycle (V r d : ℝ) (hV : 0 < V) (hr : 0 ≤ r) (hd : 0 ≤ d)
    (f : JointCounts → ℝ≥0∞) (X : JointCounts) : ℝ≥0∞ :=
  jointSourceEndpoint false V r d hV hr hd
    (fun Y => jointSourceEndpoint false V r d hV hr hd
      (fun Z => jointSourceEndpoint true V r d hV hr hd f Z 1) Y (1/4)) X (11/4)

theorem source_endpoint_mono (collect : Bool) (V r d : ℝ) (hV : 0 < V) (hr : 0 ≤ r) (hd : 0 ≤ d)
    (f g : JointCounts → ℝ≥0∞) (h : ∀ X,f X ≤ g X) (X : JointCounts) (T : ℝ) :
    jointSourceEndpoint collect V r d hV hr hd f X T ≤ jointSourceEndpoint collect V r d hV hr hd g X T :=
  chronological_endpoint_mono _ _ _ _ f g h X T

theorem source_cycle_transfer (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ))
    (hr : 0 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25)
    (f : JointCounts → ℝ≥0∞) (hf : ∀ X,f X ≤ 1)
    (hzero : ∀ X,X ∉ jointCountActive true V → f X=0) (X : JointCounts) :
    sourceStoppedCycle V r d hV hr hr' hd hd' f X ≤ jointSourceCycle V r d hV hr hd f X := by
  let Q := fun b collect g Y T => causalClockEndpoint
    (jointSourceClock b collect V r d hV hr hr' hd hd') (3000*(V:ℝ)) g Y T
  let A := fun Y => Q true true f Y 1
  let B := fun Y => Q true false A Y (1/4)
  let R := fun Y => jointSourceEndpoint true V r d hV hr hd f Y 1
  let S := fun Y => jointSourceEndpoint false V r d hV hr hd R Y (1/4)
  have hq : 0 < 3000*(V:ℝ) := by positivity
  have hA (Y : JointCounts) : A Y ≤ R Y := by
    have hh := joint_source_clock_le true true V r d hV hr hr' hd hd' f hf Y 1
    rw [mask_eq_of_zero _ f hzero] at hh
    exact hh
  have hA1 (Y : JointCounts) : A Y ≤ 1 :=
    causal_clock_le_one _ _ hq.le f hf Y 1
  have hA0 (Y : JointCounts) (hy : Y ∉ jointCountActive true V) : A Y=0 :=
    stopped_clock_outside _ _ _ _ _ hq _ f Y hy (hzero Y hy) 1
  have hB (Y : JointCounts) : B Y ≤ S Y := by
    have hh := joint_source_clock_le true false V r d hV hr hr' hd hd' A hA1 Y (1/4)
    rw [mask_eq_of_zero _ A hA0] at hh
    exact hh.trans (source_endpoint_mono false V r d hV hr hd A R hA Y (1/4))
  have hB1 (Y : JointCounts) : B Y ≤ 1 :=
    causal_clock_le_one _ _ hq.le A hA1 Y (1/4)
  have hB0 (Y : JointCounts) (hy : Y ∉ jointCountActive true V) : B Y=0 :=
    stopped_clock_outside _ _ _ _ _ hq _ A Y hy (hA0 Y hy) (1/4)
  have hBm (Y : JointCounts) (hy : Y ∉ jointCountActive false V) : B Y=0 := by
    apply hB0 Y
    intro hs
    exact hy (count_active_material true V Y.1 hs)
  have hh := joint_source_clock_le false false V r d hV hr hr' hd hd' B hB1 X (11/4)
  rw [mask_eq_of_zero _ B hBm] at hh
  exact hh.trans (source_endpoint_mono false V r d hV hr hd B S hB X (11/4))

end
end FiniteCopyReactor
