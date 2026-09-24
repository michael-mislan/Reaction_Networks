import proofs.FiniteReservoir.JointSourceBridge
import proofs.FiniteReservoir.JointTrajectory
import proofs.FiniteCopyReactor.EndpointOperators

namespace FiniteReservoir
noncomputable section
open Classical FiniteCopyReactor MeasureTheory ProbabilityTheory RandomViability FiniteCopy
open scoped ENNReal

def sourceStoppedCycle (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ))
    
    (f : JointCounts M → ℝ≥0∞) (X : JointCounts M) : ℝ≥0∞ :=
  causalClockEndpoint (jointSourceClock false false V M p hV) (3000*(V:ℝ))
    (fun Y => causalClockEndpoint (jointSourceClock true false V M p hV) (3000*(V:ℝ))
      (fun Z => causalClockEndpoint (jointSourceClock true true V M p hV) (3000*(V:ℝ)) f Z 1)
      Y (1/4)) X (11/4)

/-- Unrestricted chronological phases retain the actual population and all five counters. -/
def jointSourceCycle (V : ℝ) (M : ℕ) (p : Parameters M) (hV : 0 < V) 
    (f : JointCounts M → ℝ≥0∞) (X : JointCounts M) : ℝ≥0∞ :=
  jointSourceEndpoint false V M p hV
    (fun Y => jointSourceEndpoint false V M p hV
      (fun Z => jointSourceEndpoint true V M p hV f Z 1) Y (1/4)) X (11/4)

theorem source_endpoint_mono (collect : Bool) (V : ℝ) (M : ℕ) (p : Parameters M) (hV : 0 < V) 
    (f g : JointCounts M → ℝ≥0∞) (h : ∀ X,f X ≤ g X) (X : JointCounts M) (T : ℝ) :
    jointSourceEndpoint collect V M p hV f X T ≤ jointSourceEndpoint collect V M p hV g X T :=
  chronological_endpoint_mono _ _ _ _ f g h X T

theorem source_cycle_transfer (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ))
    
    (f : JointCounts M → ℝ≥0∞) (hf : ∀ X,f X ≤ 1)
    (hzero : ∀ X,X ∉ jointCountActive true V M → f X=0) (X : JointCounts M) :
    sourceStoppedCycle V M p hV f X ≤ jointSourceCycle V M p hV f X := by
  let Q := fun b collect g Y T => causalClockEndpoint
    (jointSourceClock b collect V M p hV) (3000*(V:ℝ)) g Y T
  let A := fun Y => Q true true f Y 1
  let B := fun Y => Q true false A Y (1/4)
  let R := fun Y => jointSourceEndpoint true V M p hV f Y 1
  let S := fun Y => jointSourceEndpoint false V M p hV R Y (1/4)
  have hq : 0 < 3000*(V:ℝ) := by positivity
  have hA (Y : JointCounts M) : A Y ≤ R Y := by
    have hh := joint_source_clock_le true true V M p hV f hf Y 1
    rw [mask_eq_of_zero _ f hzero] at hh
    exact hh
  have hA1 (Y : JointCounts M) : A Y ≤ 1 :=
    causal_clock_le_one _ _ hq.le f hf Y 1
  have hA0 (Y : JointCounts M) (hy : Y ∉ jointCountActive true V M) : A Y=0 :=
    stopped_clock_outside _ _ _ _ _ hq _ f Y hy (hzero Y hy) 1
  have hB (Y : JointCounts M) : B Y ≤ S Y := by
    have hh := joint_source_clock_le true false V M p hV A hA1 Y (1/4)
    rw [mask_eq_of_zero _ A hA0] at hh
    exact hh.trans (source_endpoint_mono false V M p hV A R hA Y (1/4))
  have hB1 (Y : JointCounts M) : B Y ≤ 1 :=
    causal_clock_le_one _ _ hq.le A hA1 Y (1/4)
  have hB0 (Y : JointCounts M) (hy : Y ∉ jointCountActive true V M) : B Y=0 :=
    stopped_clock_outside _ _ _ _ _ hq _ A Y hy (hA0 Y hy) (1/4)
  have hBm (Y : JointCounts M) (hy : Y ∉ jointCountActive false V M) : B Y=0 := by
    apply hB0 Y
    intro hs
    exact hy (count_active_material true V Y.1.1 hs)
  have hh := joint_source_clock_le false false V M p hV B hB1 X (11/4)
  rw [mask_eq_of_zero _ B hBm] at hh
  exact hh.trans (source_endpoint_mono false V M p hV B S hB X (11/4))

end
end FiniteReservoir
