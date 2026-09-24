import proofs.FiniteReservoir.IntegerMarks
import proofs.FiniteReservoir.PhysicalSource
import proofs.FiniteReservoir.StoppingSemantics
import proofs.FiniteCopyReactor.JointCountSource

namespace FiniteReservoir
noncomputable section
open Classical ProductiveRecovery RandomViability.Binding RandomViability MeasureTheory ProbabilityTheory FiniteCopy FiniteCopyReactor
open scoped ENNReal BigOperators

theorem countState_injective (M : ℕ) : Function.Injective (countState (M := M)) := by
  intro X Y h
  apply Prod.ext
  · exact congrArg (fun s : State => s.1) h
  · apply Fin.ext
    exact congrArg (fun s : State => s.2.fuel) h

abbrev JointCounts (M : ℕ) := CountState M × IntegerCounters

def jointReactorRate (V : ℝ) (M : ℕ) (p : Parameters M) (X : JointCounts M) (j : CompetitionChannel) : ℝ := reactorRate M p V X.1 j

def jointReactorNext {M : ℕ} (collect : Bool) (X : JointCounts M) (j : CompetitionChannel) : JointCounts M :=
  (reactorNext X.1 j,fun i => X.2 i+integerCycleMarks collect j i)

theorem joint_reactor_nonneg (V : ℝ) (M : ℕ) (p : Parameters M) (hV : 0 < V)  :
    ∀ X j,0 ≤ jointReactorRate V M p X j := fun X => reactor_rate_nonneg M p V hV X.1

theorem joint_reactor_total_pos (V : ℝ) (M : ℕ) (p : Parameters M) (hV : 0 < V)  :
    ∀ X,0 < ∑ j,jointReactorRate V M p X j := fun X => reactor_total_pos M p V hV X.1

def jointCountActive (stopStock : Bool) (V M : ℕ) : Set (JointCounts M) := {X | countSegmentActive stopStock V X.1.1}

theorem joint_count_rate_bound (b : Bool) (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ))
     :
    ∀ X ∈ jointCountActive b V M,(∑ j,jointReactorRate V M p X j) ≤ 3000*(V:ℝ) := by
  intro X hX
  have ha := count_active_material b V X.1.1 hX
  simp only [jointReactorRate,reactorRate,rate_binding,countState]
  exact total_rate_bound X.1.1 V p.release _ _ hV (by linarith [p.release_lower])
    p.release_upper (parameters_box p X.1.2) ha


def integerCountState {V M : ℕ} (X : BoxState V M × IntegerCounters) : JointCounts M := ((boxCounts X.1.1,X.1.2),X.2)

theorem integer_count_active (b : Bool) (V M : ℕ) (X : BoxState V M × IntegerCounters) :
    integerCountState X ∈ jointCountActive b V M ↔ segmentActive b V M X.1 := by
  cases b <;> rfl

def jointSourceClock (b collect : Bool) (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ))
     :=
  stoppedClockKernel (jointCountActive b V M) (jointReactorNext collect) (jointReactorRate V M p)
    (joint_reactor_nonneg V M p hV) (3000*(V:ℝ)) (by positivity)
    (joint_count_rate_bound b V M p hV)

def jointSourceEndpoint (collect : Bool) (V : ℝ) (M : ℕ) (p : Parameters M) (hV : 0 < V) 
    (f : JointCounts M → ℝ≥0∞) (X : JointCounts M) (T : ℝ) : ℝ≥0∞ :=
  chronologicalEndpoint (jointReactorNext collect) (jointReactorRate V M p)
    (joint_reactor_nonneg V M p hV) (joint_reactor_total_pos V M p hV) f X T

theorem joint_source_clock_le (b collect : Bool) (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ))
    
    (f : JointCounts M → ℝ≥0∞) (hf : ∀ X,f X ≤ 1) (X : JointCounts M) (T : ℝ) :
    causalClockEndpoint (jointSourceClock b collect V M p hV) (3000*(V:ℝ))
      (fun Y => if Y ∈ jointCountActive b V M then f Y else 0) X T ≤
      jointSourceEndpoint collect V M p hV f X T :=
  stopped_clock_le_unrestricted (jointCountActive b V M) (jointReactorNext collect) (jointReactorRate V M p)
    (joint_reactor_nonneg V M p hV) (joint_reactor_total_pos V M p hV)
    (3000*(V:ℝ)) (by positivity) (joint_count_rate_bound b V M p hV) f hf X T

end
end FiniteReservoir
