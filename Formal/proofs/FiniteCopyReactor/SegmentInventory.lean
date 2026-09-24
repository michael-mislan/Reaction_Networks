import proofs.FiniteCopyReactor.CycleInventory
import proofs.FiniteCopyReactor.SourceCycleMeasure

namespace FiniteCopyReactor
noncomputable section
open Classical ProductiveRecovery MeasureTheory ProbabilityTheory RandomViability RandomViability.Binding
open scoped ENNReal BigOperators

/-- A finite physical reaction trace retains the joint state and literal integer counter increments. -/
structure SegmentTrace (collect : Bool) (X Y : JointCounts) where
  length : ℕ
  state : ℕ → JointCounts
  label : ℕ → CompetitionChannel
  start : state 0=X
  finish : state length=Y
  available : ∀ k < length,∀ i,reactants (competitionBase (label k)) i ≤ (state k).1 i
  next : ∀ k < length,(state (k+1)).1=competitionNext (state k).1 (label k)
  counters : ∀ k < length,∀ i,(state (k+1)).2 i=(state k).2 i+integerCycleMarks collect (label k) i

def SegmentTrace.produced {collect X Y} (tr : SegmentTrace collect X Y) : ℝ :=
  ∑ k ∈ Finset.range tr.length,synthesisMark (tr.label k)
def SegmentTrace.exported {collect X Y} (tr : SegmentTrace collect X Y) : ℝ :=
  ∑ k ∈ Finset.range tr.length,templateMark (tr.label k)

theorem SegmentTrace.inventory {collect X Y} (tr : SegmentTrace collect X Y) :
    templateStock Y.1+tr.exported=templateStock X.1+tr.produced := by
  have hh := finite_path_inventory tr.length (fun k => (tr.state k).1) tr.label tr.available tr.next
  change templateStock (tr.state tr.length).1-templateStock (tr.state 0).1=tr.produced-tr.exported at hh
  rw [tr.start,tr.finish] at hh
  linarith

theorem SegmentTrace.exported_nonneg {collect X Y} (tr : SegmentTrace collect X Y) : 0 ≤ tr.exported :=
  Finset.sum_nonneg (fun k _ => (template_mark_bounds (tr.label k)).1)

theorem segment_counter_inventory (collect : Bool) (n : ℕ) (Z : ℕ → JointCounts)
    (j : ℕ → CompetitionChannel)
    (hc : ∀ k < n,∀ i,(Z (k+1)).2 i=(Z k).2 i+integerCycleMarks collect (j k) i) :
    ((Z n).2 1:ℝ)-((Z 0).2 1:ℝ)=
      ∑ k ∈ Finset.range n,if collect then templateMark (j k) else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hh := ih (fun k hk => hc k (by omega))
    have hs := hc n (by omega) 1
    have hs' : ((Z (n+1)).2 1:ℝ)=((Z n).2 1:ℝ)+(integerCycleMarks collect (j n) 1:ℝ) := by
      exact_mod_cast hs
    rw [integer_cycle_marks_exact] at hs'
    have he : cycleMarks collect (j n) 1=if collect then templateMark (j n) else 0 := by rfl
    rw [he] at hs'
    rw [Finset.sum_range_succ]
    linarith

theorem SegmentTrace.collection_le {collect X Y} (tr : SegmentTrace collect X Y) :
    (Y.2 1:ℝ)-(X.2 1:ℝ) ≤ tr.exported := by
  have hh := segment_counter_inventory collect tr.length tr.state tr.label tr.counters
  rw [tr.start,tr.finish] at hh
  cases collect
  · simp only [Bool.false_eq_true,if_false,Finset.sum_const_zero] at hh
    rw [hh]
    exact tr.exported_nonneg
  · simp only [if_true] at hh
    exact hh.le

/-- Almost every actual chronological endpoint has a finite supported trace from its actual start. -/
theorem joint_endpoint_has_trace (collect : Bool) (V r d : ℝ)
    (hV : 0 < V) (hr : 0 ≤ r) (hd : 0 ≤ d) (X : JointCounts) (T : ℝ) :
    ∀ᵐ Y ∂jointEndpointKernel collect V r d hV hr hd T X,Nonempty (SegmentTrace collect X Y) := by
  change ∀ᵐ Y ∂(jointSourceTrajectory collect V r d hV hr hd X).map (selectedEndpoint T),_
  apply (ae_map_iff (selected_endpoint_measurable T).aemeasurable (Set.to_countable _).measurableSet).mpr
  have hi := jumpTrajectory_initial_population X (jointReactorNext collect) (jointReactorRate V r d)
    (joint_reactor_nonneg V r d hV hr hd) (joint_reactor_total_pos V r d hV hr hd)
  filter_upwards [joint_actual_events collect V r d hV hr hd X,hi] with z hz hstart
  choose j _hlabel _hrate hs hn hc using hz
  refine ⟨⟨Nat.find (endpoint_choice_exists T z),fun k => (z k).1,j,hstart,rfl,
    fun k _ => hs k,fun k _ => hn k,fun k _ => hc k⟩⟩

end
end FiniteCopyReactor
