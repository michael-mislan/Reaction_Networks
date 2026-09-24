import proofs.FiniteCopyReactor.JointCountSource
import proofs.FiniteCopyReactor.KernelEmbedding

namespace FiniteCopyReactor
noncomputable section
open Classical ProductiveRecovery RandomViability.Binding RandomViability MeasureTheory ProbabilityTheory FiniteCopy
open scoped ENNReal BigOperators

theorem integer_cycle_source_prob (b collect : Bool) (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ))
    (hr : 0 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25)
    (X : BoxCounts V × IntegerCounters) (j : Option CompetitionChannel) :
    (integerCycleKernel b collect V r d hV hr hr' hd hd').prob X j=
      (jointSourceClock b collect V r d hV hr hr' hd hd').prob (integerCountState X) j := by
  have he (k : CompetitionChannel) : (supplyModel b V r d hV hr hd).rate X.1 k=
      stoppedRate (jointCountActive b V) (jointReactorRate V r d) (integerCountState X) k := by
    rw [segment_rate]
    simp only [stoppedRate,integer_count_active]
    rfl
  cases j with
  | none =>
    change 1-(∑ k,(supplyModel b V r d hV hr hd).rate X.1 k)/(3000*(V:ℝ))=
      1-(∑ k,stoppedRate (jointCountActive b V) (jointReactorRate V r d) (integerCountState X) k)/(3000*(V:ℝ))
    exact congrArg (fun t : ℝ => 1-t/(3000*(V:ℝ))) (Finset.sum_congr rfl (fun k _ => he k))
  | some j =>
    change (supplyModel b V r d hV hr hd).rate X.1 j/(3000*(V:ℝ))=
      stoppedRate (jointCountActive b V) (jointReactorRate V r d) (integerCountState X) j/(3000*(V:ℝ))
    rw [he]

theorem integer_cycle_source_next (b collect : Bool) (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ))
    (hr : 0 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25)
    (X : BoxCounts V × IntegerCounters) (j : Option CompetitionChannel)
    (hp : (integerCycleKernel b collect V r d hV hr hr' hd hd').prob X j ≠ 0) :
    integerCountState ((integerCycleKernel b collect V r d hV hr hr' hd hd').next X j)=
      (jointSourceClock b collect V r d hV hr hr' hd hd').next (integerCountState X) j := by
  cases j with
  | none =>
    change (boxCounts X.1,fun i => X.2 i+0)=(boxCounts X.1,X.2)
    simp
  | some j =>
    have hpos : 0 < (supplyKernel b .foodU V r d hV hr hr' hd hd').prob X.1 (some j) :=
      lt_of_le_of_ne ((integerCycleKernel b collect V r d hV hr hr' hd hd').nonneg X (some j)) (Ne.symm hp)
    obtain ⟨ha,he⟩ := supported_segment_next b V r d hV hr hr' hd hd' X.1 j hpos
    have hp' := hpos
    change 0 < (supplyModel b V r d hV hr hd).rate X.1 j/(3000*(V:ℝ)) at hp'
    rw [segment_rate,if_pos ha] at hp'
    have hn : reactorRate V r d (boxCounts X.1) j ≠ 0 := by
      intro hh
      rw [hh,zero_div] at hp'
      exact (lt_irrefl 0) hp'
    apply Prod.ext
    · exact he.trans (reactor_next_source (boxCounts X.1) V r d j hn).symm
    · rfl

theorem integer_cycle_source_clock (b collect : Bool) (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ))
    (hr : 0 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25)
    (f : JointCounts → ℝ≥0∞) (X : BoxCounts V × IntegerCounters) (T : ℝ) :
    causalClockEndpoint (integerCycleKernel b collect V r d hV hr hr' hd hd') (3000*(V:ℝ))
      (fun Y => f (integerCountState Y)) X T=
      causalClockEndpoint (jointSourceClock b collect V r d hV hr hr' hd hd') (3000*(V:ℝ)) f (integerCountState X) T :=
  causal_clock_map _ _ integerCountState
    (integer_cycle_source_prob b collect V r d hV hr hr' hd hd')
    (integer_cycle_source_next b collect V r d hV hr hr' hd hd') f _ T X

theorem integer_cycle_real_clock (b collect : Bool) (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ))
    (hr : 0 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25)
    (f : BoxCounts V × ReactorCounters → ℝ≥0∞) (X : BoxCounts V × IntegerCounters) (q T : ℝ) :
    causalClockEndpoint (integerCycleKernel b collect V r d hV hr hr' hd hd') q
      (fun Y => f (realCounterState Y)) X T=
      causalClockEndpoint (jointCycleKernel b collect V r d hV hr hr' hd hd') q f (realCounterState X) T :=
  causal_clock_map _ _ realCounterState (fun _ _ => rfl)
    (fun Y j _ => integer_cycle_embedding b collect V r d hV hr hr' hd hd' Y j) f q T X

/-- The existing finite-box counter law is paid for by the literal unrestricted source. -/
theorem integer_cycle_physical_lower (b collect : Bool) (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ))
    (hr : 0 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25)
    (f : JointCounts → ℝ≥0∞) (hf : ∀ X,f X ≤ 1) (X : BoxCounts V × IntegerCounters) (T : ℝ) :
    causalClockEndpoint (integerCycleKernel b collect V r d hV hr hr' hd hd') (3000*(V:ℝ))
      (fun Y => if integerCountState Y ∈ jointCountActive b V then f (integerCountState Y) else 0) X T ≤
      jointSourceEndpoint collect V r d hV hr hd f (integerCountState X) T := by
  rw [integer_cycle_source_clock b collect V r d hV hr hr' hd hd'
    (fun Y => if Y ∈ jointCountActive b V then f Y else 0) X T]
  exact joint_source_clock_le b collect V r d hV hr hr' hd hd' f hf (integerCountState X) T

end
end FiniteCopyReactor
