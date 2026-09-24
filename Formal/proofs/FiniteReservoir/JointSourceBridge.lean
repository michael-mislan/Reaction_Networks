import proofs.FiniteReservoir.JointCountSource
import proofs.FiniteCopyReactor.KernelEmbedding

namespace FiniteReservoir
noncomputable section
open Classical ProductiveRecovery RandomViability.Binding RandomViability MeasureTheory ProbabilityTheory FiniteCopy FiniteCopyReactor
open scoped ENNReal BigOperators

theorem integer_cycle_source_prob (b collect : Bool) (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ))
    
    (X : BoxState V M × IntegerCounters) (j : Option CompetitionChannel) :
    (integerCycleKernel b collect V M p hV).prob X j=
      (jointSourceClock b collect V M p hV).prob (integerCountState X) j := by
  have he (k : CompetitionChannel) : (supplyModel b V M p hV).rate X.1 k=
      FiniteCopyReactor.stoppedRate (jointCountActive b V M) (jointReactorRate V M p) (integerCountState X) k := by
    rw [segment_rate]
    simp only [FiniteCopyReactor.stoppedRate,integer_count_active]
    rfl
  cases j with
  | none =>
    change 1-(∑ k,(supplyModel b V M p hV).rate X.1 k)/(3000*(V:ℝ))=
      1-(∑ k,FiniteCopyReactor.stoppedRate (jointCountActive b V M) (jointReactorRate V M p) (integerCountState X) k)/(3000*(V:ℝ))
    exact congrArg (fun t : ℝ => 1-t/(3000*(V:ℝ))) (Finset.sum_congr rfl (fun k _ => he k))
  | some j =>
    change (supplyModel b V M p hV).rate X.1 j/(3000*(V:ℝ))=
      FiniteCopyReactor.stoppedRate (jointCountActive b V M) (jointReactorRate V M p) (integerCountState X) j/(3000*(V:ℝ))
    rw [he]

theorem integer_cycle_source_next (b collect : Bool) (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ))
    
    (X : BoxState V M × IntegerCounters) (j : Option CompetitionChannel)
    (hp : (integerCycleKernel b collect V M p hV).prob X j ≠ 0) :
    integerCountState ((integerCycleKernel b collect V M p hV).next X j)=
      (jointSourceClock b collect V M p hV).next (integerCountState X) j := by
  cases j with
  | none =>
    change ((integerCountState X).1,fun i => X.2 i+0)=integerCountState X
    simp only [add_zero]
    rfl
  | some j =>
    have hpos : 0 < (supplyKernel b .foodU V M p hV).prob X.1 (some j) :=
      lt_of_le_of_ne ((integerCycleKernel b collect V M p hV).nonneg X (some j)) (Ne.symm hp)
    obtain ⟨ha,he⟩ := supported_segment_next b V M p hV X.1 j hpos
    have hp' := hpos
    change 0 < (supplyModel b V M p hV).rate X.1 j/(3000*(V:ℝ)) at hp'
    rw [segment_rate,if_pos ha] at hp'
    have hn : reactorRate M p V (integerCountState X).1 j ≠ 0 := by
      intro hh
      change 0 < reactorRate M p V (integerCountState X).1 j/(3000*(V:ℝ)) at hp'
      rw [hh,zero_div] at hp'
      exact (lt_irrefl 0) hp'
    apply Prod.ext
    · apply countState_injective M
      exact he.trans (reactor_next_source M p V (integerCountState X).1 j hn).symm
    · rfl


theorem integer_cycle_source_clock (b collect : Bool) (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ))
    
    (f : JointCounts M → ℝ≥0∞) (X : BoxState V M × IntegerCounters) (T : ℝ) :
    causalClockEndpoint (integerCycleKernel b collect V M p hV) (3000*(V:ℝ))
      (fun Y => f (integerCountState Y)) X T=
      causalClockEndpoint (jointSourceClock b collect V M p hV) (3000*(V:ℝ)) f (integerCountState X) T :=
  causal_clock_map _ _ integerCountState
    (integer_cycle_source_prob b collect V M p hV)
    (integer_cycle_source_next b collect V M p hV) f _ T X

theorem integer_cycle_real_clock (b collect : Bool) (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ))
    
    (f : BoxState V M × ReactorCounters → ℝ≥0∞) (X : BoxState V M × IntegerCounters) (q T : ℝ) :
    causalClockEndpoint (integerCycleKernel b collect V M p hV) q
      (fun Y => f (realCounterState Y)) X T=
      causalClockEndpoint (jointCycleKernel b collect V M p hV) q f (realCounterState X) T :=
  causal_clock_map _ _ realCounterState (fun _ _ => rfl)
    (fun Y j _ => integer_cycle_embedding b collect V M p hV Y j) f q T X

/-- The existing finite-box counter law is paid for by the literal unrestricted source. -/
theorem integer_cycle_physical_lower (b collect : Bool) (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ))
    
    (f : JointCounts M → ℝ≥0∞) (hf : ∀ X,f X ≤ 1) (X : BoxState V M × IntegerCounters) (T : ℝ) :
    causalClockEndpoint (integerCycleKernel b collect V M p hV) (3000*(V:ℝ))
      (fun Y => if integerCountState Y ∈ jointCountActive b V M then f (integerCountState Y) else 0) X T ≤
      jointSourceEndpoint collect V M p hV f (integerCountState X) T := by
  rw [integer_cycle_source_clock b collect V M p hV
    (fun Y => if Y ∈ jointCountActive b V M then f Y else 0) X T]
  exact joint_source_clock_le b collect V M p hV f hf (integerCountState X) T

end
end FiniteReservoir
