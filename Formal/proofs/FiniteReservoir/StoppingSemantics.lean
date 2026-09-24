import proofs.FiniteReservoir.JointCycle
import proofs.FiniteReservoir.SourceCorrespondence
import proofs.FiniteCopyReactor.StoppingSemantics

namespace FiniteReservoir
noncomputable section
open ProductiveRecovery RandomViability.Binding FiniteCopy FiniteCopyReactor Classical

def segmentActive (b : Bool) (V M : ℕ) (N : BoxState V M) : Prop :=
  if b then residenceActive V N.1 else resourceGood (boxCounts N.1) V

theorem segment_active_material (b : Bool) (V M : ℕ) (N : BoxState V M)
    (h : segmentActive b V M N) : resourceGood (boxCounts N.1) V := by
  cases b
  · exact h
  · exact h.1

theorem segment_rate (b : Bool) (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ)) 
    (N : BoxState V M) (j : CompetitionChannel) :
    (supplyModel b V M p hV).rate N j=
      if segmentActive b V M N then rate (boxState N) V p.release p.cleavage p.capacity j else 0 := by
  cases b <;> rfl

theorem supported_segment_next (b : Bool) (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ))
    
    (N : BoxState V M) (j : CompetitionChannel)
    (hp : 0 < (supplyKernel b .foodU V M p hV).prob N (some j)) :
    segmentActive b V M N ∧
    boxState ((supplyKernel b .foodU V M p hV).next N (some j))=
      next (boxState N) j := by
  change 0 < (supplyModel b V M p hV).rate N j/(3000*(V:ℝ)) at hp
  rw [segment_rate] at hp
  have ha : segmentActive b V M N := by
    by_contra h
    rw [if_neg h,zero_div] at hp
    exact (lt_irrefl 0) hp
  refine ⟨ha,?_⟩
  have hmat := segment_active_material b V M N ha
  have hj : rate (boxState N) V p.release p.cleavage p.capacity j ≠ 0 := by
    intro hz
    rw [if_pos ha,hz,zero_div] at hp
    exact (lt_irrefl 0) hp
  change boxState ((supplyModel b V M p hV).next N j)=_
  cases b <;> exact box_next_supported V M p N hmat j hj


/-- Once the stop occurs, the only positive-probability label is the dummy.
Thus both the exact exiting state and all five counters remain unchanged. -/
theorem inactive_joint_freeze (b collect : Bool) (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ))
    
    (X : BoxState V M × ReactorCounters) (j : Option CompetitionChannel)
    (ha : ¬segmentActive b V M X.1)
    (hp : 0 < (jointCycleKernel b collect V M p hV).prob X j) :
    (jointCycleKernel b collect V M p hV).next X j=X := by
  cases j with
  | none =>
    change (X.1,fun i => X.2 i+0)=X
    simp
  | some j =>
    change 0 < (supplyModel b V M p hV).rate X.1 j/(3000*(V:ℝ)) at hp
    rw [segment_rate,if_neg ha,zero_div] at hp
    exact False.elim ((lt_irrefl 0) hp)

theorem successful_segment_no_prior_exit (b collect : Bool) (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ))
    
    (n : ℕ) (X : ℕ → BoxState V M × ReactorCounters) (j : ℕ → Option CompetitionChannel)
    (hp : ∀ k < n,0 < (jointCycleKernel b collect V M p hV).prob (X k) (j k))
    (hn : ∀ k < n,X (k+1)=(jointCycleKernel b collect V M p hV).next (X k) (j k))
    (ha : segmentActive b V M (X n).1) : ∀ k ≤ n,segmentActive b V M (X k).1 :=
  supported_path_stays_active (jointCycleKernel b collect V M p hV) (fun X => segmentActive b V M X.1)
    (inactive_joint_freeze b collect V M p hV) n X j hp hn ha

end
end FiniteReservoir
