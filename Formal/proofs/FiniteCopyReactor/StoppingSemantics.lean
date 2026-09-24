import proofs.FiniteCopyReactor.JointCycle
import proofs.FiniteCopyReactor.CountTrajectory

namespace FiniteCopyReactor
noncomputable section
open ProductiveRecovery RandomViability.Binding FiniteCopy Classical

def segmentActive (b : Bool) (V : ℕ) (N : BoxCounts V) : Prop :=
  if b then residenceActive V N else resourceGood (boxCounts N) V

theorem segment_active_material (b : Bool) (V : ℕ) (N : BoxCounts V)
    (h : segmentActive b V N) : resourceGood (boxCounts N) V := by
  cases b
  · exact h
  · exact h.1

theorem segment_rate (b : Bool) (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ)) (hr : 0 ≤ r) (hd : 0 ≤ d)
    (N : BoxCounts V) (j : CompetitionChannel) :
    (supplyModel b V r d hV hr hd).rate N j=
      if segmentActive b V N then reactorRate V r d (boxCounts N) j else 0 := by
  cases b <;> rfl

theorem supported_segment_next (b : Bool) (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ))
    (hr : 0 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25)
    (N : BoxCounts V) (j : CompetitionChannel)
    (hp : 0 < (supplyKernel b .foodU V r d hV hr hr' hd hd').prob N (some j)) :
    segmentActive b V N ∧
    boxCounts ((supplyKernel b .foodU V r d hV hr hr' hd hd').next N (some j))=
      CommonPhysicalRealization.physicalNext (boxCounts N) j := by
  change 0 < (supplyModel b V r d hV hr hd).rate N j/(3000*(V:ℝ)) at hp
  rw [segment_rate] at hp
  have ha : segmentActive b V N := by
    by_contra h
    rw [if_neg h,zero_div] at hp
    exact (lt_irrefl 0) hp
  refine ⟨ha,?_⟩
  have hmat := segment_active_material b V N ha
  change boxCounts ((supplyModel b V r d hV hr hd).next N j)=_
  cases b <;> exact boxNext_exact V N (competitionBase j) hmat

/-- Once the stop occurs, the only positive-probability label is the dummy.
Thus both the exact exiting state and all five counters remain unchanged. -/
theorem inactive_joint_freeze (b collect : Bool) (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ))
    (hr : 0 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25)
    (X : BoxCounts V × ReactorCounters) (j : Option CompetitionChannel)
    (ha : ¬segmentActive b V X.1)
    (hp : 0 < (jointCycleKernel b collect V r d hV hr hr' hd hd').prob X j) :
    (jointCycleKernel b collect V r d hV hr hr' hd hd').next X j=X := by
  cases j with
  | none =>
    change (X.1,fun i => X.2 i+0)=X
    simp
  | some j =>
    change 0 < (supplyModel b V r d hV hr hd).rate X.1 j/(3000*(V:ℝ)) at hp
    rw [segment_rate,if_neg ha,zero_div] at hp
    exact False.elim ((lt_irrefl 0) hp)

theorem supported_path_stays_active {α β : Type*} [Fintype β]
    (P : MarkedKernel α β) (A : α → Prop)
    (hf : ∀ x j, ¬A x → 0 < P.prob x j → P.next x j=x)
    (n : ℕ) (X : ℕ → α) (j : ℕ → β)
    (hp : ∀ k < n,0 < P.prob (X k) (j k))
    (hn : ∀ k < n,X (k+1)=P.next (X k) (j k))
    (ha : A (X n)) : ∀ k ≤ n,A (X k) := by
  induction n with
  | zero =>
    intro k hk
    have he : k=0 := by omega
    subst k
    exact ha
  | succ n ih =>
    have hprev : A (X n) := by
      by_contra h
      have he := (hn n (by omega)).trans (hf (X n) (j n) h (hp n (by omega)))
      rw [he] at ha
      exact h ha
    intro k hk
    by_cases hkn : k ≤ n
    · exact ih (fun k hk => hp k (by omega)) (fun k hk => hn k (by omega)) hprev k hkn
    · have : k=n+1 := by omega
      subst k
      exact ha

theorem successful_segment_no_prior_exit (b collect : Bool) (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ))
    (hr : 0 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25)
    (n : ℕ) (X : ℕ → BoxCounts V × ReactorCounters) (j : ℕ → Option CompetitionChannel)
    (hp : ∀ k < n,0 < (jointCycleKernel b collect V r d hV hr hr' hd hd').prob (X k) (j k))
    (hn : ∀ k < n,X (k+1)=(jointCycleKernel b collect V r d hV hr hr' hd hd').next (X k) (j k))
    (ha : segmentActive b V (X n).1) : ∀ k ≤ n,segmentActive b V (X k).1 :=
  supported_path_stays_active (jointCycleKernel b collect V r d hV hr hr' hd hd') (fun X => segmentActive b V X.1)
    (inactive_joint_freeze b collect V r d hV hr hr' hd hd') n X j hp hn ha

end
end FiniteCopyReactor
