import proofs.RandomViability.PhysicalMassExit
import proofs.RandomViability.PhysicalNonexplosion

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy Filter
open scoped Topology
noncomputable section
set_option maxHeartbeats 100000

theorem prefix_elapsed_eq_waiting_sum {α β : Type*}
    (z : ℕ → JumpState α β) (K : ℕ) :
    prefixElapsed K (Preorder.frestrictLe K z) = waitingSum (fun i => (z (i+1)).2.2) K := by
  unfold prefixElapsed waitingSum
  change (∑ i : Fin K,(z ((i : ℕ)+1)).2.2) = _
  exact Fin.sum_univ_eq_sum_range (fun i => (z (i+1)).2.2) K

/-- A finite holding interval exists at every nonnegative time; zero waits
are allowed and ties select the state after all jumps at that time. -/
theorem unbounded_elapsed_covers_time {α β : Type*}
    (z : ℕ → JumpState α β)
    (hd : Tendsto (fun K => prefixElapsed K (Preorder.frestrictLe K z)) atTop atTop)
    (t : ℝ) (ht : 0 ≤ t) :
    ∃ K,(∀ i ≤ K,prefixElapsed i (Preorder.frestrictLe i z) ≤ t) ∧
      t < prefixElapsed (K+1) (Preorder.frestrictLe (K+1) z) := by
  have he : ∃ K,t < prefixElapsed K (Preorder.frestrictLe K z) :=
    (hd.eventually (eventually_gt_atTop t)).exists
  have hj := Nat.find_spec he
  have hj0 : Nat.find he ≠ 0 := by
    intro hJ
    rw [hJ] at hj
    simp only [prefixElapsed,Fin.sum_univ_zero] at hj
    linarith only [ht,hj]
  refine ⟨Nat.find he-1,?_,?_⟩
  · intro i hi
    exact le_of_not_gt (Nat.find_min he (by omega : i < Nat.find he))
  · have heq : Nat.find he-1+1 = Nat.find he := by omega
    rw [heq]
    exact hj

theorem unbounded_elapsed_partial_interval {α β : Type*}
    (z : ℕ → JumpState α β)
    (hd : Tendsto (fun K => prefixElapsed K (Preorder.frestrictLe K z)) atTop atTop)
    (t T : ℝ) (ht : 0 ≤ t) (hT : t ≤ T) :
    ∃ K s,(∀ i ≤ K,prefixElapsed i (Preorder.frestrictLe i z) ≤ t) ∧
      0 ≤ s ∧ s ≤ min (z (K+1)).2.2 (T-prefixElapsed K (Preorder.frestrictLe K z)) ∧
      prefixElapsed K (Preorder.frestrictLe K z)+s = t ∧
      t < prefixElapsed (K+1) (Preorder.frestrictLe (K+1) z) := by
  obtain ⟨K,hbefore,hafter⟩ := unbounded_elapsed_covers_time z hd t ht
  refine ⟨K,t-prefixElapsed K (Preorder.frestrictLe K z),hbefore,
    sub_nonneg.mpr (hbefore K le_rfl),?_,by ring,hafter⟩
  apply le_min
  · rw [prefixElapsed_restrict_succ] at hafter
    linarith only [hafter]
  · exact sub_le_sub_right hT _

variable {n : ℕ} [MeasurableSpace (PhysicalCountChannel n)]
  [MeasurableSingletonClass (PhysicalCountChannel n)]

/-- Reuses the existing full unbounded-law nonexplosion theorem. -/
theorem physical_prefix_times_diverge (hn : 2 ≤ n)
    (c : SourceMoleculeFibreConfig n) (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ) :
    ∀ᵐ z ∂physicalTrajectoryLaw hn c V 1 hV (by norm_num) basal cat N,
      Tendsto (fun K => prefixElapsed K (Preorder.frestrictLe K z)) atTop atTop := by
  simpa only [prefix_elapsed_eq_waiting_sum] using
    physical_jump_times_tendsto_atTop hn c V 1 hV (by norm_num) basal cat N

theorem physical_time_coverage (hn : 2 ≤ n)
    (c : SourceMoleculeFibreConfig n) (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ) :
    ∀ᵐ z ∂physicalTrajectoryLaw hn c V 1 hV (by norm_num) basal cat N,
      ∀ t : ℝ,0 ≤ t → ∃ K,prefixElapsed K (Preorder.frestrictLe K z) ≤ t ∧
        t < prefixElapsed (K+1) (Preorder.frestrictLe (K+1) z) := by
  filter_upwards [physical_prefix_times_diverge hn c V hV basal cat N] with z hz
  intro t ht
  obtain ⟨K,hbefore,hafter⟩ := unbounded_elapsed_covers_time z hz t ht
  exact ⟨K,hbefore K le_rfl,hafter⟩

end
end RandomViability
