import proofs.RandomViability.MarkedUniformProbability

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 150000

/-- A countable, measurable version of the collective finite-horizon event. -/
def finiteMarkedSuccess {n : ℕ} (V : NNReal) (r : Reaction n)
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) : Prop :=
  (∀ k,prefixElapsed k (Preorder.frestrictLe k z) ≤ 100 → (countMass (z k).1 : ℝ) ≤ 11*V) ∧
  (∀ k,prefixElapsed k (Preorder.frestrictLe k z) ≤ 100 →
    max 1 (prefixElapsed k (Preorder.frestrictLe k z)) < prefixElapsed (k+1) (Preorder.frestrictLe (k+1) z) →
    (1/3000000000000000000 : ℝ) ≤ ((z k).1 (reactionProduct r) : ℝ)/V) ∧
  ∃ J K,prefixElapsed J (Preorder.frestrictLe J z) ≤ 1 ∧
    1 < prefixElapsed (J+1) (Preorder.frestrictLe (J+1) z) ∧
    prefixElapsed (J+K) (Preorder.frestrictLe (J+K) z) ≤ 100 ∧
    100 < prefixElapsed (J+K+1) (Preorder.frestrictLe (J+K+1) z) ∧
    (1/10 : ℝ) < markedWindowReward (fun _ => exportReward V) z J K ∧
    markedWindowReward (positiveBasalReward V) z 0 (J+K) <
      markedWindowReward (fun _ => exportReward V) z J K/4

theorem holding_index_unique {α β : Type*} (z : ℕ → JumpState α β)
    (hh : ∀ k,0 ≤ (z (k+1)).2.2) (i j : ℕ) (t : ℝ)
    (hi : prefixElapsed i (Preorder.frestrictLe i z) ≤ t)
    (hi' : t < prefixElapsed (i+1) (Preorder.frestrictLe (i+1) z))
    (hj : prefixElapsed j (Preorder.frestrictLe j z) ≤ t)
    (hj' : t < prefixElapsed (j+1) (Preorder.frestrictLe (j+1) z)) : i = j := by
  have hm := prefix_elapsed_monotone z hh
  rcases lt_trichotomy i j with h|h|h
  · have he := hm (show i+1 ≤ j by omega)
    linarith only [he,hj,hi']
  · exact h
  · have he := hm (show j+1 ≤ i by omega)
    linarith only [he,hi,hj']

theorem marked_coverage_implies_finite {n : ℕ} (V : NNReal) (r : Reaction n)
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n))
    (hh : ∀ k,0 ≤ (z (k+1)).2.2) (hz : markedProductiveCoverage V r 101 z) :
    finiteMarkedSuccess V r z := by
  refine ⟨hz.2.1,?_,hz.2.2⟩
  intro k hk hk'
  let t := max 1 (prefixElapsed k (Preorder.frestrictLe k z))
  have ht : t ≤ 100 := max_le (by norm_num) hk
  obtain ⟨j,hj,hj',_,hp⟩ := hz.1 t (le_max_left _ _) (by linarith only [ht])
  have he := holding_index_unique z hh j k t hj hj' (le_max_right _ _) hk'
  simpa only [he] using hp

variable {n : ℕ} [MeasurableSpace (PhysicalCountChannel n)]
  [MeasurableSingletonClass (PhysicalCountChannel n)]

theorem marked_window_reward_measurable
    (reward : (Molecule n → ℕ) → PhysicalCountChannel n → ℝ) (J K : ℕ) :
    Measurable (fun z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n) => markedWindowReward reward z J K) := by
  letI := markSingletonClass (β := PhysicalCountChannel n)
  have hm : Measurable (fun p : (Molecule n → ℕ) × (Unit ⊕ PhysicalCountChannel n) =>
      p.2.elim (fun _ => (0 : ℝ)) (reward p.1)) := measurable_of_countable _
  unfold markedWindowReward
  apply Finset.measurable_sum
  intro i _
  exact hm.comp (((measurable_pi_apply (J+i)).fst).prodMk ((measurable_pi_apply (J+i+1)).snd.fst))

theorem finite_marked_success_measurable (V : NNReal) (r : Reaction n) :
    MeasurableSet {z | finiteMarkedSuccess V r z} := by
  have hclock (i : ℕ) : Measurable (fun z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n) =>
      prefixElapsed i (Preorder.frestrictLe i z)) :=
    (prefixElapsed_measurable i).comp (Preorder.measurable_frestrictLe i)
  have hmass (i : ℕ) : Measurable (fun z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n) =>
      (countMass (z i).1 : ℝ)) := (measurable_of_countable (fun N : Molecule n → ℕ => (countMass N : ℝ))).comp
        (measurable_pi_apply i).fst
  have hcount (i : ℕ) : Measurable (fun z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n) =>
      ((z i).1 (reactionProduct r) : ℝ)/V) :=
    (measurable_of_countable (fun N : Molecule n → ℕ => (N (reactionProduct r) : ℝ)/V)).comp (measurable_pi_apply i).fst
  have hexport := marked_window_reward_measurable (fun _ => exportReward (n := n) V)
  have hbasal := marked_window_reward_measurable (positiveBasalReward (n := n) V)
  unfold finiteMarkedSuccess
  measurability

end
end RandomViability
