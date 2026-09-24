import proofs.RandomViability.MarkedRewardMaximal
import proofs.RandomViability.CoordinateIntervalControl

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 100000

def markedRewardDrift {n : ℕ} (c : SourceMoleculeFibreConfig n) (V : NNReal)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (reward : (Molecule n → ℕ) → PhysicalCountChannel n → ℝ) (N : Molecule n → ℕ) : ℝ :=
  ∑ ch,unboundedPhysicalRate c V 1 basal cat N ch*reward N ch

def markedRewardWithinInterval {n : ℕ} (c : SourceMoleculeFibreConfig n) (V : NNReal)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (reward : (Molecule n → ℕ) → PhysicalCountChannel n → ℝ) (T : ℝ)
    (stop : (k : ℕ) → (Finset.Iic k → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) → Prop)
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) (k : ℕ) (s : ℝ) : ℝ :=
  if censoredNonfoodStop V T stop k (Preorder.frestrictLe k z) then
    censoredMarkedRewardPrefix c V basal cat reward T stop z k else
    censoredMarkedRewardPrefix c V basal cat reward T stop z k-markedRewardDrift c V basal cat reward (z k).1*s

theorem marked_reward_interval_abs_envelope {n : ℕ}
    (c : SourceMoleculeFibreConfig n) (V : NNReal)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (reward : (Molecule n → ℕ) → PhysicalCountChannel n → ℝ)
    (hreward : ∀ N ch,|reward N ch| ≤ (n : ℝ)/V) (T : ℝ)
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) (k : ℕ) (s : ℝ)
    (hs : 0 ≤ s) (hsh : s ≤ min (z (k+1)).2.2 (T-prefixElapsed k (Preorder.frestrictLe k z))) :
    |markedRewardWithinInterval c V basal cat reward T (massExitStop V) z k s| ≤
      max |censoredMarkedRewardPrefix c V basal cat reward T (massExitStop V) z k|
        |censoredMarkedRewardPrefix c V basal cat reward T (massExitStop V) z (k+1)|+(n : ℝ)/V := by
  have hB : (0 : ℝ) ≤ (n : ℝ)/V := by positivity
  by_cases hp : censoredNonfoodStop V T (massExitStop V) k (Preorder.frestrictLe k z)
  · rw [markedRewardWithinInterval,if_pos hp]
    exact (le_max_left _ _).trans (le_add_of_nonneg_right hB)
  · let d : ℝ := if (z (k+1)).2.2 ≤ T-prefixElapsed k (Preorder.frestrictLe k z) then
      (z (k+1)).2.1.elim (fun _ => 0) (reward (z k).1) else 0
    have hd : |d| ≤ (n : ℝ)/V := by
      dsimp [d]
      split_ifs
      · cases hl : (z (k+1)).2.1 with
        | inl u => simpa only [Sum.elim_inl,abs_zero] using hB
        | inr ch =>
          simp only [Sum.elim_inr]
          exact hreward (z k).1 ch
      · simpa only [abs_zero] using hB
    have hstep : censoredMarkedRewardPrefix c V basal cat reward T (massExitStop V) z (k+1) =
        censoredMarkedRewardPrefix c V basal cat reward T (massExitStop V) z k+d-
        markedRewardDrift c V basal cat reward (z k).1*
          min (z (k+1)).2.2 (T-prefixElapsed k (Preorder.frestrictLe k z)) := by
      have hsucc : censoredMarkedRewardPrefix c V basal cat reward T (massExitStop V) z (k+1) =
          censoredMarkedRewardPrefix c V basal cat reward T (massExitStop V) z k+
            censoredMarkedRewardCompensation c V basal cat reward T (massExitStop V) k (Preorder.frestrictLe k z) (z (k+1)) := by
        unfold censoredMarkedRewardPrefix
        rw [Fin.sum_univ_castSucc]
        rfl
      rw [hsucc]
      unfold censoredMarkedRewardCompensation
      dsimp only
      rw [if_neg hp]
      dsimp [d,markedRewardDrift]
      ring
    have hh := affine_jump_interval_abs_envelope
      (censoredMarkedRewardPrefix c V basal cat reward T (massExitStop V) z k)
      (markedRewardDrift c V basal cat reward (z k).1) d
      (min (z (k+1)).2.2 (T-prefixElapsed k (Preorder.frestrictLe k z))) s ((n : ℝ)/V) hs hsh hB hd
    rw [← hstep] at hh
    simpa only [markedRewardWithinInterval,if_neg hp] using hh

variable {n : ℕ} [MeasurableSpace (PhysicalCountChannel n)]
  [MeasurableSingletonClass (PhysicalCountChannel n)]

/-- Upper-measure bound for both signs throughout every censored holding interval. -/
theorem physical_marked_reward_two_sided_interval_tail (hn : 4 ≤ n)
    (c : SourceMoleculeFibreConfig n) (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ)
    (reward : (Molecule n → ℕ) → PhysicalCountChannel n → ℝ)
    (hreward : ∀ N ch,|reward N ch| ≤ (n : ℝ)/V)
    (hvariance : ∀ N,(countMass N : ℝ) ≤ 11*V →
      (∑ ch,unboundedPhysicalRate c V 1 basal cat N ch*(reward N ch)^2) ≤ (384000+11*(n : ℝ))/V)
    (δ T : ℝ) (hδ : 0 < δ) (hT : 0 ≤ T) :
    physicalTrajectoryLaw (by omega : 2 ≤ n) c V 1 hV (by norm_num) basal cat N
      {z | ∃ k s,0 ≤ s ∧ s ≤ min (z (k+1)).2.2 (T-prefixElapsed k (Preorder.frestrictLe k z)) ∧
        δ+(n : ℝ)/V ≤ |markedRewardWithinInterval c V basal cat reward T (massExitStop V) z k s|} ≤
      2*ENNReal.ofReal (Real.exp (-(δ^2*(V : ℝ)/(4*(n : ℝ)*(96011*T+δ))))) := by
  apply le_trans (measure_mono ?_)
    (physical_marked_reward_two_sided_tail hn c V hV basal cat N reward hreward hvariance δ T hδ hT (massExitStop V) (massExitStop_measurable V))
  intro z hz
  obtain ⟨k,s,hs,hsh,hcross⟩ := hz
  have hb := marked_reward_interval_abs_envelope c V basal cat reward hreward T z k s hs hsh
  have hm : δ ≤ max |censoredMarkedRewardPrefix c V basal cat reward T (massExitStop V) z k|
      |censoredMarkedRewardPrefix c V basal cat reward T (massExitStop V) z (k+1)| := by linarith
  rcases le_max_iff.mp hm with hleft|hright
  · exact ⟨k,hleft⟩
  · exact ⟨k+1,hright⟩

end
end RandomViability
