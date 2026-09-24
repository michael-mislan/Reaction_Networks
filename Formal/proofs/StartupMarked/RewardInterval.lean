import proofs.StartupMarked.RewardMaximal

namespace StartupMarked
open Classical RandomViability MeasureTheory ProbabilityTheory RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 50000

theorem gamma_reward_interval_abs_envelope {n : ℕ}
    (c : SourceMoleculeFibreConfig n) (V : NNReal)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (reward : (Molecule n → ℕ) → PhysicalCountChannel n → ℝ)
    (hreward : ∀ N ch,|reward N ch| ≤ (1 : ℝ)) (T : ℝ)
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) (k : ℕ) (s : ℝ)
    (hs : 0 ≤ s) (hsh : s ≤ min (z (k+1)).2.2 (T-prefixElapsed k (Preorder.frestrictLe k z))) :
    |markedRewardWithinInterval c V basal cat reward T (massExitStop V) z k s| ≤
      max |censoredMarkedRewardPrefix c V basal cat reward T (massExitStop V) z k|
        |censoredMarkedRewardPrefix c V basal cat reward T (massExitStop V) z (k+1)|+(1 : ℝ) := by
  have hB : (0 : ℝ) ≤ (1 : ℝ) := by positivity
  by_cases hp : censoredNonfoodStop V T (massExitStop V) k (Preorder.frestrictLe k z)
  · rw [markedRewardWithinInterval,if_pos hp]
    exact (le_max_left _ _).trans (le_add_of_nonneg_right hB)
  · let d : ℝ := if (z (k+1)).2.2 ≤ T-prefixElapsed k (Preorder.frestrictLe k z) then
      (z (k+1)).2.1.elim (fun _ => 0) (reward (z k).1) else 0
    have hd : |d| ≤ (1 : ℝ) := by
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
      (min (z (k+1)).2.2 (T-prefixElapsed k (Preorder.frestrictLe k z))) s ((1 : ℝ)) hs hsh hB hd
    rw [← hstep] at hh
    simpa only [markedRewardWithinInterval,if_neg hp] using hh

variable {n : ℕ} [MeasurableSpace (PhysicalCountChannel n)] [MeasurableSingletonClass (PhysicalCountChannel n)]

theorem gamma_reward_interval_tail (hn : 2 ≤ n)
    (c : SourceMoleculeFibreConfig n) (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal) (N : Molecule n → ℕ)
    (reward : (Molecule n → ℕ) → PhysicalCountChannel n → ℝ)
    (hreward : ∀ N ch,|reward N ch| ≤ 1)
    (Γ T δ : ℝ) (hΓ : 0 ≤ Γ) (hT : 0 ≤ T)
    (hgen : ∀ θ : ℝ,|θ| ≤ 1 → ∀ X,(countMass X : ℝ) ≤ 11*V →
      (∑ ch,unboundedPhysicalRate c V 1 basal cat X ch*(Real.exp (θ*reward X ch)-1)) ≤
        gammaRewardTilt c V basal cat reward θ Γ X) :
    physicalTrajectoryLaw hn c V 1 hV (by norm_num) basal cat N
      {z | ∃ k s,0 ≤ s ∧ s ≤ min (z (k+1)).2.2 (T-prefixElapsed k (Preorder.frestrictLe k z)) ∧
        δ+1 ≤ |markedRewardWithinInterval c V basal cat reward T (massExitStop V) z k s|} ≤
      2*ENNReal.ofReal (Real.exp (-δ+Γ*T)) := by
  apply le_trans (measure_mono ?_)
    (gamma_reward_two_sided_tail hn c V hV basal cat N reward Γ T δ hΓ hT hgen
      (massExitStop V) (massExitStop_measurable V))
  intro z hz
  obtain ⟨k,s,hs,hsh,hcross⟩ := hz
  have hb := gamma_reward_interval_abs_envelope c V basal cat reward hreward T z k s hs hsh
  have hm : δ ≤ max |censoredMarkedRewardPrefix c V basal cat reward T (massExitStop V) z k|
      |censoredMarkedRewardPrefix c V basal cat reward T (massExitStop V) z (k+1)| := by linarith
  rcases le_max_iff.mp hm with hleft|hright
  · exact ⟨k,hleft⟩
  · exact ⟨k+1,hright⟩

end
end StartupMarked
