import proofs.RandomViability.SignedNonfoodMaximal
import proofs.RandomViability.CoordinateIntervalControl

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 100000

theorem nonfood_interval_abs_envelope {n : ℕ} (hn : 4 ≤ n)
    (c : SourceMoleculeFibreConfig n) (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (T : ℝ)
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) (k : ℕ) (s : ℝ)
    (hs : 0 ≤ s) (hsh : s ≤ min (z (k+1)).2.2 (T-prefixElapsed k (Preorder.frestrictLe k z))) :
    |nonfoodCompensationWithinInterval c V basal cat T (massExitStop V) z k s| ≤
      max |censoredNonfoodPrefix c V basal cat T (massExitStop V) z k|
        |censoredNonfoodPrefix c V basal cat T (massExitStop V) z (k+1)|+(n : ℝ)/V := by
  have hB : (0 : ℝ) ≤ (n : ℝ)/V := by positivity
  by_cases hp : censoredNonfoodStop V T (massExitStop V) k (Preorder.frestrictLe k z)
  · rw [nonfoodCompensationWithinInterval,if_pos hp]
    exact (le_max_left _ _).trans (le_add_of_nonneg_right hB)
  · let d : ℝ := if (z (k+1)).2.2 ≤ T-prefixElapsed k (Preorder.frestrictLe k z) then
      (z (k+1)).2.1.elim (fun _ => 0) (nonfoodConcentrationJump V (z k).1) else 0
    have hd : |d| ≤ (n : ℝ)/V := by
      dsimp [d]
      split_ifs
      · cases hl : (z (k+1)).2.1 with
        | inl u => simpa only [Sum.elim_inl,abs_zero] using hB
        | inr ch =>
          simp only [Sum.elim_inr]
          exact physical_nonfood_normalized_jump hn V hV (z k).1 ch
      · simpa only [abs_zero] using hB
    have hstep : censoredNonfoodPrefix c V basal cat T (massExitStop V) z (k+1) =
        censoredNonfoodPrefix c V basal cat T (massExitStop V) z k+d-
        physicalNonfoodDrift c V basal cat (z k).1*
          min (z (k+1)).2.2 (T-prefixElapsed k (Preorder.frestrictLe k z)) := by
      have hsucc : censoredNonfoodPrefix c V basal cat T (massExitStop V) z (k+1) =
          censoredNonfoodPrefix c V basal cat T (massExitStop V) z k+
            censoredNonfoodCompensation c V basal cat T (massExitStop V) k (Preorder.frestrictLe k z) (z (k+1)) := by
        unfold censoredNonfoodPrefix
        rw [Fin.sum_univ_castSucc]
        rfl
      rw [hsucc]
      unfold censoredNonfoodCompensation
      dsimp only
      rw [if_neg hp]
      dsimp [d,physicalNonfoodDrift]
      ring
    have hh := affine_jump_interval_abs_envelope
      (censoredNonfoodPrefix c V basal cat T (massExitStop V) z k)
      (physicalNonfoodDrift c V basal cat (z k).1) d
      (min (z (k+1)).2.2 (T-prefixElapsed k (Preorder.frestrictLe k z))) s ((n : ℝ)/V) hs hsh hB hd
    rw [← hstep] at hh
    simpa only [nonfoodCompensationWithinInterval,if_neg hp] using hh

variable {n : ℕ} [MeasurableSpace (PhysicalCountChannel n)]
  [MeasurableSingletonClass (PhysicalCountChannel n)]

/-- Upper-measure bound for both signs throughout every censored holding interval. -/
theorem physical_nonfood_two_sided_interval_tail (hn : 4 ≤ n)
    (c : SourceMoleculeFibreConfig n) (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ)
    (hbasal : ∀ r,(basal r : ℝ) ≤ 1) (hcat : ∀ r z,(cat r z : ℝ) ≤ 16)
    (δ T : ℝ) (hδ : 0 < δ) (hT : 0 ≤ T) :
    physicalTrajectoryLaw (by omega : 2 ≤ n) c V 1 hV (by norm_num) basal cat N
      {z | ∃ k s,0 ≤ s ∧ s ≤ min (z (k+1)).2.2 (T-prefixElapsed k (Preorder.frestrictLe k z)) ∧
        δ+(n : ℝ)/V ≤ |nonfoodCompensationWithinInterval c V basal cat T (massExitStop V) z k s|} ≤
      2*ENNReal.ofReal (Real.exp (-(δ^2*(V : ℝ)/(4*(n : ℝ)*(96011*T+δ))))) := by
  apply le_trans (measure_mono ?_)
    (physical_nonfood_two_sided_tail hn c V hV basal cat N hbasal hcat δ T hδ hT (massExitStop V) (massExitStop_measurable V))
  intro z hz
  obtain ⟨k,s,hs,hsh,hcross⟩ := hz
  have hb := nonfood_interval_abs_envelope hn c V hV basal cat T z k s hs hsh
  have hm : δ ≤ max |censoredNonfoodPrefix c V basal cat T (massExitStop V) z k|
      |censoredNonfoodPrefix c V basal cat T (massExitStop V) z (k+1)| := by linarith
  rcases le_max_iff.mp hm with hleft|hright
  · exact ⟨k,hleft⟩
  · exact ⟨k+1,hright⟩

end
end RandomViability
