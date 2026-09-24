import proofs.RandomViability.NonfoodCoordinateBridge

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 100000

theorem affine_jump_interval_envelope (a b d h s B : ℝ) (hs : 0 ≤ s) (hsh : s ≤ h)
    (hB : 0 ≤ B) (hd : -B ≤ d) : a-b*s ≤ max a (a+d-b*h)+B := by
  by_cases hb : 0 ≤ b
  · calc
      _ ≤ a := sub_le_self _ (mul_nonneg hb hs)
      _ ≤ max a (a+d-b*h) := le_max_left _ _
      _ ≤ _ := le_add_of_nonneg_right hB
  · have hm := mul_le_mul_of_nonpos_left hsh (le_of_not_ge hb)
    have hx := le_max_right a (a+d-b*h)
    linarith

def censoredNonfoodPrefix {n : ℕ} (c : SourceMoleculeFibreConfig n) (V : NNReal)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal) (T : ℝ)
    (stop : (k : ℕ) → (Finset.Iic k → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) → Prop)
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) (K : ℕ) : ℝ :=
  ∑ i : Fin K,censoredNonfoodCompensation c V basal cat T stop
    i (Preorder.frestrictLe (i : ℕ) z) (z ((i : ℕ)+1))

theorem censoredNonfoodPrefix_succ {n : ℕ} (c : SourceMoleculeFibreConfig n) (V : NNReal)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal) (T : ℝ)
    (stop : (k : ℕ) → (Finset.Iic k → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) → Prop)
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) (K : ℕ) :
    censoredNonfoodPrefix c V basal cat T stop z (K+1) =
      censoredNonfoodPrefix c V basal cat T stop z K+
      censoredNonfoodCompensation c V basal cat T stop K (Preorder.frestrictLe K z) (z (K+1)) := by
  unfold censoredNonfoodPrefix
  rw [Fin.sum_univ_castSucc]
  rfl

def nonfoodCompensationWithinInterval {n : ℕ} (c : SourceMoleculeFibreConfig n) (V : NNReal)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal) (T : ℝ)
    (stop : (k : ℕ) → (Finset.Iic k → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) → Prop)
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) (k : ℕ) (s : ℝ) : ℝ :=
  if censoredNonfoodStop V T stop k (Preorder.frestrictLe k z) then
    censoredNonfoodPrefix c V basal cat T stop z k else
    censoredNonfoodPrefix c V basal cat T stop z k-physicalNonfoodDrift c V basal cat (z k).1*s

theorem nonfood_interval_envelope {n : ℕ} (hn : 4 ≤ n)
    (c : SourceMoleculeFibreConfig n) (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal) (T : ℝ)
    (stop : (k : ℕ) → (Finset.Iic k → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) → Prop)
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) (k : ℕ) (s : ℝ)
    (hs : 0 ≤ s) (hsh : s ≤ min (z (k+1)).2.2 (T-prefixElapsed k (Preorder.frestrictLe k z))) :
    nonfoodCompensationWithinInterval c V basal cat T stop z k s ≤
      max (censoredNonfoodPrefix c V basal cat T stop z k)
        (censoredNonfoodPrefix c V basal cat T stop z (k+1))+(n : ℝ)/V := by
  have hB : (0 : ℝ) ≤ (n : ℝ)/V := by positivity
  by_cases hp : censoredNonfoodStop V T stop k (Preorder.frestrictLe k z)
  · rw [nonfoodCompensationWithinInterval,if_pos hp]
    exact (le_max_left _ _).trans (le_add_of_nonneg_right hB)
  · let d : ℝ := if (z (k+1)).2.2 ≤ T-prefixElapsed k (Preorder.frestrictLe k z) then
      (z (k+1)).2.1.elim (fun _ => 0) (nonfoodConcentrationJump V (z k).1) else 0
    have hd : -((n : ℝ)/V) ≤ d := by
      dsimp [d]
      split_ifs
      · cases hl : (z (k+1)).2.1 with
        | inl u => simp only [Sum.elim_inl]; linarith
        | inr ch =>
          simp only [Sum.elim_inr]
          exact (abs_le.mp (physical_nonfood_normalized_jump hn V hV (z k).1 ch)).1
      · linarith
    have hstep : censoredNonfoodPrefix c V basal cat T stop z (k+1) =
        censoredNonfoodPrefix c V basal cat T stop z k+d-
        physicalNonfoodDrift c V basal cat (z k).1*
          min (z (k+1)).2.2 (T-prefixElapsed k (Preorder.frestrictLe k z)) := by
      rw [censoredNonfoodPrefix_succ]
      unfold censoredNonfoodCompensation
      dsimp only
      rw [if_neg hp]
      dsimp [d,physicalNonfoodDrift]
      ring
    have hh := affine_jump_interval_envelope
      (censoredNonfoodPrefix c V basal cat T stop z k)
      (physicalNonfoodDrift c V basal cat (z k).1) d
      (min (z (k+1)).2.2 (T-prefixElapsed k (Preorder.frestrictLe k z))) s ((n : ℝ)/V) hs hsh hB hd
    rw [← hstep] at hh
    simpa only [nonfoodCompensationWithinInterval,if_neg hp] using hh

variable {n : ℕ} [MeasurableSpace (PhysicalCountChannel n)]
  [MeasurableSingletonClass (PhysicalCountChannel n)]

/-- Upper-measure bound for interval interpolation of the stopped compensation.
The one-jump allowance accounts for a downward count jump at the right endpoint. -/
theorem physical_nonfood_interval_tail (hn : 4 ≤ n)
    (c : SourceMoleculeFibreConfig n) (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ)
    (hbasal : ∀ r,(basal r : ℝ) ≤ 1) (hcat : ∀ r z,(cat r z : ℝ) ≤ 16)
    (δ T : ℝ) (hδ : 0 < δ) (hT : 0 ≤ T)
    (stop : (k : ℕ) → (Finset.Iic k → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) → Prop)
    (hstop : ∀ k,MeasurableSet {h | stop k h}) :
    physicalTrajectoryLaw (by omega : 2 ≤ n) c V 1 hV (by norm_num) basal cat N
      {z | ∃ k s,0 ≤ s ∧ s ≤ min (z (k+1)).2.2 (T-prefixElapsed k (Preorder.frestrictLe k z)) ∧
        δ+(n : ℝ)/V ≤ nonfoodCompensationWithinInterval c V basal cat T stop z k s} ≤
      ENNReal.ofReal (Real.exp (-(δ^2*(V : ℝ)/(4*(n : ℝ)*(96011*T+δ))))) := by
  apply le_trans (measure_mono ?_)
    (physical_censored_nonfood_volume_rate hn c V hV basal cat N hbasal hcat δ T hδ hT stop hstop)
  intro z hz
  obtain ⟨k,s,hs,hsh,hcross⟩ := hz
  have hb := nonfood_interval_envelope hn c V hV basal cat T stop z k s hs hsh
  have hm : δ ≤ max (censoredNonfoodPrefix c V basal cat T stop z k)
      (censoredNonfoodPrefix c V basal cat T stop z (k+1)) := by linarith
  apply Set.mem_iUnion.mpr
  refine ⟨k+1,?_⟩
  rcases le_max_iff.mp hm with hleft|hright
  · exact ⟨k,by omega,hleft⟩
  · exact ⟨k+1,le_rfl,hright⟩

end
end RandomViability
