import proofs.RandomViability.CoordinateNoiseScale

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 100000

theorem affine_jump_interval_abs_envelope (a b d h s B : ℝ)
    (hs : 0 ≤ s) (hsh : s ≤ h) (hB : 0 ≤ B) (hd : |d| ≤ B) :
    |a-b*s| ≤ max |a| |a+d-b*h|+B := by
  by_cases ha : 0 ≤ a-b*s
  · rw [abs_of_nonneg ha]
    exact (affine_jump_interval_envelope a b d h s B hs hsh hB (abs_le.mp hd).1).trans
      (add_le_add (max_le_max (le_abs_self _) (le_abs_self _)) le_rfl)
  · have hn : -B ≤ -d := by linarith [(abs_le.mp hd).2]
    have hh := affine_jump_interval_envelope (-a) (-b) (-d) h s B hs hsh hB hn
    have he : -a+ -d- -b*h = -(a+d-b*h) := by ring
    rw [he] at hh
    calc
      _ = -a- -b*s := by rw [abs_of_neg (lt_of_not_ge ha)]; ring
      _ ≤ max (-a) (-(a+d-b*h))+B := hh
      _ ≤ _ := add_le_add (max_le_max (neg_le_abs _) (neg_le_abs _)) le_rfl

def coordinateCompensationWithinInterval {n : ℕ} (c : SourceMoleculeFibreConfig n) (V : NNReal)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (q : Molecule n) (T : ℝ)
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) (k : ℕ) (s : ℝ) : ℝ :=
  if censoredNonfoodStop V T (massExitStop V) k (Preorder.frestrictLe k z) then
    censoredCoordinatePrefix c V basal cat q T z k else
    censoredCoordinatePrefix c V basal cat q T z k-physicalCoordinateDrift c V basal cat (z k).1 q*s

theorem coordinate_interval_envelope {n : ℕ}
    (c : SourceMoleculeFibreConfig n) (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (q : Molecule n) (T : ℝ)
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) (k : ℕ) (s : ℝ)
    (hs : 0 ≤ s) (hsh : s ≤ min (z (k+1)).2.2 (T-prefixElapsed k (Preorder.frestrictLe k z))) :
    |coordinateCompensationWithinInterval c V basal cat q T z k s| ≤
      max |censoredCoordinatePrefix c V basal cat q T z k|
        |censoredCoordinatePrefix c V basal cat q T z (k+1)|+2/V := by
  have hB : (0 : ℝ) ≤ 2/V := by positivity
  by_cases hp : censoredNonfoodStop V T (massExitStop V) k (Preorder.frestrictLe k z)
  · rw [coordinateCompensationWithinInterval,if_pos hp]
    exact (le_max_left _ _).trans (le_add_of_nonneg_right hB)
  · let d : ℝ := if (z (k+1)).2.2 ≤ T-prefixElapsed k (Preorder.frestrictLe k z) then
      (z (k+1)).2.1.elim (fun _ => 0) (coordinateConcentrationJump V q (z k).1) else 0
    have hd : |d| ≤ 2/V := by
      dsimp [d]
      split_ifs
      · cases hl : (z (k+1)).2.1 with
        | inl u => simpa only [Sum.elim_inl,abs_zero] using hB
        | inr ch =>
          simp only [Sum.elim_inr]
          exact coordinate_concentration_jump_bound V hV q (z k).1 ch
      · simpa only [abs_zero] using hB
    have hstep : censoredCoordinatePrefix c V basal cat q T z (k+1) =
        censoredCoordinatePrefix c V basal cat q T z k+d-
        physicalCoordinateDrift c V basal cat (z k).1 q*
          min (z (k+1)).2.2 (T-prefixElapsed k (Preorder.frestrictLe k z)) := by
      have hsucc : censoredCoordinatePrefix c V basal cat q T z (k+1) =
          censoredCoordinatePrefix c V basal cat q T z k+
            censoredCoordinateCompensation c V basal cat q T k (Preorder.frestrictLe k z) (z (k+1)) := by
        unfold censoredCoordinatePrefix
        rw [Fin.sum_univ_castSucc]
        rfl
      rw [hsucc]
      unfold censoredCoordinateCompensation
      dsimp only
      rw [if_neg hp]
      dsimp [d]
      ring
    have hh := affine_jump_interval_abs_envelope
      (censoredCoordinatePrefix c V basal cat q T z k)
      (physicalCoordinateDrift c V basal cat (z k).1 q) d
      (min (z (k+1)).2.2 (T-prefixElapsed k (Preorder.frestrictLe k z))) s (2/V) hs hsh hB hd
    rw [← hstep] at hh
    simpa only [coordinateCompensationWithinInterval,if_neg hp] using hh

variable {n : ℕ} [MeasurableSpace (PhysicalCountChannel n)]
  [MeasurableSingletonClass (PhysicalCountChannel n)]

/-- Upper-measure bound for both signs throughout every censored holding interval. -/
theorem physical_coordinate_interval_tail (hn : 2 ≤ n)
    (c : SourceMoleculeFibreConfig n) (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ)
    (hbasal : ∀ r,(basal r : ℝ) ≤ 1) (hcat : ∀ r z,(cat r z : ℝ) ≤ 16)
    (q : Molecule n) (δ T : ℝ) (hδ : 0 < δ) (hT : 0 ≤ T) :
    physicalTrajectoryLaw hn c V 1 hV (by norm_num) basal cat N
      {z | ∃ k s,0 ≤ s ∧ s ≤ min (z (k+1)).2.2 (T-prefixElapsed k (Preorder.frestrictLe k z)) ∧
        δ+2/V ≤ |coordinateCompensationWithinInterval c V basal cat q T z k s|} ≤
      2*ENNReal.ofReal (Real.exp (-(δ^2*(V : ℝ)/(4*(96000*T+2*δ))))) := by
  apply le_trans (measure_mono ?_)
    (physical_coordinate_two_sided_tail hn c V hV basal cat N hbasal hcat q δ T hδ hT)
  intro z hz
  obtain ⟨k,s,hs,hsh,hcross⟩ := hz
  have hb := coordinate_interval_envelope c V hV basal cat q T z k s hs hsh
  have hm : δ ≤ max |censoredCoordinatePrefix c V basal cat q T z k|
      |censoredCoordinatePrefix c V basal cat q T z (k+1)| := by linarith
  rcases le_max_iff.mp hm with hleft|hright
  · exact ⟨k,hleft⟩
  · exact ⟨k+1,hright⟩

end
end RandomViability
