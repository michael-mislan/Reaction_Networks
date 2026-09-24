import proofs.RandomViability.MassNoiseAssembly

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory Set RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 100000

theorem mass_corrected_jump {n : ℕ} (c : SourceMoleculeFibreConfig n) (V : NNReal)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal) (T : ℝ)
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) (k : ℕ)
    (hc : jumpConsistent unboundedPhysicalNext (z k).1 (z (k+1)))
    (hs : ¬censoredNonfoodStop V T (massExitStop V) k (Preorder.frestrictLe k z))
    (ht : (z (k+1)).2.2 ≤ T-prefixElapsed k (Preorder.frestrictLe k z)) :
    (countMass (z (k+1)).1 : ℝ)/V-censoredMassPrefix c V basal cat T z (k+1) =
      (countMass (z k).1 : ℝ)/V-censoredMassPrefix c V basal cat T z k+
      physicalMassDrift c V basal cat (z k).1*(z (k+1)).2.2 := by
  have hsucc : censoredMassPrefix c V basal cat T z (k+1) =
      censoredMassPrefix c V basal cat T z k+
        censoredMassCompensation c V basal cat T k (Preorder.frestrictLe k z) (z (k+1)) := by
    unfold censoredMassPrefix
    rw [Fin.sum_univ_castSucc]
    rfl
  have hi : (z (k+1)).2.1.elim (fun _ => (0 : ℝ)) (massConcentrationJump V (z k).1) =
      ((countMass (z (k+1)).1 : ℝ)-(countMass (z k).1 : ℝ))/V := by
    obtain ⟨ch,hl,hn⟩ := hc
    rw [hl]
    change massConcentrationJump V (z k).1 ch = _
    rw [hn]
    rfl
  rw [hsucc]
  simp only [censoredMassCompensation,if_neg hs,if_pos ht,min_eq_left ht]
  change (countMass (z (k+1)).1 : ℝ)/V-(censoredMassPrefix c V basal cat T z k+
    ((z (k+1)).2.1.elim (fun _ => 0) (massConcentrationJump V (z k).1)-
      physicalMassDrift c V basal cat (z k).1*(z (k+1)).2.2)) = _
  rw [hi]
  ring

/-- Includes the terminal count jump, even when that jump exits the corridor. -/
theorem physical_mass_prefix_ceiling {n : ℕ} (hn : 2 ≤ n)
    (c : SourceMoleculeFibreConfig n) (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (T η : ℝ) (hη : 0 ≤ η)
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) (K : ℕ)
    (hinit : (countMass (z 0).1 : ℝ)/V ≤ 10)
    (hc : ∀ i < K,jumpConsistent unboundedPhysicalNext (z i).1 (z (i+1)))
    (hs : ∀ i < K,¬censoredNonfoodStop V T (massExitStop V) i (Preorder.frestrictLe i z))
    (ht : ∀ i < K,(z (i+1)).2.2 ≤ T-prefixElapsed i (Preorder.frestrictLe i z))
    (hh : ∀ i < K,0 ≤ (z (i+1)).2.2)
    (hnoise : ∀ i < K,∀ s ∈ Icc 0 (z (i+1)).2.2,
      -η ≤ massCompensationWithinInterval c V basal cat T z i s)
    (hend : censoredMassPrefix c V basal cat T z K ≤ η) :
    (countMass (z K).1 : ℝ)/V ≤ 10+2*η := by
  have hb := compensated_scalar_prefix_floor
    (fun i => -((countMass (z i).1 : ℝ)/V))
    (fun i => -censoredMassPrefix c V basal cat T z i)
    (fun i => -physicalMassDrift c V basal cat (z i).1)
    (fun i => (z (i+1)).2.2) 1 (-10) η K (by norm_num)
    (by simp [censoredMassPrefix])
    (by norm_num; linarith only [hinit,hη]) hh
    (by
      intro i hi
      dsimp only
      rw [physical_mass_drift_identity hn c V hV basal cat]
      linarith)
    (by
      intro i hi s hsi
      have hh := hnoise i hi s hsi
      rw [massCompensationWithinInterval,if_neg (hs i hi)] at hh
      linarith only [hh])
    (by
      intro i hi
      have hj := mass_corrected_jump c V basal cat T z i (hc i hi) (hs i hi) (ht i hi)
      linarith only [hj])
    (by linarith only [hend])
  norm_num at hb
  linarith only [hb]

end
end RandomViability
