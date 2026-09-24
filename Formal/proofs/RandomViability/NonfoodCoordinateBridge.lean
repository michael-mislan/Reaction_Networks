import proofs.RandomViability.CollectiveConcentrationScale
import proofs.RandomViability.JumpSupport

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 100000

def physicalNonfoodDrift {n : ℕ} (c : SourceMoleculeFibreConfig n) (V : NNReal)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ) : ℝ :=
  ∑ ch,unboundedPhysicalRate c V 1 basal cat N ch*nonfoodConcentrationJump V N ch

theorem consistent_nonfood_increment {n : ℕ} (V : NNReal) (N : Molecule n → ℕ)
    (y : JumpState (Molecule n → ℕ) (PhysicalCountChannel n))
    (hy : jumpConsistent unboundedPhysicalNext N y) :
    y.2.1.elim (fun _ => 0) (nonfoodConcentrationJump V N) =
      (countNonfoodMass y.1-countNonfoodMass N)/V := by
  obtain ⟨ch,hlabel,hnext⟩ := hy
  rw [hlabel]
  change nonfoodConcentrationJump V N ch = _
  rw [hnext]
  rfl

/-- The censored recorded increment is a literal observed count change, not
an assumed martingale increment. -/
theorem consistent_censored_nonfood_compensation {n : ℕ}
    (c : SourceMoleculeFibreConfig n) (V : NNReal)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal) (T : ℝ)
    (stop : (k : ℕ) → (Finset.Iic k → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) → Prop)
    (k : ℕ) (h : Finset.Iic k → JumpState (Molecule n → ℕ) (PhysicalCountChannel n))
    (y : JumpState (Molecule n → ℕ) (PhysicalCountChannel n))
    (hy : jumpConsistent unboundedPhysicalNext (h ⟨k,Finset.mem_Iic.mpr le_rfl⟩).1 y) :
    censoredNonfoodCompensation c V basal cat T stop k h y =
      if censoredNonfoodStop V T stop k h then 0 else
        (if y.2.2 ≤ T-prefixElapsed k h then
          (countNonfoodMass y.1-countNonfoodMass (h ⟨k,Finset.mem_Iic.mpr le_rfl⟩).1)/V else 0)-
        physicalNonfoodDrift c V basal cat (h ⟨k,Finset.mem_Iic.mpr le_rfl⟩).1*
          min y.2.2 (T-prefixElapsed k h) := by
  unfold censoredNonfoodCompensation physicalNonfoodDrift
  dsimp only
  rw [consistent_nonfood_increment V _ y hy]

theorem nonfood_changes_telescope {n : ℕ} (V : NNReal)
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) (K : ℕ) :
    (∑ i : Fin K,(countNonfoodMass (z ((i : ℕ)+1)).1-countNonfoodMass (z i).1)/(V : ℝ)) =
      (countNonfoodMass (z K).1-countNonfoodMass (z 0).1)/V := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Fin.sum_univ_castSucc]
    change (∑ i : Fin K,(countNonfoodMass (z ((i : ℕ)+1)).1-countNonfoodMass (z i).1)/(V : ℝ))+
      (countNonfoodMass (z (K+1)).1-countNonfoodMass (z K).1)/V = _
    rw [ih]
    ring

theorem censored_nonfood_complete_prefix_identity {n : ℕ}
    (c : SourceMoleculeFibreConfig n) (V : NNReal)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal) (T : ℝ)
    (stop : (k : ℕ) → (Finset.Iic k → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) → Prop)
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) (K : ℕ)
    (hc : ∀ i < K,jumpConsistent unboundedPhysicalNext (z i).1 (z (i+1)))
    (hs : ∀ i < K,¬censoredNonfoodStop V T stop i (Preorder.frestrictLe i z))
    (ht : ∀ i < K,(z (i+1)).2.2 ≤ T-prefixElapsed i (Preorder.frestrictLe i z)) :
    (∑ i : Fin K,censoredNonfoodCompensation c V basal cat T stop
      i (Preorder.frestrictLe (i : ℕ) z) (z ((i : ℕ)+1))) =
      (countNonfoodMass (z K).1-countNonfoodMass (z 0).1)/V-
      ∑ i : Fin K,physicalNonfoodDrift c V basal cat (z i).1*(z ((i : ℕ)+1)).2.2 := by
  calc
    _ = ∑ i : Fin K,((countNonfoodMass (z ((i : ℕ)+1)).1-countNonfoodMass (z i).1)/V-
        physicalNonfoodDrift c V basal cat (z i).1*(z ((i : ℕ)+1)).2.2) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [consistent_censored_nonfood_compensation c V basal cat T stop i _ _ (hc i i.isLt),
        if_neg (hs i i.isLt),if_pos (ht i i.isLt),min_eq_left (ht i i.isLt)]
      rfl
    _ = _ := by rw [Finset.sum_sub_distrib,nonfood_changes_telescope]

variable {n : ℕ} [MeasurableSpace (PhysicalCountChannel n)]
  [MeasurableSingletonClass (PhysicalCountChannel n)]

theorem physical_nonfood_increment_binding (hn : 2 ≤ n)
    (c : SourceMoleculeFibreConfig n) (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ) :
    ∀ᵐ z ∂physicalTrajectoryLaw hn c V 1 hV (by norm_num) basal cat N, ∀ k,
      (z (k+1)).2.1.elim (fun _ => 0) (nonfoodConcentrationJump V (z k).1) =
        (countNonfoodMass (z (k+1)).1-countNonfoodMass (z k).1)/V := by
  have hh := jumpTrajectory_consistent N unboundedPhysicalNext
    (unboundedPhysicalRate c V 1 basal cat) (unboundedPhysicalRate_nonneg c V 1 basal cat)
    (unbounded_total_pos hn c V 1 hV (by norm_num) basal cat)
  filter_upwards [hh] with z hz
  exact fun k => consistent_nonfood_increment V _ _ (hz k)

end
end RandomViability
