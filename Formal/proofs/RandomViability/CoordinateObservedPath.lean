import proofs.RandomViability.CoordinateIntervalControl

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 100000

theorem consistent_censored_coordinate_compensation {n : ℕ}
    (c : SourceMoleculeFibreConfig n) (V : NNReal)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (q : Molecule n) (T : ℝ) (k : ℕ)
    (h : Finset.Iic k → JumpState (Molecule n → ℕ) (PhysicalCountChannel n))
    (y : JumpState (Molecule n → ℕ) (PhysicalCountChannel n))
    (hy : jumpConsistent unboundedPhysicalNext (h ⟨k,Finset.mem_Iic.mpr le_rfl⟩).1 y) :
    censoredCoordinateCompensation c V basal cat q T k h y =
      if censoredNonfoodStop V T (massExitStop V) k h then 0 else
        (if y.2.2 ≤ T-prefixElapsed k h then
          ((y.1 q : ℝ)-((h ⟨k,Finset.mem_Iic.mpr le_rfl⟩).1 q : ℝ))/V else 0)-
        physicalCoordinateDrift c V basal cat (h ⟨k,Finset.mem_Iic.mpr le_rfl⟩).1 q*
          min y.2.2 (T-prefixElapsed k h) := by
  unfold censoredCoordinateCompensation
  dsimp only
  rw [consistent_coordinate_increment V q _ y hy]

theorem coordinate_changes_telescope {n : ℕ} (V : NNReal) (q : Molecule n)
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) (K : ℕ) :
    (∑ i : Fin K,(((z ((i : ℕ)+1)).1 q : ℝ)-((z i).1 q : ℝ))/V) =
      (((z K).1 q : ℝ)-((z 0).1 q : ℝ))/V := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Fin.sum_univ_castSucc]
    change (∑ i : Fin K,(((z ((i : ℕ)+1)).1 q : ℝ)-((z i).1 q : ℝ))/V)+
      (((z (K+1)).1 q : ℝ)-((z K).1 q : ℝ))/V = _
    rw [ih]
    ring

theorem coordinate_complete_prefix_identity {n : ℕ}
    (c : SourceMoleculeFibreConfig n) (V : NNReal)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (q : Molecule n) (T : ℝ)
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) (K : ℕ)
    (hc : ∀ i < K,jumpConsistent unboundedPhysicalNext (z i).1 (z (i+1)))
    (hs : ∀ i < K,¬censoredNonfoodStop V T (massExitStop V) i (Preorder.frestrictLe i z))
    (ht : ∀ i < K,(z (i+1)).2.2 ≤ T-prefixElapsed i (Preorder.frestrictLe i z)) :
    censoredCoordinatePrefix c V basal cat q T z K =
      (((z K).1 q : ℝ)-((z 0).1 q : ℝ))/V-
      ∑ i : Fin K,physicalCoordinateDrift c V basal cat (z i).1 q*(z ((i : ℕ)+1)).2.2 := by
  unfold censoredCoordinatePrefix
  calc
    _ = ∑ i : Fin K,((((z ((i : ℕ)+1)).1 q : ℝ)-((z i).1 q : ℝ))/V-
        physicalCoordinateDrift c V basal cat (z i).1 q*(z ((i : ℕ)+1)).2.2) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [consistent_censored_coordinate_compensation c V basal cat q T i _ _ (hc i i.isLt),
        if_neg (hs i i.isLt),if_pos (ht i i.isLt),min_eq_left (ht i i.isLt)]
      rfl
    _ = _ := by rw [Finset.sum_sub_distrib,coordinate_changes_telescope]

variable {n : ℕ} [MeasurableSpace (PhysicalCountChannel n)]
  [MeasurableSingletonClass (PhysicalCountChannel n)]

theorem physical_coordinate_increment_binding (hn : 2 ≤ n)
    (c : SourceMoleculeFibreConfig n) (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ) (q : Molecule n) :
    ∀ᵐ z ∂physicalTrajectoryLaw hn c V 1 hV (by norm_num) basal cat N, ∀ k,
      (z (k+1)).2.1.elim (fun _ => 0) (coordinateConcentrationJump V q (z k).1) =
        (((z (k+1)).1 q : ℝ)-((z k).1 q : ℝ))/V := by
  have hh := jumpTrajectory_consistent N unboundedPhysicalNext
    (unboundedPhysicalRate c V 1 basal cat) (unboundedPhysicalRate_nonneg c V 1 basal cat)
    (unbounded_total_pos hn c V 1 hV (by norm_num) basal cat)
  filter_upwards [hh] with z hz
  exact fun k => consistent_coordinate_increment V q _ _ (hz k)

end
end RandomViability
