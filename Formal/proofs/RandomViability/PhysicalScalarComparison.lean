import proofs.RandomViability.CoordinateObservedPath
import proofs.RandomViability.CompensatedScalarComparison

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory Set RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 100000

theorem coordinate_corrected_jump {n : ℕ} (c : SourceMoleculeFibreConfig n) (V : NNReal)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (q : Molecule n) (T : ℝ)
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) (k : ℕ)
    (hc : jumpConsistent unboundedPhysicalNext (z k).1 (z (k+1)))
    (hs : ¬censoredNonfoodStop V T (massExitStop V) k (Preorder.frestrictLe k z))
    (ht : (z (k+1)).2.2 ≤ T-prefixElapsed k (Preorder.frestrictLe k z)) :
    ((z (k+1)).1 q : ℝ)/V-censoredCoordinatePrefix c V basal cat q T z (k+1) =
      ((z k).1 q : ℝ)/V-censoredCoordinatePrefix c V basal cat q T z k+
      physicalCoordinateDrift c V basal cat (z k).1 q*(z (k+1)).2.2 := by
  have hsucc : censoredCoordinatePrefix c V basal cat q T z (k+1) =
      censoredCoordinatePrefix c V basal cat q T z k+
        censoredCoordinateCompensation c V basal cat q T k (Preorder.frestrictLe k z) (z (k+1)) := by
    unfold censoredCoordinatePrefix
    rw [Fin.sum_univ_castSucc]
    rfl
  rw [hsucc,consistent_censored_coordinate_compensation c V basal cat q T k _ _ hc,
    if_neg hs,if_pos ht,min_eq_left ht]
  change ((z (k+1)).1 q : ℝ)/V-(censoredCoordinatePrefix c V basal cat q T z k+
    ((((z (k+1)).1 q : ℝ)-((z k).1 q : ℝ))/V-
      physicalCoordinateDrift c V basal cat (z k).1 q*(z (k+1)).2.2)) = _
  ring

/-- Actual count-path comparison up to any active complete prefix. The
fluctuation assumptions refer to the same compensation bounded in probability. -/
theorem physical_coordinate_prefix_comparison {n : ℕ}
    (c : SourceMoleculeFibreConfig n) (V : NNReal)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (q : Molecule n) (T a b eta : ℝ)
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) (K : ℕ)
    (ha : 0 < a)
    (hc : ∀ i < K,jumpConsistent unboundedPhysicalNext (z i).1 (z (i+1)))
    (hs : ∀ i < K,¬censoredNonfoodStop V T (massExitStop V) i (Preorder.frestrictLe i z))
    (ht : ∀ i < K,(z (i+1)).2.2 ≤ T-prefixElapsed i (Preorder.frestrictLe i z))
    (hh : ∀ i < K,0 ≤ (z (i+1)).2.2)
    (hd : ∀ i < K,b-a*(((z i).1 q : ℝ)/V) ≤ physicalCoordinateDrift c V basal cat (z i).1 q)
    (hnoise : ∀ i < K,∀ s ∈ Icc 0 (z (i+1)).2.2,
      coordinateCompensationWithinInterval c V basal cat q T z i s ≤ eta)
    (hend : -eta ≤ censoredCoordinatePrefix c V basal cat q T z K) :
    ((((z 0).1 q : ℝ)/V)-(b/a-eta))/Real.exp (a*prefixElapsed K (Preorder.frestrictLe K z))+
      b/a-2*eta ≤ ((z K).1 q : ℝ)/V := by
  apply compensated_scalar_prefix_lower
    (fun i => ((z i).1 q : ℝ)/V) (censoredCoordinatePrefix c V basal cat q T z)
    (fun i => physicalCoordinateDrift c V basal cat (z i).1 q) (fun i => (z (i+1)).2.2)
    a b eta K ha
  · simp [censoredCoordinatePrefix]
  · exact hh
  · exact hd
  · intro i hi s hsi
    simpa only [coordinateCompensationWithinInterval,if_neg (hs i hi)] using hnoise i hi s hsi
  · intro i hi
    exact coordinate_corrected_jump c V basal cat q T z i (hc i hi) (hs i hi) (ht i hi)
  · exact hend

end
end RandomViability
