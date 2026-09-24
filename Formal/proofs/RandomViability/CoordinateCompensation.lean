import proofs.RandomViability.PhysicalCoordinateTilt

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 100000

def censoredCoordinateCompensation {n : ℕ} (c : SourceMoleculeFibreConfig n) (V : NNReal)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (q : Molecule n) (T : ℝ) (k : ℕ)
    (h : Finset.Iic k → JumpState (Molecule n → ℕ) (PhysicalCountChannel n))
    (y : JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) : ℝ :=
  let N := (h ⟨k,Finset.mem_Iic.mpr le_rfl⟩).1
  if censoredNonfoodStop V T (massExitStop V) k h then 0 else
    (if y.2.2 ≤ T-prefixElapsed k h then
      y.2.1.elim (fun _ => 0) (coordinateConcentrationJump V q N) else 0)-
    physicalCoordinateDrift c V basal cat N q*min y.2.2 (T-prefixElapsed k h)

def censoredCoordinatePrefix {n : ℕ} (c : SourceMoleculeFibreConfig n) (V : NNReal)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (q : Molecule n) (T : ℝ)
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) (K : ℕ) : ℝ :=
  ∑ i : Fin K,censoredCoordinateCompensation c V basal cat q T
    i (Preorder.frestrictLe (i : ℕ) z) (z ((i : ℕ)+1))

theorem coordinate_multiplier_exp {n : ℕ} (c : SourceMoleculeFibreConfig n) (V : NNReal)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (q : Molecule n) (θ T : ℝ) (k : ℕ)
    (h : Finset.Iic k → JumpState (Molecule n → ℕ) (PhysicalCountChannel n))
    (y : JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) :
    coordinateCensoredMultiplier c V basal cat q θ T k h y =
      ENNReal.ofReal (Real.exp (θ*censoredCoordinateCompensation c V basal cat q T k h y-
        θ^2*(96000/V)*censoredNonfoodWait V T (massExitStop V) k h y)) := by
  unfold coordinateCensoredMultiplier censoredStoppedMultiplier
    censoredCoordinateCompensation censoredNonfoodWait
  dsimp only
  by_cases hs : censoredNonfoodStop V T (massExitStop V) k h
  · simp only [if_pos hs,mul_zero,sub_zero,Real.exp_zero,ENNReal.ofReal_one]
  · simp only [if_neg hs,censoredJumpMultiplier]
    by_cases ht : y.2.2 ≤ T-prefixElapsed k h
    · simp only [if_pos ht,min_eq_left ht]
      unfold jumpMultiplier
      have he : y.2.1.elim (fun _ => (1 : ℝ))
          (fun ch => Real.exp (θ*coordinateConcentrationJump V q (h ⟨k,Finset.mem_Iic.mpr le_rfl⟩).1 ch)) =
          Real.exp (θ*y.2.1.elim (fun _ => 0)
            (coordinateConcentrationJump V q (h ⟨k,Finset.mem_Iic.mpr le_rfl⟩).1)) := by
        cases y.2.1 <;> simp
      rw [he,← ENNReal.ofReal_mul (Real.exp_pos _).le,← Real.exp_add]
      congr 2
      unfold coordinateTiltCompensator
      ring
    · simp only [if_neg ht,min_eq_right (le_of_not_ge ht)]
      congr 2
      unfold coordinateTiltCompensator
      ring

theorem coordinate_product_exp {n : ℕ} (c : SourceMoleculeFibreConfig n) (V : NNReal)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (q : Molecule n) (θ T : ℝ) (K : ℕ)
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) :
    trajectoryProduct (coordinateCensoredMultiplier c V basal cat q θ T) K z =
      ENNReal.ofReal (Real.exp (θ*censoredCoordinatePrefix c V basal cat q T z K-
        θ^2*(96000/V)*(∑ i : Fin K,censoredNonfoodWait V T (massExitStop V)
          i (Preorder.frestrictLe (i : ℕ) z) (z ((i : ℕ)+1))))) := by
  unfold trajectoryProduct censoredCoordinatePrefix
  simp_rw [coordinate_multiplier_exp]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun _ _ => (Real.exp_pos _).le),← Real.exp_sum,
    Finset.sum_sub_distrib,← Finset.mul_sum,← Finset.mul_sum]

theorem consistent_coordinate_increment {n : ℕ} (V : NNReal) (q : Molecule n)
    (N : Molecule n → ℕ) (y : JumpState (Molecule n → ℕ) (PhysicalCountChannel n))
    (hy : jumpConsistent unboundedPhysicalNext N y) :
    y.2.1.elim (fun _ => 0) (coordinateConcentrationJump V q N) =
      ((y.1 q : ℝ)-(N q : ℝ))/V := by
  obtain ⟨ch,hlabel,hnext⟩ := hy
  rw [hlabel]
  change coordinateConcentrationJump V q N ch = _
  rw [hnext]
  rfl

end
end RandomViability
