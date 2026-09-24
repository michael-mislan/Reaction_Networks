import proofs.RandomViability.CensoredStateProducts
import proofs.RandomViability.PhysicalNonfoodTilt
import proofs.RandomViability.PredictableProductCrossing

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 100000

def censoredNonfoodStop {n : ℕ} (V : NNReal) (T : ℝ)
    (stop : (k : ℕ) → (Finset.Iic k → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) → Prop)
    (k : ℕ) (h : Finset.Iic k → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) : Prop :=
  stop k h ∨ ¬(countMass (h ⟨k,Finset.mem_Iic.mpr le_rfl⟩).1 : ℝ) ≤ 11*V ∨ T ≤ prefixElapsed k h

def censoredNonfoodMultiplier {n : ℕ} (c : SourceMoleculeFibreConfig n) (V : NNReal)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal) (θ T : ℝ)
    (stop : (k : ℕ) → (Finset.Iic k → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) → Prop) :=
  censoredStoppedMultiplier (fun N ch => Real.exp (θ*nonfoodConcentrationJump V N ch))
    (nonfoodTiltCompensator c V basal cat θ) (fun k h => T-prefixElapsed k h)
    (censoredNonfoodStop V T stop)

variable {n : ℕ} [MeasurableSpace (PhysicalCountChannel n)]
  [MeasurableSingletonClass (PhysicalCountChannel n)]

omit [MeasurableSingletonClass (PhysicalCountChannel n)] in
theorem censoredNonfoodStop_measurable (V : NNReal) (T : ℝ)
    (stop : (k : ℕ) → (Finset.Iic k → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) → Prop)
    (hstop : ∀ k,MeasurableSet {h | stop k h}) (k : ℕ) :
    MeasurableSet {h | censoredNonfoodStop V T stop k h} := by
  have hN : Measurable (fun h : Finset.Iic k → JumpState (Molecule n → ℕ) (PhysicalCountChannel n) =>
      (h ⟨k,Finset.mem_Iic.mpr le_rfl⟩).1) := (measurable_pi_apply _).fst
  exact (hstop k).union (((measurableSet_le
    ((measurable_of_countable (fun N : Molecule n → ℕ => (countMass N : ℝ))).comp hN)
    measurable_const).compl).union (measurableSet_le measurable_const (prefixElapsed_measurable k)))

theorem censoredNonfoodMultiplier_measurable (c : SourceMoleculeFibreConfig n) (V : NNReal)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal) (θ T : ℝ)
    (stop : (k : ℕ) → (Finset.Iic k → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) → Prop)
    (hstop : ∀ k,MeasurableSet {h | stop k h}) (k : ℕ) :
    Measurable (fun p : (Finset.Iic k → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) ×
      JumpState (Molecule n → ℕ) (PhysicalCountChannel n) =>
        censoredNonfoodMultiplier c V basal cat θ T stop k p.1 p.2) :=
  censoredStoppedMultiplier_measurable _ _ _
    (fun j => measurable_const.sub (prefixElapsed_measurable j)) _
    (censoredNonfoodStop_measurable V T stop hstop) k

theorem physical_censored_nonfood_mean (hn : 4 ≤ n)
    (c : SourceMoleculeFibreConfig n) (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (hbasal : ∀ r,(basal r : ℝ) ≤ 1) (hcat : ∀ r z,(cat r z : ℝ) ≤ 16)
    (θ T : ℝ) (hθ : |θ| *((n : ℝ)/V) ≤ 1)
    (stop : (k : ℕ) → (Finset.Iic k → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) → Prop)
    (k : ℕ) (h : Finset.Iic k → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) :
    (∫⁻ y,censoredNonfoodMultiplier c V basal cat θ T stop k h y
      ∂jumpHistoryKernel unboundedPhysicalNext (unboundedPhysicalRate c V 1 basal cat)
        (unboundedPhysicalRate_nonneg c V 1 basal cat)
        (unbounded_total_pos (by omega : 2 ≤ n) c V 1 hV (by norm_num) basal cat) k h) ≤ 1 := by
  by_cases hs : censoredNonfoodStop V T stop k h
  · simp only [censoredNonfoodMultiplier,censoredStoppedMultiplier,if_pos hs]
    simp
  · have hsplit := not_or.mp hs
    have hM := not_not.mp (not_or.mp hsplit.2).1
    have hrem : 0 ≤ T-prefixElapsed k h := sub_nonneg.mpr (le_of_not_ge (not_or.mp hsplit.2).2)
    simp only [censoredNonfoodMultiplier,censoredStoppedMultiplier,if_neg hs]
    exact jumpState_censored_tilt_le_one unboundedPhysicalNext (unboundedPhysicalRate c V 1 basal cat)
      (unboundedPhysicalRate_nonneg c V 1 basal cat)
      (unbounded_total_pos (by omega : 2 ≤ n) c V 1 hV (by norm_num) basal cat)
      (h ⟨k,Finset.mem_Iic.mpr le_rfl⟩).1
      (nonfoodConcentrationJump V (h ⟨k,Finset.mem_Iic.mpr le_rfl⟩).1) θ
      (nonfoodTiltCompensator c V basal cat θ (h ⟨k,Finset.mem_Iic.mpr le_rfl⟩).1)
      (T-prefixElapsed k h) hrem
      (physical_nonfood_tilt_generator hn c V hV basal cat _ hM hbasal hcat θ hθ)

/-- The last holding interval is censored at the physical deadline T. The
no-jump factor remains in the product, including when the drift compensator
is negative. -/
theorem physical_censored_nonfood_product (hn : 4 ≤ n)
    (c : SourceMoleculeFibreConfig n) (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ)
    (hbasal : ∀ r,(basal r : ℝ) ≤ 1) (hcat : ∀ r z,(cat r z : ℝ) ≤ 16)
    (θ T : ℝ) (hθ : |θ| *((n : ℝ)/V) ≤ 1)
    (stop : (k : ℕ) → (Finset.Iic k → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) → Prop)
    (hstop : ∀ k,MeasurableSet {h | stop k h}) (K : ℕ) :
    (∫⁻ z,trajectoryProduct (censoredNonfoodMultiplier c V basal cat θ T stop) K z
      ∂physicalTrajectoryLaw (by omega : 2 ≤ n) c V 1 hV (by norm_num) basal cat N) ≤ 1 := by
  simpa only [one_pow] using predictable_product_integral_le
    (physicalTrajectoryLaw (by omega : 2 ≤ n) c V 1 hV (by norm_num) basal cat N)
    (jumpHistoryKernel unboundedPhysicalNext (unboundedPhysicalRate c V 1 basal cat)
      (unboundedPhysicalRate_nonneg c V 1 basal cat)
      (unbounded_total_pos (by omega : 2 ≤ n) c V 1 hV (by norm_num) basal cat))
    (fun k => physicalTrajectoryLaw_transition (by omega : 2 ≤ n) c V 1 hV (by norm_num) basal cat N k)
    (censoredNonfoodMultiplier c V basal cat θ T stop)
    (censoredNonfoodMultiplier_measurable c V basal cat θ T stop hstop) 1
    (physical_censored_nonfood_mean hn c V hV basal cat hbasal hcat θ T hθ stop) K

end
end RandomViability
