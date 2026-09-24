import proofs.RandomViability.PhysicalCensoredNonfood

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 100000

def censoredNonfoodWait {n : ℕ} (V : NNReal) (T : ℝ)
    (stop : (k : ℕ) → (Finset.Iic k → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) → Prop)
    (k : ℕ) (h : Finset.Iic k → JumpState (Molecule n → ℕ) (PhysicalCountChannel n))
    (y : JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) : ℝ :=
  if censoredNonfoodStop V T stop k h then 0 else min y.2.2 (T-prefixElapsed k h)

def censoredNonfoodCompensation {n : ℕ} (c : SourceMoleculeFibreConfig n) (V : NNReal)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal) (T : ℝ)
    (stop : (k : ℕ) → (Finset.Iic k → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) → Prop)
    (k : ℕ) (h : Finset.Iic k → JumpState (Molecule n → ℕ) (PhysicalCountChannel n))
    (y : JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) : ℝ :=
  let N := (h ⟨k,Finset.mem_Iic.mpr le_rfl⟩).1
  if censoredNonfoodStop V T stop k h then 0 else
    (if y.2.2 ≤ T-prefixElapsed k h then
      y.2.1.elim (fun _ => 0) (nonfoodConcentrationJump V N) else 0)-
    (∑ ch,unboundedPhysicalRate c V 1 basal cat N ch*nonfoodConcentrationJump V N ch)*
      min y.2.2 (T-prefixElapsed k h)

theorem censored_nonfood_multiplier_exp {n : ℕ} (c : SourceMoleculeFibreConfig n) (V : NNReal)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal) (θ T : ℝ)
    (stop : (k : ℕ) → (Finset.Iic k → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) → Prop)
    (k : ℕ) (h : Finset.Iic k → JumpState (Molecule n → ℕ) (PhysicalCountChannel n))
    (y : JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) :
    censoredNonfoodMultiplier c V basal cat θ T stop k h y =
      ENNReal.ofReal (Real.exp (θ*censoredNonfoodCompensation c V basal cat T stop k h y-
        θ^2*((384000+11*(n : ℝ))/V)*censoredNonfoodWait V T stop k h y)) := by
  unfold censoredNonfoodMultiplier censoredStoppedMultiplier censoredNonfoodCompensation censoredNonfoodWait
  dsimp only
  by_cases hs : censoredNonfoodStop V T stop k h
  · simp only [if_pos hs,mul_zero,sub_zero,Real.exp_zero,ENNReal.ofReal_one]
  · simp only [if_neg hs,censoredJumpMultiplier]
    by_cases ht : y.2.2 ≤ T-prefixElapsed k h
    · simp only [if_pos ht,min_eq_left ht]
      unfold jumpMultiplier
      have he : y.2.1.elim (fun _ => (1 : ℝ))
          (fun ch => Real.exp (θ*nonfoodConcentrationJump V (h ⟨k,Finset.mem_Iic.mpr le_rfl⟩).1 ch)) =
          Real.exp (θ*y.2.1.elim (fun _ => 0)
            (nonfoodConcentrationJump V (h ⟨k,Finset.mem_Iic.mpr le_rfl⟩).1)) := by
        cases y.2.1 <;> simp
      rw [he,← ENNReal.ofReal_mul (Real.exp_pos _).le,← Real.exp_add]
      congr 2
      unfold nonfoodTiltCompensator
      ring
    · simp only [if_neg ht,min_eq_right (le_of_not_ge ht)]
      congr 2
      unfold nonfoodTiltCompensator
      ring

theorem censored_nonfood_product_exp {n : ℕ} (c : SourceMoleculeFibreConfig n) (V : NNReal)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal) (θ T : ℝ)
    (stop : (k : ℕ) → (Finset.Iic k → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) → Prop)
    (K : ℕ) (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) :
    trajectoryProduct (censoredNonfoodMultiplier c V basal cat θ T stop) K z =
      ENNReal.ofReal (Real.exp
        (θ*(∑ i : Fin K,censoredNonfoodCompensation c V basal cat T stop
          i (Preorder.frestrictLe (i : ℕ) z) (z ((i : ℕ)+1)))-
        θ^2*((384000+11*(n : ℝ))/V)*(∑ i : Fin K,censoredNonfoodWait V T stop
          i (Preorder.frestrictLe (i : ℕ) z) (z ((i : ℕ)+1))))) := by
  unfold trajectoryProduct
  simp_rw [censored_nonfood_multiplier_exp]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun _ _ => (Real.exp_pos _).le),← Real.exp_sum,
    Finset.sum_sub_distrib,← Finset.mul_sum,← Finset.mul_sum]

end
end RandomViability
