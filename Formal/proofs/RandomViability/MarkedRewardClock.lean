import proofs.RandomViability.CensoredNonfoodTime
import proofs.RandomViability.CollectiveConcentrationScale
import proofs.RandomViability.JumpWaitingSupport

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 100000

/-- Compensation for a specified marked reward, retaining the established clock envelope. -/
def markedRewardTilt {n : ℕ} (c : SourceMoleculeFibreConfig n) (V : NNReal)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (reward : (Molecule n → ℕ) → PhysicalCountChannel n → ℝ)
    (θ : ℝ) (N : Molecule n → ℕ) : ℝ :=
  θ*(∑ ch,unboundedPhysicalRate c V 1 basal cat N ch*reward N ch)+
    θ^2*((384000+11*(n : ℝ))/V)

def censoredMarkedRewardMultiplier {n : ℕ} (c : SourceMoleculeFibreConfig n) (V : NNReal)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal) (reward : (Molecule n → ℕ) → PhysicalCountChannel n → ℝ) (θ T : ℝ)
    (stop : (k : ℕ) → (Finset.Iic k → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) → Prop) :=
  censoredStoppedMultiplier (fun N ch => Real.exp (θ*reward N ch))
    (markedRewardTilt c V basal cat reward θ) (fun k h => T-prefixElapsed k h)
    (censoredNonfoodStop V T stop)

variable {n : ℕ} [MeasurableSpace (PhysicalCountChannel n)]
  [MeasurableSingletonClass (PhysicalCountChannel n)]

theorem censoredMarkedRewardMultiplier_measurable (c : SourceMoleculeFibreConfig n) (V : NNReal)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal) (reward : (Molecule n → ℕ) → PhysicalCountChannel n → ℝ) (θ T : ℝ)
    (stop : (k : ℕ) → (Finset.Iic k → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) → Prop)
    (hstop : ∀ k,MeasurableSet {h | stop k h}) (k : ℕ) :
    Measurable (fun p : (Finset.Iic k → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) ×
      JumpState (Molecule n → ℕ) (PhysicalCountChannel n) =>
        censoredMarkedRewardMultiplier c V basal cat reward θ T stop k p.1 p.2) :=
  censoredStoppedMultiplier_measurable _ _ _
    (fun j => measurable_const.sub (prefixElapsed_measurable j)) _
    (censoredNonfoodStop_measurable V T stop hstop) k

theorem physical_censored_marked_reward_mean (hn : 4 ≤ n)
    (c : SourceMoleculeFibreConfig n) (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (reward : (Molecule n → ℕ) → PhysicalCountChannel n → ℝ) (θ T : ℝ) (hgen : ∀ N,(countMass N : ℝ) ≤ 11*V →
      (∑ ch,unboundedPhysicalRate c V 1 basal cat N ch*(Real.exp (θ*reward N ch)-1)) ≤
        markedRewardTilt c V basal cat reward θ N)
    (stop : (k : ℕ) → (Finset.Iic k → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) → Prop)
    (k : ℕ) (h : Finset.Iic k → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) :
    (∫⁻ y,censoredMarkedRewardMultiplier c V basal cat reward θ T stop k h y
      ∂jumpHistoryKernel unboundedPhysicalNext (unboundedPhysicalRate c V 1 basal cat)
        (unboundedPhysicalRate_nonneg c V 1 basal cat)
        (unbounded_total_pos (by omega : 2 ≤ n) c V 1 hV (by norm_num) basal cat) k h) ≤ 1 := by
  by_cases hs : censoredNonfoodStop V T stop k h
  · simp only [censoredMarkedRewardMultiplier,censoredStoppedMultiplier,if_pos hs]
    simp
  · have hsplit := not_or.mp hs
    have hM := not_not.mp (not_or.mp hsplit.2).1
    have hrem : 0 ≤ T-prefixElapsed k h := sub_nonneg.mpr (le_of_not_ge (not_or.mp hsplit.2).2)
    simp only [censoredMarkedRewardMultiplier,censoredStoppedMultiplier,if_neg hs]
    exact jumpState_censored_tilt_le_one unboundedPhysicalNext (unboundedPhysicalRate c V 1 basal cat)
      (unboundedPhysicalRate_nonneg c V 1 basal cat)
      (unbounded_total_pos (by omega : 2 ≤ n) c V 1 hV (by norm_num) basal cat)
      (h ⟨k,Finset.mem_Iic.mpr le_rfl⟩).1
      (reward (h ⟨k,Finset.mem_Iic.mpr le_rfl⟩).1) θ
      (markedRewardTilt c V basal cat reward θ (h ⟨k,Finset.mem_Iic.mpr le_rfl⟩).1)
      (T-prefixElapsed k h) hrem
      (hgen _ hM)

def censoredMarkedRewardCompensation {n : ℕ} (c : SourceMoleculeFibreConfig n) (V : NNReal)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal) (reward : (Molecule n → ℕ) → PhysicalCountChannel n → ℝ) (T : ℝ)
    (stop : (k : ℕ) → (Finset.Iic k → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) → Prop)
    (k : ℕ) (h : Finset.Iic k → JumpState (Molecule n → ℕ) (PhysicalCountChannel n))
    (y : JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) : ℝ :=
  let N := (h ⟨k,Finset.mem_Iic.mpr le_rfl⟩).1
  if censoredNonfoodStop V T stop k h then 0 else
    (if y.2.2 ≤ T-prefixElapsed k h then
      y.2.1.elim (fun _ => 0) (reward N) else 0)-
    (∑ ch,unboundedPhysicalRate c V 1 basal cat N ch*reward N ch)*
      min y.2.2 (T-prefixElapsed k h)

theorem censored_marked_reward_multiplier_exp {n : ℕ} (c : SourceMoleculeFibreConfig n) (V : NNReal)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal) (reward : (Molecule n → ℕ) → PhysicalCountChannel n → ℝ) (θ T : ℝ)
    (stop : (k : ℕ) → (Finset.Iic k → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) → Prop)
    (k : ℕ) (h : Finset.Iic k → JumpState (Molecule n → ℕ) (PhysicalCountChannel n))
    (y : JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) :
    censoredMarkedRewardMultiplier c V basal cat reward θ T stop k h y =
      ENNReal.ofReal (Real.exp (θ*censoredMarkedRewardCompensation c V basal cat reward T stop k h y-
        θ^2*((384000+11*(n : ℝ))/V)*censoredNonfoodWait V T stop k h y)) := by
  unfold censoredMarkedRewardMultiplier censoredStoppedMultiplier censoredMarkedRewardCompensation censoredNonfoodWait
  dsimp only
  by_cases hs : censoredNonfoodStop V T stop k h
  · simp only [if_pos hs,mul_zero,sub_zero,Real.exp_zero,ENNReal.ofReal_one]
  · simp only [if_neg hs,censoredJumpMultiplier]
    by_cases ht : y.2.2 ≤ T-prefixElapsed k h
    · simp only [if_pos ht,min_eq_left ht]
      unfold jumpMultiplier
      have he : y.2.1.elim (fun _ => (1 : ℝ))
          (fun ch => Real.exp (θ*reward (h ⟨k,Finset.mem_Iic.mpr le_rfl⟩).1 ch)) =
          Real.exp (θ*y.2.1.elim (fun _ => 0)
            (reward (h ⟨k,Finset.mem_Iic.mpr le_rfl⟩).1)) := by
        cases y.2.1 <;> simp
      rw [he,← ENNReal.ofReal_mul (Real.exp_pos _).le,← Real.exp_add]
      congr 2
      unfold markedRewardTilt
      ring
    · simp only [if_neg ht,min_eq_right (le_of_not_ge ht)]
      congr 2
      unfold markedRewardTilt
      ring

theorem censored_marked_reward_product_exp {n : ℕ} (c : SourceMoleculeFibreConfig n) (V : NNReal)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal) (reward : (Molecule n → ℕ) → PhysicalCountChannel n → ℝ) (θ T : ℝ)
    (stop : (k : ℕ) → (Finset.Iic k → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) → Prop)
    (K : ℕ) (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) :
    trajectoryProduct (censoredMarkedRewardMultiplier c V basal cat reward θ T stop) K z =
      ENNReal.ofReal (Real.exp
        (θ*(∑ i : Fin K,censoredMarkedRewardCompensation c V basal cat reward T stop
          i (Preorder.frestrictLe (i : ℕ) z) (z ((i : ℕ)+1)))-
        θ^2*((384000+11*(n : ℝ))/V)*(∑ i : Fin K,censoredNonfoodWait V T stop
          i (Preorder.frestrictLe (i : ℕ) z) (z ((i : ℕ)+1))))) := by
  unfold trajectoryProduct
  simp_rw [censored_marked_reward_multiplier_exp]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun _ _ => (Real.exp_pos _).le),← Real.exp_sum,
    Finset.sum_sub_distrib,← Finset.mul_sum,← Finset.mul_sum]

end
end RandomViability
