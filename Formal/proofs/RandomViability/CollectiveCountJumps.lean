import proofs.RandomViability.PhysicalTotalRate
import proofs.RandomViability.BoundedRewardIdentity

namespace RandomViability
open Classical RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 40000

theorem food_mass_weight_le_two {n : ℕ} (z : Molecule n) : foodMassWeight z ≤ 2 := by
  unfold foodMassWeight
  split_ifs with h
  · exact_mod_cast h
  · norm_num

theorem ligation_nonfood_gain_le_four {n : ℕ} (r : Reaction n) :
    0 ≤ ligationNonfoodMassGain r ∧ ligationNonfoodMassGain r ≤ 4 := by
  have hh := ligationNonfoodMassGain_bounds r
  exact ⟨hh.1,by linarith [food_mass_weight_le_two (reactionLeft r),food_mass_weight_le_two (reactionRight r)]⟩

theorem basal_nonfood_raw_change {n : ℕ} (N : Molecule n → ℕ)
    (r : Reaction n) (d : Bool)
    (he : ∀ x, physicalChannelInput (.inr (.inl (r,d))) x ≤ N x) :
    countNonfoodMass (applyCountChannel N (physicalChannelInput (.inr (.inl (r,d))))
      (physicalChannelOutput (.inr (.inl (r,d))))) - countNonfoodMass N =
      if d then ligationNonfoodMassGain r else -ligationNonfoodMassGain r := by
  unfold countNonfoodMass
  rw [weightedCountMass_change _ _ _ _ he,ligationNonfoodMassGain_eq_mass_difference]
  cases d <;>
    simp [weightedCountMass,physicalChannelInput,physicalChannelOutput,
      singleCount,Nat.cast_add,mul_add,Finset.sum_add_distrib,mul_ite] <;> ring

theorem unbounded_basal_nonfood_jump_sq {n : ℕ} (N : Molecule n → ℕ)
    (r : Reaction n) (d : Bool) :
    (countNonfoodMass (unboundedPhysicalNext N (.inr (.inl (r,d))))-countNonfoodMass N)^2 ≤ 16 := by
  by_cases he : ∀ x, physicalChannelInput (.inr (.inl (r,d))) x ≤ N x
  · rw [unboundedPhysicalNext,if_pos he,basal_nonfood_raw_change N r d he]
    have hg := ligation_nonfood_gain_le_four r
    cases d with
    | false =>
      change (-ligationNonfoodMassGain r)^2 ≤ 16
      nlinarith
    | true =>
      change (ligationNonfoodMassGain r)^2 ≤ 16
      nlinarith
  · simp [unboundedPhysicalNext,he]

theorem unbounded_catalytic_nonfood_jump_sq {n : ℕ} (N : Molecule n → ℕ)
    (r : Reaction n) (x : Molecule n) (d : Bool) :
    (countNonfoodMass (unboundedPhysicalNext N (.inr (.inr (r,x,d))))-countNonfoodMass N)^2 ≤ 16 := by
  by_cases he : ∀ z, physicalChannelInput (.inr (.inr (r,x,d))) z ≤ N z
  · rw [unboundedPhysicalNext,if_pos he,catalytic_nonfood_raw_change N r x d he]
    have hg := ligation_nonfood_gain_le_four r
    cases d with
    | false =>
      change (-ligationNonfoodMassGain r)^2 ≤ 16
      nlinarith
    | true =>
      change (ligationNonfoodMassGain r)^2 ≤ 16
      nlinarith
  · simp [unboundedPhysicalNext,he]

theorem unbounded_feed_nonfood_jump {n : ℕ} (N : Molecule n → ℕ) (f : ↥(binaryFood n 2)) :
    countNonfoodMass (unboundedPhysicalNext N (.inl (.inl f)))-countNonfoodMass N = 0 := by
  have he : ∀ z, physicalChannelInput (.inl (.inl f)) z ≤ N z := fun _ => Nat.zero_le _
  rw [unboundedPhysicalNext,if_pos he]
  unfold countNonfoodMass
  rw [weightedCountMass_change _ _ _ _ he]
  have hf : molLength f.val ≤ 2 := (Finset.mem_filter.mp f.property).2
  simp [weightedCountMass,physicalChannelInput,physicalChannelOutput,singleCount,mul_ite,
    foodMassWeight,hf]

theorem unbounded_outflow_nonfood_jump_sq {n : ℕ} (N : Molecule n → ℕ) (x : Molecule n) :
    (countNonfoodMass (unboundedPhysicalNext N (.inl (.inr x)))-countNonfoodMass N)^2 ≤
      (n : ℝ)*molLength x := by
  by_cases he : ∀ z, physicalChannelInput (.inl (.inr x)) z ≤ N z
  · rw [unboundedPhysicalNext,if_pos he]
    unfold countNonfoodMass
    rw [weightedCountMass_change _ _ _ _ he]
    simp only [weightedCountMass,physicalChannelInput,physicalChannelOutput,singleCount]
    simp only [Nat.cast_zero,mul_zero,Finset.sum_const_zero,Nat.cast_ite,Nat.cast_one,mul_ite,
      mul_one,Finset.sum_ite_eq',Finset.mem_univ,ite_true,zero_sub,neg_sq]
    have hl : molLength x ≤ n := by simp [molLength]
    have hlR : (molLength x : ℝ) ≤ n := by exact_mod_cast hl
    unfold foodMassWeight
    split_ifs
    · simp
      positivity
    · simp only [sub_zero]
      nlinarith [show (0 : ℝ) ≤ molLength x by positivity]
  · simp [unboundedPhysicalNext,he]
    positivity

end
end RandomViability
