import proofs.RandomViability.ProductivePathRates
import proofs.RandomViability.FoodCutoff

namespace RandomViability
open Classical RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 30000

/-- The length-four product with code3, split into two length-two foods. -/
def productiveReaction {n : ℕ} (hn : 4 ≤ n) : Reaction n :=
  ⟨⟨3,by omega⟩,⟨⟨3,by norm_num⟩,⟨1,by norm_num⟩⟩⟩

theorem productive_reaction_lengths {n : ℕ} (hn : 4 ≤ n) :
    molLength (reactionLeft (productiveReaction hn)) = 2 ∧
    molLength (reactionRight (productiveReaction hn)) = 2 ∧
    molLength (reactionProduct (productiveReaction hn)) = 4 := by
  simp [productiveReaction, reactionLeftLength, reactionRightLength, reactionProductLength]

theorem productive_reaction_distinct {n : ℕ} (hn : 4 ≤ n) :
    reactionLeft (productiveReaction hn) ≠ reactionRight (productiveReaction hn) ∧
    reactionLeft (productiveReaction hn) ≠ reactionProduct (productiveReaction hn) ∧
    reactionRight (productiveReaction hn) ≠ reactionProduct (productiveReaction hn) := by
  have hl := productive_reaction_lengths hn
  refine ⟨?_,?_,?_⟩
  · intro h
    have hh := congrArg (fun z : Molecule n => z.2.val) h
    simp only [reactionLeft, reactionRight, moleculeOfCode, splitCodes,
      finProdFinEquiv, Equiv.coe_fn_symm_mk, Fin.val_cast] at hh
    norm_num [productiveReaction, reactionLeftLength, reactionRightLength,
      Fin.divNat, Fin.modNat] at hh
    have hc : (productiveReaction hn).2.1.val = 3 := rfl
    have hs : (productiveReaction hn).2.2.val = 1 := rfl
    rw [hc, hs] at hh
    norm_num at hh
  · intro h
    have hh := congrArg molLength h
    omega
  · intro h
    have hh := congrArg molLength h
    omega

theorem productive_reaction_food {n : ℕ} (hn : 4 ≤ n) :
    reactionLeft (productiveReaction hn) ∈ binaryFood n 2 ∧
    reactionRight (productiveReaction hn) ∈ binaryFood n 2 ∧
    reactionProduct (productiveReaction hn) ∉ binaryFood n 2 := by
  have hl := productive_reaction_lengths hn
  simp only [binaryFood, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨by omega,by omega,by omega⟩

def foodOnlyCounts (n V : ℕ) (z : Molecule n) : ℕ :=
  if z ∈ binaryFood n 2 then V else 0

theorem food_only_count_mass_le {n : ℕ} (hn : 2 ≤ n) (V : ℕ) :
    countMass (foodOnlyCounts n V) ≤ 10*V := by
  apply food_count_mass_bound hn (foodOnlyCounts n V) ?_ V ?_
  · intro z hz
    by_cases hf : z ∈ binaryFood n 2
    · exact hf
    · simp [foodOnlyCounts,hf] at hz
  · intro z hz
    simp [foodOnlyCounts,hz]

theorem productive_initial_counts {n : ℕ} (hn : 4 ≤ n) (V : ℕ) :
    foodOnlyCounts n V (reactionLeft (productiveReaction hn)) = V ∧
    foodOnlyCounts n V (reactionRight (productiveReaction hn)) = V ∧
    foodOnlyCounts n V (reactionProduct (productiveReaction hn)) = 0 := by
  have hf := productive_reaction_food hn
  simp [foodOnlyCounts,hf.1,hf.2.1,hf.2.2]

end
end RandomViability
