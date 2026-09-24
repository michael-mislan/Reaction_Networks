import proofs.InheritedCellAssay.RobustSisters

namespace InheritedCellAssay
open scoped BigOperators

/-- rho=0 joint daughter law; identical pairs have total mass (1+kappa)/2. -/
def pairWeight (κ : ℚ) (a b : Bool) : ℚ :=
  if a=b then (1+κ)/4 else (1-κ)/4

def pairMean (κ : ℚ) (f : Bool → Bool → ℚ) : ℚ :=
  ∑ a : Bool, ∑ b : Bool, pairWeight κ a b * f a b

theorem pair_nonnegative (κ : ℚ) (hl : -1 ≤ κ) (hu : κ ≤ 1) (a b : Bool) :
    0 ≤ pairWeight κ a b := by
  unfold pairWeight
  split_ifs <;> linarith

theorem pair_normalized (κ : ℚ) : pairMean κ (fun _ _ => 1) = 1 := by
  simp [pairMean, pairWeight]
  ring

theorem first_daughter_law (κ : ℚ) (a : Bool) :
    (∑ b : Bool, pairWeight κ a b) = 1/2 := by
  cases a <;> simp [pairWeight] <;> ring

def daughterOutput (a : Bool) : ℚ := if a then 8 else 1

theorem selective_pair_mean (κ : ℚ) :
    pairMean κ (fun a b => daughterOutput a + daughterOutput b) = 9 := by
  simp [pairMean, pairWeight, daughterOutput]
  ring

theorem selective_pair_variance (κ : ℚ) :
    pairMean κ (fun a b => (daughterOutput a + daughterOutput b - 9)^2) =
      49*(1+κ)/2 := by
  simp [pairMean, pairWeight, daughterOutput]
  ring

theorem variance_correction (κ : ℚ) :
    pairMean κ (fun a b => (daughterOutput a + daughterOutput b - 9)^2) -
    pairMean 0 (fun a b => (daughterOutput a + daughterOutput b - 9)^2) = 49*κ/2 := by
  rw [selective_pair_variance, selective_pair_variance]
  ring

/-- First-daughter observations cannot determine the selective family's variance. -/
theorem marginal_does_not_identify_variance :
    (∀ a : Bool, (∑ b : Bool, pairWeight (-1) a b) =
      ∑ b : Bool, pairWeight 1 a b) ∧
    pairMean (-1) (fun a b => (daughterOutput a+daughterOutput b-9)^2) = 0 ∧
    pairMean 1 (fun a b => (daughterOutput a+daughterOutput b-9)^2) = 49 := by
  constructor
  · intro a
    rw [first_daughter_law, first_daughter_law]
  · norm_num [selective_pair_variance]

/-- Mixture law for independently selecting identical versus complementary pairs. -/
def independentPairRisk (F : ℕ) (t : ℚ) : ℚ :=
  ∑ k ∈ Finset.range (F+1), (F.choose k : ℚ)*t^k*(1-t)^(F-k)*conditionalRisk F k

theorem maximal_correlation_not_maximal_error :
    independentPairRisk 5 (7/8) > independentPairRisk 5 1 := by
  norm_num [independentPairRisk, conditionalRisk, countExpectation, daughterHigh,
    selectiveFraction, Finset.sum_range_succ, Nat.choose, abs_of_nonneg, abs_of_neg]

end InheritedCellAssay

