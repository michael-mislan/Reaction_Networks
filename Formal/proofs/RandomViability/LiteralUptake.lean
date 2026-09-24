import proofs.RandomViability.FoodUptake

namespace RandomViability
open Classical RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF
noncomputable section

/-- Ordered sampling without replacement from the reactant multiset {u,w,z}.
The successive subtractions handle every substrate/catalyst coincidence. -/
def literalTriple {α : Type*} [DecidableEq α] (N : α → ℕ) (u w z : α) : ℕ :=
  N u * (N w - if w = u then 1 else 0) *
    (N z - (if z = u then 1 else 0) - (if z = w then 1 else 0))

theorem literalTriple_le_product {α : Type*} [DecidableEq α]
    (N : α → ℕ) (u w z : α) : literalTriple N u w z ≤ N u * N w * N z := by
  unfold literalTriple
  exact Nat.mul_le_mul
    (Nat.mul_le_mul_left (N u) (Nat.sub_le _ _))
    ((Nat.sub_le _ _).trans (Nat.sub_le _ _))

def ligationNonfoodMassGain {n : ℕ} (r : Reaction n) : ℝ :=
  foodMassWeight (reactionLeft r) + foodMassWeight (reactionRight r) -
    foodMassWeight (reactionProduct r)

theorem ligationNonfoodMassGain_bounds {n : ℕ} (r : Reaction n) :
    0 ≤ ligationNonfoodMassGain r ∧
    ligationNonfoodMassGain r ≤ foodMassWeight (reactionLeft r) + foodMassWeight (reactionRight r) := by
  have hlen : molLength (reactionLeft r) + molLength (reactionRight r) = molLength (reactionProduct r) := by
    simpa only [molLength_reactionLeft, molLength_reactionRight, molLength_reactionProduct] using reaction_length_add r
  constructor
  · by_cases hp : molLength (reactionProduct r) ≤ 2
    · have hl : molLength (reactionLeft r) ≤ 2 := by omega
      have hr : molLength (reactionRight r) ≤ 2 := by omega
      have hlw : foodMassWeight (reactionLeft r) = molLength (reactionLeft r) := if_pos hl
      have hrw : foodMassWeight (reactionRight r) = molLength (reactionRight r) := if_pos hr
      have hpw : foodMassWeight (reactionProduct r) = molLength (reactionProduct r) := if_pos hp
      unfold ligationNonfoodMassGain
      rw [hlw, hrw, hpw]
      have he : (molLength (reactionLeft r) : ℝ) + molLength (reactionRight r) = molLength (reactionProduct r) := by exact_mod_cast hlen
      linarith
    · have hpw : foodMassWeight (reactionProduct r) = 0 := if_neg hp
      unfold ligationNonfoodMassGain
      rw [hpw, sub_zero]
      exact add_nonneg (foodMassWeight_nonneg _) (foodMassWeight_nonneg _)
  · unfold ligationNonfoodMassGain
    exact sub_le_self _ (foodMassWeight_nonneg _)

/-- Unnormalized intensity numerator. Dividing by V^2 gives the cubic
single-catalyst molecular-count propensity, weighted by nonfood mass gain. -/
def literalFoodUptakeNumerator {n : ℕ} (c : SourceMoleculeFibreConfig n)
    (N : Molecule n → ℕ) (rate : Reaction n → Molecule n → ℝ) : ℝ :=
  ∑ z, ∑ r : Reaction n, if r ∈ c z then ligationNonfoodMassGain r * rate r z *
    (literalTriple N (reactionLeft r) (reactionRight r) z : ℝ) else 0

theorem literalFoodUptakeNumerator_le_envelope {n : ℕ} (c : SourceMoleculeFibreConfig n)
    (N : Molecule n → ℕ) (rate : Reaction n → Molecule n → ℝ) (κ : ℝ)
    (hκ : 0 ≤ κ) (hrate : ∀ r z, rate r z ≤ κ) :
    literalFoodUptakeNumerator c N rate ≤ κ * catalyticFoodEnvelope c (fun z => (N z : ℝ)) := by
  unfold literalFoodUptakeNumerator catalyticFoodEnvelope
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro z _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro r _
  by_cases hs : r ∈ c z
  · rw [if_pos hs, if_pos hs]
    have hg := ligationNonfoodMassGain_bounds r
    have ht : (literalTriple N (reactionLeft r) (reactionRight r) z : ℝ) ≤
        (N (reactionLeft r) : ℝ) * N (reactionRight r) * N z := by
      exact_mod_cast literalTriple_le_product N (reactionLeft r) (reactionRight r) z
    calc
      _ ≤ ligationNonfoodMassGain r * κ * (literalTriple N (reactionLeft r) (reactionRight r) z : ℝ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hrate r z) hg.1) (Nat.cast_nonneg _)
      _ ≤ ligationNonfoodMassGain r * κ * ((N (reactionLeft r) : ℝ) * N (reactionRight r) * N z) :=
        mul_le_mul_of_nonneg_left ht (mul_nonneg hg.1 hκ)
      _ ≤ (foodMassWeight (reactionLeft r) + foodMassWeight (reactionRight r)) * κ *
          ((N (reactionLeft r) : ℝ) * N (reactionRight r) * N z) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hg.2 hκ) (by positivity)
      _ = _ := by ring
  · rw [if_neg hs, if_neg hs, mul_zero]

theorem literalFoodUptakeNumerator_mass_bound {n k : ℕ} (c : SourceMoleculeFibreConfig n)
    (hgood : ¬ ShortIncidence k c) (N : Molecule n → ℕ)
    (rate : Reaction n → Molecule n → ℝ) (κ : ℝ)
    (hκ : 0 ≤ κ) (hrate : ∀ r z, rate r z ≤ κ) :
    (k : ℝ) * literalFoodUptakeNumerator c N rate ≤
      4 * κ * (polymerMass (fun z => (N z : ℝ)))^3 := by
  have he := literalFoodUptakeNumerator_le_envelope c N rate κ hκ hrate
  have hm := catalyticFoodEnvelope_mass_bound c hgood (fun z => (N z : ℝ)) (fun z => Nat.cast_nonneg _)
  calc
    _ ≤ (k : ℝ) * (κ * catalyticFoodEnvelope c (fun z => (N z : ℝ))) :=
      mul_le_mul_of_nonneg_left he (Nat.cast_nonneg k)
    _ = κ * ((k : ℝ) * catalyticFoodEnvelope c (fun z => (N z : ℝ))) := by ring
    _ ≤ κ * (4 * (polymerMass (fun z => (N z : ℝ)))^3) := mul_le_mul_of_nonneg_left hm hκ
    _ = _ := by ring

theorem ligationNonfoodMassGain_eq_mass_difference {n : ℕ} (r : Reaction n) :
    ligationNonfoodMassGain r =
      ((molLength (reactionProduct r) : ℝ) - foodMassWeight (reactionProduct r)) -
      ((molLength (reactionLeft r) : ℝ) - foodMassWeight (reactionLeft r)) -
      ((molLength (reactionRight r) : ℝ) - foodMassWeight (reactionRight r)) := by
  have hl : (molLength (reactionLeft r) : ℝ) + molLength (reactionRight r) = molLength (reactionProduct r) := by
    exact_mod_cast (show molLength (reactionLeft r) + molLength (reactionRight r) = molLength (reactionProduct r) by
      simpa only [molLength_reactionLeft, molLength_reactionRight, molLength_reactionProduct] using reaction_length_add r)
  unfold ligationNonfoodMassGain
  linarith

/-- Cleavage has no positive nonfood-mass increment; catalyst copies cancel
from the net stoichiometric increment in both directions. -/
theorem cleavageNonfoodMassGain_nonpos {n : ℕ} (r : Reaction n) :
    -ligationNonfoodMassGain r ≤ 0 := neg_nonpos.mpr (ligationNonfoodMassGain_bounds r).1

def literalFoodUptakeIntensity {n : ℕ} (c : SourceMoleculeFibreConfig n)
    (N : Molecule n → ℕ) (rate : Reaction n → Molecule n → ℝ) (V : ℝ) : ℝ :=
  literalFoodUptakeNumerator c N rate / V^2

/-- State-uniform molecular-count intensity bound, with explicit cubic-channel
volume normalization. No assumption on the subsequent population trajectory. -/
theorem literalFoodUptakeIntensity_mass_bound {n k : ℕ} (c : SourceMoleculeFibreConfig n)
    (hgood : ¬ ShortIncidence k c) (N : Molecule n → ℕ)
    (rate : Reaction n → Molecule n → ℝ) (κ V : ℝ)
    (hκ : 0 ≤ κ) (hV : 0 < V) (hrate : ∀ r z, rate r z ≤ κ) :
    (k : ℝ) * literalFoodUptakeIntensity c N rate V ≤
      4 * κ * V * (polymerMass (fun z => (N z : ℝ)) / V)^3 := by
  have hm := literalFoodUptakeNumerator_mass_bound c hgood N rate κ hκ hrate
  unfold literalFoodUptakeIntensity
  calc
    _ = ((k : ℝ) * literalFoodUptakeNumerator c N rate) / V^2 := by ring
    _ ≤ (4 * κ * (polymerMass (fun z => (N z : ℝ)))^3) / V^2 :=
      div_le_div_of_nonneg_right hm (sq_nonneg V)
    _ = _ := by field_simp

end
end RandomViability
