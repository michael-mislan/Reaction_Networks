import proofs.RandomViability.BoundedMoment
import proofs.RandomViability.LiteralUptake
import proofs.RandomViability.BoundedRewardIdentity

namespace RandomViability
open Classical RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section

/-- Falling factorials make the upper bound valid even when input identities
coincide; no distinctness hypothesis is used. -/
theorem catalytic_factorial_product_le {n : ℕ} (N : Molecule n → ℕ) (u w z : Molecule n) :
    (∏ x, ((N x).descFactorial (singleCount u x + singleCount w x + singleCount z x) : ℝ)) ≤
      (N u : ℝ) * N w * N z := by
  calc
    _ ≤ ∏ x, (N x : ℝ)^(singleCount u x + singleCount w x + singleCount z x) := by
      apply Finset.prod_le_prod
      · intro x _
        positivity
      · intro x _
        exact_mod_cast Nat.descFactorial_le_pow (N x) _
    _ = _ := by
      simp only [pow_add, Finset.prod_mul_distrib]
      simp [singleCount, apply_ite]

theorem catalytic_input_count {n : ℕ} (r : Reaction n) (z : Molecule n) :
    (∑ x, physicalChannelInput (.inr (.inr (r,z,true))) x) = 3 := by
  simp [physicalChannelInput, Finset.sum_add_distrib, singleCount]

theorem bounded_catalytic_ligation_rate_le {n B : ℕ}
    (c : SourceMoleculeFibreConfig n) (V D : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (catalytic : Reaction n → Molecule n → NNReal)
    (N : BoundedCounts n B) (r : Reaction n) (z : Molecule n) :
    (boundedPhysicalCountModel c V D basal catalytic).rate N (.inr (.inr (r,z,true))) ≤
      if r ∈ c z then (catalytic r z : ℝ) *
        ((boundedCountsValue N (reactionLeft r) : ℝ) * boundedCountsValue N (reactionRight r) *
          boundedCountsValue N z) / (V : ℝ)^2 else 0 := by
  change (if ∀ x, physicalChannelInput (.inr (.inr (r,z,true))) x ≤ boundedCountsValue N x then
    physicalChannelRate c V D basal catalytic (boundedCountsValue N) (.inr (.inr (r,z,true))) else 0) ≤ _
  split_ifs with he hs hs
  · unfold physicalChannelRate
    rw [catalytic_input_count]
    simp only [physicalChannelCoefficient, if_pos hs, physicalChannelInput, if_true]
    have hb := catalytic_factorial_product_le (boundedCountsValue N) (reactionLeft r) (reactionRight r) z
    calc
      _ ≤ ((catalytic r z : ℝ)*V)*
          ((boundedCountsValue N (reactionLeft r) : ℝ)*boundedCountsValue N (reactionRight r)*boundedCountsValue N z) /
          (V : ℝ)^3 := div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hb (by positivity)) (by positivity)
      _ = _ := by field_simp
  · simp [physicalChannelRate, physicalChannelCoefficient, hs]
  · positivity
  · exact le_rfl

/-- Intensity of stoichiometric nonfood-mass gain from catalytic ligations,
using the actual finite reactor rates. Cleavage has nonpositive gain. -/
def boundedCatalyticUptake {n B : ℕ} (c : SourceMoleculeFibreConfig n) (V D : NNReal)
    (basal : Reaction n → NNReal) (catalytic : Reaction n → Molecule n → NNReal)
    (N : BoundedCounts n B) : ℝ :=
  ∑ z, ∑ r, ligationNonfoodMassGain r *
    (boundedPhysicalCountModel c V D basal catalytic).rate N (.inr (.inr (r,z,true)))

theorem boundedCatalyticUptake_le_envelope {n B : ℕ}
    (c : SourceMoleculeFibreConfig n) (V D : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (catalytic : Reaction n → Molecule n → NNReal)
    (N : BoundedCounts n B) (κ : ℝ) (hκ : 0 ≤ κ)
    (hrate : ∀ r z, (catalytic r z : ℝ) ≤ κ) :
    boundedCatalyticUptake c V D basal catalytic N ≤
      κ * catalyticFoodEnvelope c (fun z => (boundedCountsValue N z : ℝ)) / (V : ℝ)^2 := by
  unfold boundedCatalyticUptake catalyticFoodEnvelope
  simp only [Finset.sum_div, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro z _
  apply Finset.sum_le_sum
  intro r _
  have hg := ligationNonfoodMassGain_bounds r
  have hb := bounded_catalytic_ligation_rate_le c V D hV basal catalytic N r z
  by_cases hs : r ∈ c z
  · rw [if_pos hs] at hb ⊢
    calc
      _ ≤ ligationNonfoodMassGain r * ((catalytic r z : ℝ) *
          ((boundedCountsValue N (reactionLeft r) : ℝ)*boundedCountsValue N (reactionRight r)*boundedCountsValue N z) /
          (V : ℝ)^2) := mul_le_mul_of_nonneg_left hb hg.1
      _ ≤ ligationNonfoodMassGain r * (κ *
          ((boundedCountsValue N (reactionLeft r) : ℝ)*boundedCountsValue N (reactionRight r)*boundedCountsValue N z) /
          (V : ℝ)^2) := mul_le_mul_of_nonneg_left
            (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hrate r z) (by positivity)) (by positivity)) hg.1
      _ ≤ (foodMassWeight (reactionLeft r)+foodMassWeight (reactionRight r)) * (κ *
          ((boundedCountsValue N (reactionLeft r) : ℝ)*boundedCountsValue N (reactionRight r)*boundedCountsValue N z) /
          (V : ℝ)^2) := mul_le_mul_of_nonneg_right hg.2 (by positivity)
      _ = _ := by ring
  · rw [if_neg hs] at hb ⊢
    simpa only [mul_zero, zero_div] using mul_nonpos_of_nonneg_of_nonpos hg.1 hb

theorem boundedCatalyticUptake_mass_bound {n B k : ℕ}
    (c : SourceMoleculeFibreConfig n) (hgood : ¬ ShortIncidence k c)
    (V D : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (catalytic : Reaction n → Molecule n → NNReal)
    (N : BoundedCounts n B) (κ : ℝ) (hκ : 0 ≤ κ)
    (hrate : ∀ r z, (catalytic r z : ℝ) ≤ κ) :
    (k : ℝ) * boundedCatalyticUptake c V D basal catalytic N ≤
      4*κ*V*((boundedMass N : ℝ)/V)^3 := by
  have he := boundedCatalyticUptake_le_envelope c V D hV basal catalytic N κ hκ hrate
  have hm := catalyticFoodEnvelope_mass_bound c hgood
    (fun z => (boundedCountsValue N z : ℝ)) (fun z => Nat.cast_nonneg _)
  have hmass : polymerMass (fun z => (boundedCountsValue N z : ℝ)) = (boundedMass N : ℝ) := by
    unfold polymerMass boundedMass countMass
    push_cast
    rfl
  rw [hmass] at hm
  calc
    _ ≤ (k : ℝ) * (κ * catalyticFoodEnvelope c (fun z => (boundedCountsValue N z : ℝ)) / (V : ℝ)^2) :=
      mul_le_mul_of_nonneg_left he (Nat.cast_nonneg _)
    _ = κ * ((k : ℝ)*catalyticFoodEnvelope c (fun z => (boundedCountsValue N z : ℝ))) / (V : ℝ)^2 := by ring
    _ ≤ κ*(4*(boundedMass N : ℝ)^3)/(V : ℝ)^2 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hm hκ) (by positivity)
    _ = _ := by field_simp

theorem boundedCatalyticUptake_eq_actual_positive {n B : ℕ}
    (c : SourceMoleculeFibreConfig n) (V D : NNReal)
    (basal : Reaction n → NNReal) (catalytic : Reaction n → Molecule n → NNReal)
    (N : BoundedCounts n B) :
    boundedCatalyticUptake c V D basal catalytic N =
      ∑ z, ∑ r, ∑ d : Bool,
        (boundedPhysicalCountModel c V D basal catalytic).rate N (.inr (.inr (r,z,d))) *
          max 0 (countNonfoodMass (boundedCountsValue
            ((boundedPhysicalCountModel c V D basal catalytic).next N (.inr (.inr (r,z,d))))) -
              countNonfoodMass (boundedCountsValue N)) := by
  simp_rw [bounded_catalytic_positive_reward]
  simp [boundedCatalyticUptake]

theorem bounded_actual_positive_mass_bound {n B k : ℕ}
    (c : SourceMoleculeFibreConfig n) (hgood : ¬ ShortIncidence k c)
    (V D : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (catalytic : Reaction n → Molecule n → NNReal)
    (N : BoundedCounts n B) (κ : ℝ) (hκ : 0 ≤ κ)
    (hrate : ∀ r z, (catalytic r z : ℝ) ≤ κ) :
    (k : ℝ) * (∑ z, ∑ r, ∑ d : Bool,
      (boundedPhysicalCountModel c V D basal catalytic).rate N (.inr (.inr (r,z,d))) *
        max 0 (countNonfoodMass (boundedCountsValue
          ((boundedPhysicalCountModel c V D basal catalytic).next N (.inr (.inr (r,z,d))))) -
            countNonfoodMass (boundedCountsValue N))) ≤
      4*κ*V*((boundedMass N : ℝ)/V)^3 := by
  rw [← boundedCatalyticUptake_eq_actual_positive]
  exact boundedCatalyticUptake_mass_bound c hgood V D hV basal catalytic N κ hκ hrate

end
end RandomViability


