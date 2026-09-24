import proofs.RandomViability.BoundedRewardIdentity
import proofs.RandomViability.UnboundedPhysicalStep

set_option Elab.async false
namespace RandomViability
open Classical RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 20000

/-- Removing a fixed food-length credit from one product coordinate. -/
def singleIncidenceWeight {n : ℕ} (p : Molecule n) (a : ℝ) (q : Molecule n) : ℝ :=
  (molLength q : ℝ) - foodMassWeight q - if q = p then a else 0

theorem singleIncidence_product_distinct {n : ℕ} (r : Reaction n) :
    reactionLeft r ≠ reactionProduct r ∧ reactionRight r ≠ reactionProduct r := by
  have hlen : molLength (reactionLeft r) + molLength (reactionRight r) =
      molLength (reactionProduct r) := by
    simpa only [molLength_reactionLeft, molLength_reactionRight, molLength_reactionProduct]
      using reaction_length_add r
  have hl : 1 ≤ molLength (reactionLeft r) := by simp [molLength]
  have hr : 1 ≤ molLength (reactionRight r) := by simp [molLength]
  constructor <;> intro h <;> have he := congrArg molLength h <;> omega

/-- The credit equal to the food mass gain cancels either reaction direction. -/
theorem singleIncidence_weight_balance {n : ℕ} (r : Reaction n) :
    singleIncidenceWeight (reactionProduct r) (ligationNonfoodMassGain r) (reactionProduct r) =
      singleIncidenceWeight (reactionProduct r) (ligationNonfoodMassGain r) (reactionLeft r) +
      singleIncidenceWeight (reactionProduct r) (ligationNonfoodMassGain r) (reactionRight r) := by
  obtain ⟨hl, hr⟩ := singleIncidence_product_distinct r
  have hlen : (molLength (reactionLeft r) : ℝ) + molLength (reactionRight r) =
      molLength (reactionProduct r) := by
    exact_mod_cast (show molLength (reactionLeft r) + molLength (reactionRight r) =
      molLength (reactionProduct r) by
      simpa only [molLength_reactionLeft, molLength_reactionRight, molLength_reactionProduct]
        using reaction_length_add r)
  simp only [singleIncidenceWeight, hl, hr, ↓reduceIte, sub_zero, ligationNonfoodMassGain]
  linarith

/-- Literal count transitions: input multiplicities include the passive catalyst,
even when it equals a substrate or the product. No propensity approximation. -/
theorem singleIncidence_count_invariant {n : ℕ} (r : Reaction n) (z : Molecule n)
    (d : Bool) (N : Molecule n → ℕ) :
    weightedCountMass (singleIncidenceWeight (reactionProduct r) (ligationNonfoodMassGain r))
      (unboundedPhysicalNext N (.inr (.inr (r,z,d)))) =
    weightedCountMass (singleIncidenceWeight (reactionProduct r) (ligationNonfoodMassGain r)) N := by
  let w := singleIncidenceWeight (reactionProduct r) (ligationNonfoodMassGain r)
  change weightedCountMass w _ = weightedCountMass w N
  by_cases he : ∀ x, physicalChannelInput (.inr (.inr (r,z,d))) x ≤ N x
  · rw [unboundedPhysicalNext, if_pos he]
    apply sub_eq_zero.mp
    rw [weightedCountMass_change _ _ _ _ he]
    have hb : w (reactionProduct r) = w (reactionLeft r) + w (reactionRight r) :=
      singleIncidence_weight_balance r
    cases d <;>
      simp [weightedCountMass, physicalChannelInput, physicalChannelOutput,
        singleCount, Nat.cast_add, mul_add, Finset.sum_add_distrib, mul_ite] <;> linarith
  · simp [unboundedPhysicalNext, he]

theorem singleIncidence_weight_lower {n : ℕ} (p q : Molecule n) (a : ℝ)
    (ha : a ≤ 2) (hp : a + 3 ≤ (molLength p : ℝ)) :
    (3/5 : ℝ)*((molLength q : ℝ)-foodMassWeight q) ≤ singleIncidenceWeight p a q := by
  by_cases hq : q = p
  · subst q
    unfold singleIncidenceWeight foodMassWeight
    simp only [↓reduceIte]
    split_ifs with hfood
    · have hlen : (molLength p : ℝ) ≤ 2 := by exact_mod_cast hfood
      simp only [sub_self]
      linarith
    · simp only [sub_zero]
      linarith
  · simp only [singleIncidenceWeight, hq, ↓reduceIte, sub_zero]
    have hn : 0 ≤ (molLength q : ℝ)-foodMassWeight q := by
      unfold foodMassWeight
      split_ifs <;> simp
    linarith

/-- The comparison applies to arbitrary nonnegative counts, hence also the
weighted cumulative washout vector on any chosen time interval. -/
theorem singleIncidence_count_lower {n : ℕ} (p : Molecule n) (a : ℝ)
    (ha : a ≤ 2) (hp : a+3 ≤ (molLength p : ℝ)) (N : Molecule n → ℕ) :
    (3/5 : ℝ)*countNonfoodMass N ≤ weightedCountMass (singleIncidenceWeight p a) N := by
  unfold countNonfoodMass weightedCountMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro q _
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
    (singleIncidence_weight_lower p q a ha hp) (Nat.cast_nonneg (N q))

theorem singleIncidence_count_eq {n : ℕ} (p : Molecule n) (a : ℝ)
    (N : Molecule n → ℕ) :
    weightedCountMass (singleIncidenceWeight p a) N = countNonfoodMass N-a*(N p : ℝ) := by
  simp [weightedCountMass, singleIncidenceWeight, countNonfoodMass, sub_mul,
    Finset.sum_sub_distrib, ite_mul]

theorem mixed_incidence_weight_parameters {n : ℕ} (r : Reaction n)
    (h : (molLength (reactionLeft r) ≤ 2 ∧ 2 < molLength (reactionRight r)) ∨
      (2 < molLength (reactionLeft r) ∧ molLength (reactionRight r) ≤ 2)) :
    ligationNonfoodMassGain r ≤ 2 ∧
      ligationNonfoodMassGain r+3 ≤ (molLength (reactionProduct r) : ℝ) := by
  have hlen : molLength (reactionLeft r)+molLength (reactionRight r) =
      molLength (reactionProduct r) := by
    simpa only [molLength_reactionLeft, molLength_reactionRight, molLength_reactionProduct]
      using reaction_length_add r
  have hlenR : (molLength (reactionLeft r) : ℝ)+molLength (reactionRight r) =
      molLength (reactionProduct r) := by exact_mod_cast hlen
  rcases h with ⟨hl,hr⟩ | ⟨hl,hr⟩
  · have hp : ¬molLength (reactionProduct r) ≤ 2 := by omega
    have hrl : (3 : ℝ) ≤ molLength (reactionRight r) := by exact_mod_cast hr
    have hll : (molLength (reactionLeft r) : ℝ) ≤ 2 := by exact_mod_cast hl
    simp only [ligationNonfoodMassGain, foodMassWeight, hl, not_le.mpr hr, hp,
      ↓reduceIte, add_zero, sub_zero]
    exact ⟨hll, by linarith⟩
  · have hp : ¬molLength (reactionProduct r) ≤ 2 := by omega
    have hll : (3 : ℝ) ≤ molLength (reactionLeft r) := by exact_mod_cast hl
    have hrl : (molLength (reactionRight r) : ℝ) ≤ 2 := by exact_mod_cast hr
    simp only [ligationNonfoodMassGain, foodMassWeight, hr, not_le.mpr hl, hp,
      ↓reduceIte, zero_add, sub_zero]
    exact ⟨hrl, by linarith⟩

/-- Uniform in the literal catalogue and all input counts; applying this to
washout counts gives the required physical export comparison. -/
theorem mixed_incidence_count_lower {n : ℕ} (r : Reaction n)
    (h : (molLength (reactionLeft r) ≤ 2 ∧ 2 < molLength (reactionRight r)) ∨
      (2 < molLength (reactionLeft r) ∧ molLength (reactionRight r) ≤ 2))
    (N : Molecule n → ℕ) :
    (3/5 : ℝ)*countNonfoodMass N ≤
      weightedCountMass (singleIncidenceWeight (reactionProduct r) (ligationNonfoodMassGain r)) N := by
  have hp := mixed_incidence_weight_parameters r h
  exact singleIncidence_count_lower _ _ hp.1 hp.2 N

end
end RandomViability
