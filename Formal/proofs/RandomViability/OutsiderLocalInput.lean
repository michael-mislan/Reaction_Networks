import proofs.RandomViability.NonfoodTargetCreation
import proofs.RandomViability.ShortTargetTailLoss
import proofs.RandomViability.MarkedCatalyticInput

set_option Elab.async false
namespace RandomViability
open Classical RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 60000

theorem food_pair_nonfood_mass_bound {n : ℕ} (u v : Molecule n)
    (hu : molLength u ≤ 2) (hv : molLength v ≤ 2) (hp : 2 < molLength u+molLength v)
    (x : Molecule n → ℝ) (hx : ∀ q,0 ≤ x q) : 4*x u*x v ≤ (polymerMass x)^2 := by
  by_cases he : u = v
  · subst v
    have hlen : molLength u = 2 := by omega
    have hm := coordinate_mass_le x hx u
    rw [hlen] at hm
    norm_num at hm
    have hs := pow_le_pow_left₀ (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (hx u)) hm 2
    nlinarith only [hs]
  · have hsum : (∑ q ∈ ({u,v} : Finset (Molecule n)),x q) ≤ ∑ q,x q :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun q _ _ => hx q)
    simp only [Finset.sum_pair he] at hsum
    have hm := hsum.trans (concentration_le_mass x hx)
    have hs := pow_le_pow_left₀ (add_nonneg (hx u) (hx v)) hm 2
    nlinarith only [hs,sq_nonneg (x u-x v)]

theorem positive_catalytic_reward_reverse {n : ℕ} (V : NNReal) (N : Molecule n → ℕ)
    (r : Reaction n) (z : Molecule n) :
    normalizedPositiveCatalyticReward V N (.inr (.inr (r,z,false))) = 0 := by
  have hg := (ligation_nonfood_gain_le_four r).1
  unfold normalizedPositiveCatalyticReward
  by_cases he : ∀ x,physicalChannelInput (.inr (.inr (r,z,false))) x ≤ N x
  · rw [unboundedPhysicalNext,if_pos he,catalytic_nonfood_raw_change N r z false he]
    simp only [Bool.false_eq_true,if_false]
    rw [max_eq_left (by linarith),zero_div]
  · simp [unboundedPhysicalNext,he]

/-- The literal local input is absorbed by a 2000-weight outsider dilution.
This bound includes equal food substrates and full falling-factorial rates. -/
theorem local_food_nonfood_input_le {n : ℕ} (c : SourceMoleculeFibreConfig n)
    (V : NNReal) (hV : 0 < (V : ℝ)) (basal : Reaction n → NNReal)
    (cat : Reaction n → Molecule n → NNReal) (r : Reaction n) (z : Molecule n)
    (hl : molLength (reactionLeft r) ≤ 2) (hr : molLength (reactionRight r) ≤ 2)
    (hp : 2 < molLength (reactionProduct r)) (hcat : (cat r z : ℝ) ≤ 16)
    (N : Molecule n → ℕ) (hM : (countMass N : ℝ) ≤ 11*V) :
    (∑ d : Bool,unboundedPhysicalRate c V 1 basal cat N (.inr (.inr (r,z,d)))*
      normalizedPositiveCatalyticReward V N (.inr (.inr (r,z,d)))) ≤ 1936*((N z : ℝ)/V) := by
  simp only [Fintype.sum_bool,positive_catalytic_reward_reverse,mul_zero,add_zero]
  let x : Molecule n → ℝ := fun q => (N q : ℝ)/V
  have hx : ∀ q,0 ≤ x q := fun q => by dsimp [x]; positivity
  have hL : polymerMass x ≤ 11 := by
    rw [normalized_count_mass]
    exact (div_le_iff₀ hV).2 hM
  have hL0 : 0 ≤ polymerMass x := Finset.sum_nonneg (fun q _ => mul_nonneg (Nat.cast_nonneg _) (hx q))
  have hprod : 2 < molLength (reactionLeft r)+molLength (reactionRight r) := by
    have he : molLength (reactionLeft r)+molLength (reactionRight r) = molLength (reactionProduct r) := by
      simpa only [molLength_reactionLeft,molLength_reactionRight,molLength_reactionProduct] using reaction_length_add r
    omega
  have hpair := food_pair_nonfood_mass_bound (reactionLeft r) (reactionRight r) hl hr hprod x hx
  have hL2 := pow_le_pow_left₀ hL0 hL 2
  have hpx : 4*x (reactionLeft r)*x (reactionRight r) ≤ 121 := by nlinarith only [hpair,hL2]
  have hpz := mul_le_mul_of_nonneg_right hpx (hx z)
  calc
    _ ≤ unboundedPhysicalRate c V 1 basal cat N (.inr (.inr (r,z,true)))*(4/V) :=
      mul_le_mul_of_nonneg_left (positive_catalytic_reward_bounds V hV N _).2
        (unboundedPhysicalRate_nonneg c V 1 basal cat N _)
    _ ≤ (16*((N (reactionLeft r) : ℝ)*N (reactionRight r)*N z)/(V : ℝ)^2)*(4/V) :=
      mul_le_mul_of_nonneg_right
        (unbounded_catalytic_ligation_rate_le c V 1 hV basal cat N r z 16 (by norm_num) hcat) (by positivity)
    _ = 64*x (reactionLeft r)*x (reactionRight r)*x z := by dsimp [x]; field_simp; ring
    _ ≤ _ := by change _ ≤ 1936*x z; nlinarith only [hpz]

end
end RandomViability
