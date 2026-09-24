import proofs.RandomViability.OutsiderLocalInput
import proofs.RandomViability.IncidenceRewardErasure
import proofs.RandomViability.PhysicalCoordinateUpper
import proofs.RandomViability.SingleIncidenceRewardNoise

set_option Elab.async false
namespace RandomViability
open Classical RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 80000

def outsiderSignedReward {n : ℕ} (z : Molecule n) (V : NNReal)
    (N : Molecule n → ℕ) (ch : PhysicalCountChannel n) : ℝ :=
  (positiveBasalReward V N ch+normalizedPositiveCatalyticReward V N ch+
    2000*coordinateConcentrationJump V z N ch)/1001

theorem outsider_signed_reward_bound {n : ℕ} (z : Molecule n) (V : NNReal)
    (hV : 0 < (V : ℝ)) (N : Molecule n → ℕ) (ch : PhysicalCountChannel n) :
    |outsiderSignedReward z V N ch| ≤ 4/V := by
  have hB := positive_basal_reward_bounds V hV N ch
  have hC := positive_catalytic_reward_bounds V hV N ch
  have hsum : |positiveBasalReward V N ch+normalizedPositiveCatalyticReward V N ch| ≤ 4/V := by
    rw [abs_of_nonneg (add_nonneg hB.1 hC.1)]
    rcases ch with e | (b | c)
    · simp only [positiveBasalReward,normalizedPositiveCatalyticReward,zero_add]; positivity
    · simpa only [normalizedPositiveCatalyticReward,add_zero] using hB.2
    · simpa only [positiveBasalReward,zero_add] using hC.2
  have hraw := unbounded_coordinate_jump_sq N z ch
  have habs : |(unboundedPhysicalNext N ch z : ℝ)-(N z : ℝ)| ≤ 2 := by
    rw [abs_le]
    constructor <;> nlinarith only [hraw]
  have hcoord : |coordinateConcentrationJump V z N ch| ≤ 2/V := by
    unfold coordinateConcentrationJump
    rw [abs_div,abs_of_pos hV]
    exact div_le_div_of_nonneg_right habs hV.le
  unfold outsiderSignedReward
  rw [abs_div]
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 1001)]
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 1001)).2
  have hh := abs_add_le (positiveBasalReward V N ch+normalizedPositiveCatalyticReward V N ch)
    (2000*coordinateConcentrationJump V z N ch)
  rw [abs_mul] at hh
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 2000)] at hh
  calc
    _ ≤ _ := hh
    _ ≤ 4/(V : ℝ)+2000*(2/V) := add_le_add hsum (mul_le_mul_of_nonneg_left hcoord (by norm_num))
    _ = _ := by ring

theorem outsider_signed_reward_drift {n : ℕ} (c : SourceMoleculeFibreConfig n)
    (z : Molecule n) (V : NNReal) (basal : Reaction n → NNReal)
    (cat : Reaction n → Molecule n → NNReal) (N : Molecule n → ℕ) :
    markedRewardDrift c V basal cat (outsiderSignedReward z V) N =
      (markedRewardDrift c V basal cat (positiveBasalReward V) N+
        markedRewardDrift c V basal cat (normalizedPositiveCatalyticReward V) N+
        2000*physicalCoordinateDrift c V basal cat N z)/1001 := by
  unfold markedRewardDrift outsiderSignedReward physicalCoordinateDrift
  rw [Finset.mul_sum,← Finset.sum_add_distrib,← Finset.sum_add_distrib,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro ch _
  ring

theorem isolated_outsider_signed_drift_bound {n : ℕ} (c : SourceMoleculeFibreConfig n)
    (z : Molecule n) (r : Reaction n) (hiso : SingleLocalIncidence singleIncidenceCutoff c z r)
    (hout : OutsiderFoodIncidence r z) (hsmall : molLength z ≤ singleIncidenceCutoff+2)
    (V : NNReal) (hV : 0 < (V : ℝ)) (basal : Reaction n → NNReal)
    (cat : Reaction n → Molecule n → NNReal)
    (hb : ∀ r,(basal r : ℝ) ≤ 4*(1/500000000 : ℝ))
    (hcat : ∀ r q,(cat r q : ℝ) ≤ 16)
    (N : Molecule n → ℕ) (hM : (countMass N : ℝ) ≤ 11*V) :
    markedRewardDrift c V basal cat (outsiderSignedReward z V) N ≤
      (37282993/46875000000 : ℝ)/1001 := by
  have hfree := erase_local_has_no_short_incidence c z r hiso
  have hB := positive_basal_reward_drift c V hV basal cat N (1/500000000) (by norm_num) hb hM
  have hC := positive_catalytic_drift_short_bound (eraseLocalIncidence c z r) hfree V hV basal cat N hM hcat
  have hlocal := local_food_nonfood_input_le c V hV basal cat r z hout.1 hout.2.1 hout.2.2.1 (hcat r z) N hM
  have hsplit := reward_drift_erase_identity c z r V basal cat (normalizedPositiveCatalyticReward V) N
  have hcoord := short_free_nonfood_coordinate_upper (eraseLocalIncidence c z r) hfree z
    hout.2.2.2.1 hsmall V hV basal cat hb hcat N hM
  rw [← outsider_coordinate_drift_erase c z r hout V basal cat N] at hcoord
  rw [outsider_signed_reward_drift]
  apply (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 1001)).2
  change markedRewardDrift c V basal cat (positiveBasalReward V) N ≤ _ at hB
  norm_num [singleIncidenceCutoff] at hC
  have hz0 : 0 ≤ (N z : ℝ)/V := by positivity
  linarith only [hB,hC,hlocal,hsplit,hcoord,hz0]

end
end RandomViability
