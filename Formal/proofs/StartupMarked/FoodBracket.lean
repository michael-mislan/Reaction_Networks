import proofs.StartupMarked.FoodTaylor
import proofs.StartupMarked.LogBracket

namespace StartupMarked
open Classical RandomViability RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 50000

theorem food_deficit_lipschitz (u v : ℝ) : |foodDeficit v-foodDeficit u| ≤ |v-u| := by
  have hh := abs_max_sub_max_le_abs (1-v) (1-u) (0 : ℝ)
  have he : (1-v)-(1-u) = -(v-u) := by ring
  simpa only [foodDeficit,he,abs_neg] using hh

theorem squared_food_deficit_lipschitz (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    |(foodDeficit v)^2-(foodDeficit u)^2| ≤ 2*|v-u| := by
  have hsum0 := add_nonneg (foodDeficit_nonneg v) (foodDeficit_nonneg u)
  have hsum : foodDeficit v+foodDeficit u ≤ 2 := by
    linarith [foodDeficit_le_one u hu,foodDeficit_le_one v hv]
  calc
    _ = |(foodDeficit v-foodDeficit u)*(foodDeficit v+foodDeficit u)| := by congr 1; ring
    _ = |foodDeficit v-foodDeficit u| *(foodDeficit v+foodDeficit u) := by
      rw [abs_mul,abs_of_nonneg hsum0]
    _ ≤ |v-u| *(foodDeficit v+foodDeficit u) :=
      mul_le_mul_of_nonneg_right (food_deficit_lipschitz u v) hsum0
    _ ≤ |v-u| *2 := mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
    _ = _ := mul_comm _ _

theorem normalized_coordinate_abs {n : ℕ} (V : NNReal) (hV : 0 < (V : ℝ))
    (N : Molecule n → ℕ) (q : Molecule n) (ch : PhysicalCountChannel n) :
    |((unboundedPhysicalNext N ch q : ℝ)/V)-((N q : ℝ)/V)| ≤ 2/(V : ℝ) := by
  have hs := unbounded_coordinate_jump_sq N q ch
  have hh : |(unboundedPhysicalNext N ch q : ℝ)-(N q : ℝ)| ≤ 2 := by
    apply abs_le.mpr
    constructor <;> nlinarith only [hs]
  rw [← sub_div,abs_div,abs_of_pos hV]
  exact div_le_div_of_nonneg_right hh hV.le

theorem food_penalty_jump_abs {n : ℕ} (V : NNReal) (hV : 0 < (V : ℝ))
    (r : Reaction n) (N : Molecule n → ℕ) (ch : PhysicalCountChannel n) :
    |foodPenalty V r (unboundedPhysicalNext N ch)-foodPenalty V r N| ≤ 32/(V : ℝ) := by
  let M := unboundedPhysicalNext N ch
  have hu := squared_food_deficit_lipschitz ((N (reactionLeft r) : ℝ)/V)
    ((M (reactionLeft r) : ℝ)/V) (by positivity) (by positivity)
  have hw := squared_food_deficit_lipschitz ((N (reactionRight r) : ℝ)/V)
    ((M (reactionRight r) : ℝ)/V) (by positivity) (by positivity)
  have hdu := normalized_coordinate_abs V hV N (reactionLeft r) ch
  have hdw := normalized_coordinate_abs V hV N (reactionRight r) ch
  have he : foodPenalty V r M-foodPenalty V r N =
      4*(((foodDeficit ((M (reactionLeft r) : ℝ)/V))^2-(foodDeficit ((N (reactionLeft r) : ℝ)/V))^2)+
        ((foodDeficit ((M (reactionRight r) : ℝ)/V))^2-(foodDeficit ((N (reactionRight r) : ℝ)/V))^2)) := by
    unfold foodPenalty
    ring
  change |foodPenalty V r M-foodPenalty V r N| ≤ _
  rw [he,abs_mul,abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  have ht := abs_add_le
    ((foodDeficit ((M (reactionLeft r) : ℝ)/V))^2-(foodDeficit ((N (reactionLeft r) : ℝ)/V))^2)
    ((foodDeficit ((M (reactionRight r) : ℝ)/V))^2-(foodDeficit ((N (reactionRight r) : ℝ)/V))^2)
  change |((M (reactionLeft r) : ℝ)/V)-((N (reactionLeft r) : ℝ)/V)| ≤ _ at hdu
  change |((M (reactionRight r) : ℝ)/V)-((N (reactionRight r) : ℝ)/V)| ≤ _ at hdw
  have hu' := hu.trans (mul_le_mul_of_nonneg_left hdu (by norm_num : (0 : ℝ) ≤ 2))
  have hw' := hw.trans (mul_le_mul_of_nonneg_left hdw (by norm_num : (0 : ℝ) ≤ 2))
  exact (mul_le_mul_of_nonneg_left (ht.trans (add_le_add hu' hw'))
    (by norm_num : (0 : ℝ) ≤ 4)).trans_eq (by ring)

end
end StartupMarked
