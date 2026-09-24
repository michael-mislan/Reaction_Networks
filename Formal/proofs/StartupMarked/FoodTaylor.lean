import proofs.StartupMarked.RetainedReward
import proofs.StartupMarked.CatalogRate

namespace StartupMarked
open Classical RandomViability RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 50000

theorem food_deficit_taylor (u v : ℝ) :
    (foodDeficit v)^2-(foodDeficit u)^2+2*foodDeficit u*(v-u) ≤ (v-u)^2 := by
  by_cases hu : u ≤ 1
  · rw [show foodDeficit u = 1-u from max_eq_left (by linarith)]
    by_cases hv : v ≤ 1
    · rw [show foodDeficit v = 1-v from max_eq_left (by linarith)]
      nlinarith
    · rw [show foodDeficit v = 0 from max_eq_right (by linarith)]
      nlinarith [sq_nonneg (v-1)]
  · rw [show foodDeficit u = 0 from max_eq_right (by linarith)]
    by_cases hv : v ≤ 1
    · rw [show foodDeficit v = 1-v from max_eq_left (by linarith)]
      nlinarith [mul_nonneg (show 0 ≤ u-1 by linarith) (show 0 ≤ u+1-2*v by linarith)]
    · rw [show foodDeficit v = 0 from max_eq_right (by linarith)]
      nlinarith [sq_nonneg (v-u)]

theorem food_penalty_taylor {n : ℕ} (V : NNReal) (r : Reaction n)
    (N M : Molecule n → ℕ) :
    -(foodPenalty V r M-foodPenalty V r N) ≥
      8*foodDeficit ((N (reactionLeft r) : ℝ)/V)*
        (((M (reactionLeft r) : ℝ)/V)-((N (reactionLeft r) : ℝ)/V))+
      8*foodDeficit ((N (reactionRight r) : ℝ)/V)*
        (((M (reactionRight r) : ℝ)/V)-((N (reactionRight r) : ℝ)/V))-
      4*((((M (reactionLeft r) : ℝ)/V)-((N (reactionLeft r) : ℝ)/V))^2+
         (((M (reactionRight r) : ℝ)/V)-((N (reactionRight r) : ℝ)/V))^2) := by
  have hu := food_deficit_taylor ((N (reactionLeft r) : ℝ)/V) ((M (reactionLeft r) : ℝ)/V)
  have hw := food_deficit_taylor ((N (reactionRight r) : ℝ)/V) ((M (reactionRight r) : ℝ)/V)
  unfold foodPenalty
  linarith only [hu,hw]

theorem normalized_coordinate_square {n : ℕ} (V : NNReal)
    (N : Molecule n → ℕ) (q : Molecule n) (ch : PhysicalCountChannel n) :
    (((unboundedPhysicalNext N ch q : ℝ)/V)-((N q : ℝ)/V))^2 ≤ 4/(V : ℝ)^2 := by
  rw [← sub_div,div_pow]
  exact div_le_div_of_nonneg_right (unbounded_coordinate_jump_sq N q ch) (sq_nonneg _)

theorem food_penalty_generator {n : ℕ} (hn : 2 ≤ n) (cfg : SourceMoleculeFibreConfig n)
    (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ) (r : Reaction n)
    (hb : ∀ r,(basal r : ℝ) ≤ 1) (hc : ∀ r z,(cat r z : ℝ) ≤ 16)
    (hM : (countMass N : ℝ) ≤ 11*V) :
    8*foodDeficit ((N (reactionLeft r) : ℝ)/V)*physicalCoordinateDrift cfg V basal cat N (reactionLeft r)+
    8*foodDeficit ((N (reactionRight r) : ℝ)/V)*physicalCoordinateDrift cfg V basal cat N (reactionRight r)-
      3072000/(V : ℝ) ≤
      ∑ ch,unboundedPhysicalRate cfg V 1 basal cat N ch*
        (-(foodPenalty V r (unboundedPhysicalNext N ch)-foodPenalty V r N)) := by
  let R := unboundedPhysicalRate cfg V 1 basal cat N
  let du := coordinateConcentrationJump V (reactionLeft r) N
  let dw := coordinateConcentrationJump V (reactionRight r) N
  let fu := foodDeficit ((N (reactionLeft r) : ℝ)/V)
  let fw := foodDeficit ((N (reactionRight r) : ℝ)/V)
  have hR : (∑ ch,R ch) ≤ 96000*V := by
    have hh := unbounded_total_rate_mass_eleven hn cfg V hV basal cat N hM hb hc
    dsimp [R]
    linarith
  have hquad (ch : PhysicalCountChannel n) : (du ch)^2+(dw ch)^2 ≤ 8/(V : ℝ)^2 := by
    have hu := normalized_coordinate_square V N (reactionLeft r) ch
    have hw := normalized_coordinate_square V N (reactionRight r) ch
    dsimp [du,dw,coordinateConcentrationJump]
    simp only [← sub_div] at hu hw
    exact (add_le_add hu hw).trans_eq (by ring)
  have hsum : (∑ ch,R ch*((du ch)^2+(dw ch)^2)) ≤ 768000/(V : ℝ) := by
    calc
      _ ≤ ∑ ch,R ch*(8/(V : ℝ)^2) := Finset.sum_le_sum (fun ch _ =>
        mul_le_mul_of_nonneg_left (hquad ch) (unboundedPhysicalRate_nonneg cfg V 1 basal cat N ch))
      _ = (∑ ch,R ch)*(8/(V : ℝ)^2) := (Finset.sum_mul ..).symm
      _ ≤ (96000*V)*(8/(V : ℝ)^2) := mul_le_mul_of_nonneg_right hR (by positivity)
      _ = _ := by field_simp; ring
  have hp (ch : PhysicalCountChannel n) :
      8*fu*du ch+8*fw*dw ch-4*((du ch)^2+(dw ch)^2) ≤
      -(foodPenalty V r (unboundedPhysicalNext N ch)-foodPenalty V r N) := by
    simpa only [fu,fw,du,dw,coordinateConcentrationJump,sub_div] using
      food_penalty_taylor V r N (unboundedPhysicalNext N ch)
  have hsumP := Finset.sum_le_sum (fun ch (_ : ch ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (hp ch) (unboundedPhysicalRate_nonneg cfg V 1 basal cat N ch))
  have he : (∑ ch,R ch*(8*fu*du ch+8*fw*dw ch-4*((du ch)^2+(dw ch)^2))) =
      8*fu*(∑ ch,R ch*du ch)+8*fw*(∑ ch,R ch*dw ch)-4*(∑ ch,R ch*((du ch)^2+(dw ch)^2)) := by
    simp only [Finset.mul_sum,← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro ch _
    ring
  change (∑ ch,R ch*(8*fu*du ch+8*fw*dw ch-4*((du ch)^2+(dw ch)^2))) ≤ _ at hsumP
  rw [he] at hsumP
  change 8*fu*(∑ ch,R ch*du ch)+8*fw*(∑ ch,R ch*dw ch)-3072000/(V : ℝ) ≤ _
  have herr : 4*(∑ ch,R ch*((du ch)^2+(dw ch)^2)) ≤ 3072000/(V : ℝ) :=
    (mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 4)).trans_eq (by ring)
  exact (sub_le_sub le_rfl herr).trans hsumP

end
end StartupMarked
