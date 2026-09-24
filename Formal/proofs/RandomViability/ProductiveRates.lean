import proofs.RandomViability.PhysicalTotalRate
import proofs.RandomViability.BasalSeedRate

namespace RandomViability
open Classical RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 30000

theorem catalytic_factorial_product_distinct {n : ℕ} (N : Molecule n → ℕ)
    (u w z : Molecule n) (huw : u ≠ w) (huz : u ≠ z) (hwz : w ≠ z) :
    (∏ y, ((N y).descFactorial (singleCount u y+singleCount w y+singleCount z y) : ℝ)) =
      (N u : ℝ)*N w*N z := by
  calc
    _ = ∏ y, (N y : ℝ)^(singleCount u y+singleCount w y+singleCount z y) := by
      apply Finset.prod_congr rfl
      intro y _
      by_cases hu : y=u
      · subst y
        simp [singleCount, huw, huz]
      · by_cases hw : y=w
        · subst y
          simp [singleCount, Ne.symm huw, hwz]
        · by_cases hz : y=z
          · subst y
            simp [singleCount, Ne.symm huz, Ne.symm hwz]
          · simp [singleCount, hu, hw, hz]
    _ = _ := by
      simp only [pow_add, Finset.prod_mul_distrib]
      simp [singleCount, apply_ite]

theorem unbounded_catalytic_ligation_rate_distinct {n : ℕ}
    (c : SourceMoleculeFibreConfig n) (V D : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ) (r : Reaction n) (z : Molecule n)
    (huw : reactionLeft r ≠ reactionRight r) (huz : reactionLeft r ≠ z)
    (hwz : reactionRight r ≠ z) (hu : 1 ≤ N (reactionLeft r))
    (hw : 1 ≤ N (reactionRight r)) (hz : 1 ≤ N z) (hsel : r ∈ c z) :
    unboundedPhysicalRate c V D basal cat N (.inr (.inr (r,z,true))) =
      (cat r z : ℝ)*((N (reactionLeft r) : ℝ)*N (reactionRight r)*N z)/(V : ℝ)^2 := by
  have hen : ∀ y, physicalChannelInput (.inr (.inr (r,z,true))) y ≤ N y := by
    intro y
    by_cases hyu : y=reactionLeft r
    · subst y
      simpa [physicalChannelInput, singleCount, huw, huz] using hu
    · by_cases hyw : y=reactionRight r
      · subst y
        simpa [physicalChannelInput, singleCount, Ne.symm huw, hwz] using hw
      · by_cases hyz : y=z
        · subst y
          simpa [physicalChannelInput, singleCount, Ne.symm huz, Ne.symm hwz] using hz
        · simp [physicalChannelInput, singleCount, hyu, hyw, hyz]
  rw [unboundedPhysicalRate, if_pos hen]
  unfold physicalChannelRate
  rw [catalytic_input_count]
  simp only [physicalChannelCoefficient, if_pos hsel, physicalChannelInput, if_true]
  rw [catalytic_factorial_product_distinct N _ _ _ huw huz hwz]
  field_simp

/-- Every regenerative firing in the proposed path has rate at least one,
even at one catalyst copy, provided the two foods retain half their feed count. -/
theorem productive_catalytic_rate_lower {n : ℕ}
    (c : SourceMoleculeFibreConfig n) (V D : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ) (r : Reaction n) (z : Molecule n)
    (huw : reactionLeft r ≠ reactionRight r) (huz : reactionLeft r ≠ z)
    (hwz : reactionRight r ≠ z) (hu : (V : ℝ)/2 ≤ N (reactionLeft r))
    (hw : (V : ℝ)/2 ≤ N (reactionRight r)) (hz : 1 ≤ N z)
    (hsel : r ∈ c z) (hc : 4 ≤ (cat r z : ℝ)) :
    1 ≤ unboundedPhysicalRate c V D basal cat N (.inr (.inr (r,z,true))) := by
  have hu' : 1 ≤ N (reactionLeft r) := by
    have hh : 0 < (N (reactionLeft r) : ℝ) := lt_of_lt_of_le (by positivity) hu
    have hh' : 0 < N (reactionLeft r) := by exact_mod_cast hh
    omega
  have hw' : 1 ≤ N (reactionRight r) := by
    have hh : 0 < (N (reactionRight r) : ℝ) := lt_of_lt_of_le (by positivity) hw
    have hh' : 0 < N (reactionRight r) := by exact_mod_cast hh
    omega
  rw [unbounded_catalytic_ligation_rate_distinct c V D hV basal cat N r z huw huz hwz hu' hw' hz hsel]
  apply (le_div_iff₀ (sq_pos_of_pos hV)).mpr
  have hpair := mul_le_mul hu hw (by positivity : (0 : ℝ) ≤ (V : ℝ)/2)
    (by positivity : (0 : ℝ) ≤ N (reactionLeft r))
  have hz' : (1 : ℝ) ≤ N z := by exact_mod_cast hz
  have hbase := mul_le_mul hc hpair (by positivity : (0 : ℝ) ≤ (V : ℝ)/2*((V : ℝ)/2))
    (NNReal.coe_nonneg (cat r z))
  have hlast := mul_le_mul hbase hz' (by norm_num : (0 : ℝ) ≤ 1)
    (by positivity : 0 ≤ (cat r z : ℝ)*((N (reactionLeft r) : ℝ)*N (reactionRight r)))
  nlinarith only [hlast]

end
end RandomViability
