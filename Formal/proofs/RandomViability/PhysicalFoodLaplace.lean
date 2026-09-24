import proofs.RandomViability.UnboundedPhysicalStep

namespace RandomViability
open Classical RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 30000

theorem unbounded_food_exponential_intensity {n : ℕ} (hn : 2 ≤ n)
    (c : SourceMoleculeFibreConfig n) (V D : NNReal)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ) :
    (∑ ch, unboundedPhysicalRate c V D basal cat N ch * ((2 : ℝ)^foodInputMass ch-1)) =
      14*(D : ℝ)*V := by
  simp only [Fintype.sum_sum_type, foodInputMass, pow_zero, sub_self, mul_zero,
    Finset.sum_const_zero, add_zero, unbounded_feed_rate]
  rw [food_length_sum hn (fun l => (D : ℝ)*V*((2 : ℝ)^l-1))]
  norm_num
  ring

theorem physical_food_laplace_factor {n : ℕ} (hn : 2 ≤ n)
    (c : SourceMoleculeFibreConfig n) (V D : NNReal)
    (hV : 0 < (V : ℝ)) (hD : 0 < (D : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ) :
    (∑ ch, unboundedPhysicalRate c V D basal cat N ch * (2 : ℝ)^foodInputMass ch) /
      ((∑ ch, unboundedPhysicalRate c V D basal cat N ch) + 14*(D : ℝ)*V) = 1 := by
  have h := unbounded_food_exponential_intensity hn c V D basal cat N
  simp only [mul_sub, mul_one, Finset.sum_sub_distrib] at h
  have ht := unbounded_total_pos hn c V D hV hD basal cat N
  have hd : (∑ ch, unboundedPhysicalRate c V D basal cat N ch) + 14*(D : ℝ)*V ≠ 0 := by positivity
  apply (div_eq_one_iff_eq hd).mpr
  linarith

end
end RandomViability
