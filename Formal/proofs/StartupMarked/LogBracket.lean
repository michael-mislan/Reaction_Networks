import proofs.StartupMarked.RetainedMoments

namespace StartupMarked
open Classical RandomViability RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 50000

theorem log_difference_upper (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Real.log b-Real.log a ≤ (b-a)/a := by
  rw [← Real.log_div hb.ne' ha.ne']
  have hh := Real.log_le_sub_one_of_pos (div_pos hb ha)
  have he : b/a-1 = (b-a)/a := by field_simp
  rwa [he] at hh

theorem log_difference_lipschitz (a b c : ℝ) (hc : 0 < c) (ha : c ≤ a) (hb : c ≤ b) :
    |Real.log b-Real.log a| ≤ |b-a|/c := by
  have ha0 := hc.trans_le ha
  have hb0 := hc.trans_le hb
  by_cases hab : a ≤ b
  · rw [abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log ha0 hab)),abs_of_nonneg (sub_nonneg.mpr hab)]
    exact (log_difference_upper a b ha0 hb0).trans
      (div_le_div_of_nonneg_left (sub_nonneg.mpr hab) hc ha)
  · have hba : b ≤ a := le_of_not_ge hab
    rw [abs_of_nonpos (sub_nonpos.mpr (Real.log_le_log hb0 hba)),
      abs_of_nonpos (sub_nonpos.mpr hba),neg_sub,neg_sub]
    exact (log_difference_upper b a hb0 ha0).trans
      (div_le_div_of_nonneg_left (sub_nonneg.mpr hba) hc hb)

theorem retained_log_square {n : ℕ} (r : Reaction n) (N : Molecule n → ℕ)
    (ch : PhysicalCountChannel n) (hK : 2 < N (reactionProduct r)) :
    (retainedLog r N ch)^2 ≤ (retainedChange r N ch)^2/((N (reactionProduct r) : ℝ)-2)^2 := by
  have hk : (2 : ℝ) < N (reactionProduct r) := by exact_mod_cast hK
  have hd := retained_change_lower r N ch
  have hh := log_difference_lipschitz (N (reactionProduct r) : ℝ)
    ((N (reactionProduct r) : ℝ)+retainedChange r N ch)
    ((N (reactionProduct r) : ℝ)-2) (by linarith) (by linarith) (by linarith)
  rw [← retained_log_as_change,add_sub_cancel_left] at hh
  have hs := pow_le_pow_left₀ (abs_nonneg _) hh 2
  simpa only [sq_abs,div_pow] using hs

theorem physical_retained_log_square {n : ℕ} (cfg : SourceMoleculeFibreConfig n) (V : NNReal)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (r : Reaction n) (N : Molecule n → ℕ)
    (huz : reactionLeft r ≠ reactionProduct r) (hwz : reactionRight r ≠ reactionProduct r)
    (hK : 2 < N (reactionProduct r)) :
    (∑ ch,unboundedPhysicalRate cfg V 1 basal cat N ch*(retainedLog r N ch)^2) ≤
      (unboundedPhysicalRate cfg V 1 basal cat N (selectedForward r)+
        2*adverseCopyFlux cfg V basal cat N (reactionProduct r))/((N (reactionProduct r) : ℝ)-2)^2 := by
  calc
    _ ≤ ∑ ch,unboundedPhysicalRate cfg V 1 basal cat N ch*
        ((retainedChange r N ch)^2/((N (reactionProduct r) : ℝ)-2)^2) :=
      Finset.sum_le_sum (fun ch _ => mul_le_mul_of_nonneg_left (retained_log_square r N ch hK)
        (unboundedPhysicalRate_nonneg cfg V 1 basal cat N ch))
    _ = (∑ ch,unboundedPhysicalRate cfg V 1 basal cat N ch*(retainedChange r N ch)^2)/
        ((N (reactionProduct r) : ℝ)-2)^2 := by simp only [mul_div_assoc,Finset.sum_div]
    _ ≤ _ := div_le_div_of_nonneg_right (retained_second_moment cfg V basal cat r N huz hwz) (sq_nonneg _)

end
end StartupMarked
