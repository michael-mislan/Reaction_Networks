import proofs.StartupMarked.LogTaylor

namespace StartupMarked
open Classical RandomViability RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 50000

theorem selected_copy_change {n : ℕ} (r : Reaction n) (N : Molecule n → ℕ)
    (huz : reactionLeft r ≠ reactionProduct r) (hwz : reactionRight r ≠ reactionProduct r) :
    (unboundedPhysicalNext N (selectedForward r) (reactionProduct r) : ℝ)-N (reactionProduct r) =
      if (∀ z,physicalChannelInput (selectedForward r) z ≤ N z) then 1 else 0 := by
  by_cases he : ∀ z,physicalChannelInput (selectedForward r) z ≤ N z
  · rw [if_pos he,unboundedPhysicalNext,if_pos he]
    have hh := coordinate_raw_change N (physicalChannelInput (selectedForward r))
      (physicalChannelOutput (selectedForward r)) he (reactionProduct r)
    norm_num [selectedForward,physicalChannelInput,physicalChannelOutput,singleCount,
      Ne.symm huz,Ne.symm hwz] at hh ⊢
    exact hh
  · rw [if_neg he,unboundedPhysicalNext,if_neg he,sub_self]

theorem selected_retained_change {n : ℕ} (r : Reaction n) (N : Molecule n → ℕ) :
    retainedChange r N (selectedForward r) =
      (unboundedPhysicalNext N (selectedForward r) (reactionProduct r) : ℝ)-N (reactionProduct r) := by
  simp only [retainedChange,true_or,if_true]

theorem selected_weighted_change {n : ℕ} (cfg : SourceMoleculeFibreConfig n) (V : NNReal)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (r : Reaction n) (N : Molecule n → ℕ)
    (huz : reactionLeft r ≠ reactionProduct r) (hwz : reactionRight r ≠ reactionProduct r) :
    unboundedPhysicalRate cfg V 1 basal cat N (selectedForward r)*retainedChange r N (selectedForward r) =
      unboundedPhysicalRate cfg V 1 basal cat N (selectedForward r) := by
  rw [selected_retained_change,selected_copy_change r N huz hwz]
  split_ifs with he
  · rw [mul_one]
  · simp [unboundedPhysicalRate,he]

theorem retained_first_moment_term {n : ℕ} (cfg : SourceMoleculeFibreConfig n) (V : NNReal)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (r : Reaction n) (N : Molecule n → ℕ) (ch : PhysicalCountChannel n)
    (huz : reactionLeft r ≠ reactionProduct r) (hwz : reactionRight r ≠ reactionProduct r) :
    unboundedPhysicalRate cfg V 1 basal cat N ch*retainedChange r N ch =
      (if ch = selectedForward r then unboundedPhysicalRate cfg V 1 basal cat N ch else 0)-
      unboundedPhysicalRate cfg V 1 basal cat N ch*
        max 0 ((N (reactionProduct r) : ℝ)-unboundedPhysicalNext N ch (reactionProduct r)) := by
  by_cases hs : ch = selectedForward r
  · subst ch
    rw [selected_weighted_change cfg V basal cat r N huz hwz,if_pos rfl]
    have hh := selected_copy_change r N huz hwz
    have hn : (N (reactionProduct r) : ℝ)-unboundedPhysicalNext N (selectedForward r) (reactionProduct r) ≤ 0 := by
      split_ifs at hh <;> linarith
    rw [max_eq_left hn,mul_zero,sub_zero]
  · rw [if_neg hs]
    unfold retainedChange
    by_cases hn : unboundedPhysicalNext N ch (reactionProduct r) < N (reactionProduct r)
    · rw [if_pos (Or.inr hn)]
      have hh : (0 : ℝ) ≤ (N (reactionProduct r) : ℝ)-unboundedPhysicalNext N ch (reactionProduct r) := by
        exact sub_nonneg.mpr (by exact_mod_cast hn.le)
      rw [max_eq_right hh]
      ring
    · rw [if_neg (not_or.mpr ⟨hs,hn⟩)]
      have hh : (N (reactionProduct r) : ℝ)-unboundedPhysicalNext N ch (reactionProduct r) ≤ 0 := by
        exact sub_nonpos.mpr (by exact_mod_cast Nat.le_of_not_lt hn)
      rw [max_eq_left hh,mul_zero,sub_zero]

theorem selected_rate_sum {n : ℕ} (cfg : SourceMoleculeFibreConfig n) (V : NNReal)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (r : Reaction n) (N : Molecule n → ℕ) :
    (∑ ch,if ch = selectedForward r then unboundedPhysicalRate cfg V 1 basal cat N ch else 0) =
      unboundedPhysicalRate cfg V 1 basal cat N (selectedForward r) := by
  rw [Finset.sum_eq_single (selectedForward r)]
  · rw [if_pos rfl]
  · intro ch _ hne
    exact if_neg hne
  · intro hh
    exact (hh (Finset.mem_univ _)).elim

theorem retained_first_moment {n : ℕ} (cfg : SourceMoleculeFibreConfig n) (V : NNReal)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (r : Reaction n) (N : Molecule n → ℕ)
    (huz : reactionLeft r ≠ reactionProduct r) (hwz : reactionRight r ≠ reactionProduct r) :
    (∑ ch,unboundedPhysicalRate cfg V 1 basal cat N ch*retainedChange r N ch) =
      unboundedPhysicalRate cfg V 1 basal cat N (selectedForward r)-
        adverseCopyFlux cfg V basal cat N (reactionProduct r) := by
  simp_rw [retained_first_moment_term cfg V basal cat r N _ huz hwz]
  rw [Finset.sum_sub_distrib]
  rw [selected_rate_sum]
  rfl

theorem retained_square_term {n : ℕ} (r : Reaction n) (N : Molecule n → ℕ)
    (ch : PhysicalCountChannel n)
    (huz : reactionLeft r ≠ reactionProduct r) (hwz : reactionRight r ≠ reactionProduct r) :
    (retainedChange r N ch)^2 ≤ (if ch = selectedForward r then (1 : ℝ) else 0)+
      2*max 0 ((N (reactionProduct r) : ℝ)-unboundedPhysicalNext N ch (reactionProduct r)) := by
  have hp := le_max_left (0 : ℝ)
    ((N (reactionProduct r) : ℝ)-unboundedPhysicalNext N ch (reactionProduct r))
  by_cases hs : ch = selectedForward r
  · subst ch
    rw [if_pos rfl,selected_retained_change]
    have hh := selected_copy_change r N huz hwz
    split_ifs at hh <;> rw [hh] <;> nlinarith only [hp]
  · rw [if_neg hs]
    unfold retainedChange
    split_ifs with hh
    · have hn := hh.resolve_left hs
      have hd : (unboundedPhysicalNext N ch (reactionProduct r) : ℝ)-N (reactionProduct r) ≤ 0 :=
        sub_nonpos.mpr (by exact_mod_cast hn.le)
      have hlo := physical_downward_jump_le_two N (reactionProduct r) ch
      rw [max_eq_right (by linarith : (0 : ℝ) ≤
        (N (reactionProduct r) : ℝ)-unboundedPhysicalNext N ch (reactionProduct r))]
      nlinarith only [mul_nonneg (neg_nonneg.mpr hd) (by linarith only [hlo] :
        0 ≤ 2+((unboundedPhysicalNext N ch (reactionProduct r) : ℝ)-N (reactionProduct r)))]
    · nlinarith only [hp]

theorem retained_second_moment {n : ℕ} (cfg : SourceMoleculeFibreConfig n) (V : NNReal)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (r : Reaction n) (N : Molecule n → ℕ)
    (huz : reactionLeft r ≠ reactionProduct r) (hwz : reactionRight r ≠ reactionProduct r) :
    (∑ ch,unboundedPhysicalRate cfg V 1 basal cat N ch*(retainedChange r N ch)^2) ≤
      unboundedPhysicalRate cfg V 1 basal cat N (selectedForward r)+
        2*adverseCopyFlux cfg V basal cat N (reactionProduct r) := by
  have hh := Finset.sum_le_sum (fun ch (_ : ch ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (retained_square_term r N ch huz hwz)
      (unboundedPhysicalRate_nonneg cfg V 1 basal cat N ch))
  apply hh.trans_eq
  simp only [mul_add,Finset.sum_add_distrib,mul_ite,mul_one,mul_zero]
  rw [selected_rate_sum]
  congr 1
  unfold adverseCopyFlux
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ch _
  ring

end
end StartupMarked
