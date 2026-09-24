import proofs.StartupMarked.SelectedRate
import proofs.StartupMarked.SharpLoss
import proofs.StartupMarked.CatalogRate
import proofs.RandomViability.CopyNumberLogBound

namespace StartupMarked
open Classical RandomViability RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 50000

def retainedChange {n : ℕ} (r : Reaction n) (N : Molecule n → ℕ) (ch : PhysicalCountChannel n) : ℝ :=
  if ch = selectedForward r ∨ unboundedPhysicalNext N ch (reactionProduct r) < N (reactionProduct r)
  then (unboundedPhysicalNext N ch (reactionProduct r) : ℝ)-(N (reactionProduct r) : ℝ)
  else 0

theorem retained_change_lower {n : ℕ} (r : Reaction n) (N : Molecule n → ℕ) (ch : PhysicalCountChannel n) :
    -2 ≤ retainedChange r N ch := by
  unfold retainedChange
  split_ifs
  · have hh := physical_downward_jump_le_two N (reactionProduct r) ch
    linarith only [hh]
  · norm_num

theorem retained_log_as_change {n : ℕ} (r : Reaction n) (N : Molecule n → ℕ) (ch : PhysicalCountChannel n) :
    retainedLog r N ch =
      Real.log ((N (reactionProduct r) : ℝ)+retainedChange r N ch)-Real.log (N (reactionProduct r) : ℝ) := by
  unfold retainedLog retainedChange
  split_ifs
  · rw [add_sub_cancel]
  · simp only [add_zero,sub_self]

theorem retained_log_taylor_lower {n : ℕ} (r : Reaction n) (N : Molecule n → ℕ)
    (ch : PhysicalCountChannel n) (hK : 4 ≤ N (reactionProduct r)) :
    retainedChange r N ch/(N (reactionProduct r) : ℝ)-
      2*(retainedChange r N ch)^2/(N (reactionProduct r) : ℝ)^2 ≤ retainedLog r N ch := by
  have hk : (4 : ℝ) ≤ N (reactionProduct r) := by exact_mod_cast hK
  rw [retained_log_as_change]
  apply Binding.log_jump_lower _ _ (by linarith)
  have hd := retained_change_lower r N ch
  linarith only [hk,hd]

theorem physical_retained_log_taylor {n : ℕ} (cfg : SourceMoleculeFibreConfig n)
    (V : NNReal) (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ) (r : Reaction n) (hK : 4 ≤ N (reactionProduct r)) :
    (∑ ch,unboundedPhysicalRate cfg V 1 basal cat N ch*retainedChange r N ch)/(N (reactionProduct r) : ℝ)-
      2*(∑ ch,unboundedPhysicalRate cfg V 1 basal cat N ch*(retainedChange r N ch)^2)/
        (N (reactionProduct r) : ℝ)^2 ≤
      ∑ ch,unboundedPhysicalRate cfg V 1 basal cat N ch*retainedLog r N ch := by
  have hh := Finset.sum_le_sum (fun ch (_ : ch ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (retained_log_taylor_lower r N ch hK)
      (unboundedPhysicalRate_nonneg cfg V 1 basal cat N ch))
  convert hh using 1
  simp only [Finset.sum_div,Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro ch _
  ring

end
end StartupMarked
