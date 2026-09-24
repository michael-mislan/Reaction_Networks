import proofs.StartupCount.CountFlux
import proofs.RandomViability.CollectiveCalculus

namespace StartupMarked
open Classical RandomViability RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 40000

def selectedForward {n : ℕ} (r : Reaction n) : PhysicalCountChannel n :=
  .inr (.inr (r,reactionProduct r,true))

def foodPenalty {n : ℕ} (V : NNReal) (r : Reaction n) (N : Molecule n → ℕ) : ℝ :=
  4*((foodDeficit ((N (reactionLeft r) : ℝ)/V))^2+
    (foodDeficit ((N (reactionRight r) : ℝ)/V))^2)

def retainedLog {n : ℕ} (r : Reaction n) (N : Molecule n → ℕ) (ch : PhysicalCountChannel n) : ℝ :=
  if ch = selectedForward r ∨ unboundedPhysicalNext N ch (reactionProduct r) < N (reactionProduct r)
  then Real.log (unboundedPhysicalNext N ch (reactionProduct r) : ℝ)-Real.log (N (reactionProduct r) : ℝ)
  else 0

def retainedReward {n : ℕ} (V : NNReal) (r : Reaction n)
    (N : Molecule n → ℕ) (ch : PhysicalCountChannel n) : ℝ :=
  retainedLog r N ch - (foodPenalty V r (unboundedPhysicalNext N ch)-foodPenalty V r N)

def cutoffReward {n : ℕ} (V : NNReal) (r : Reaction n) (k₀ : ℕ)
    (N : Molecule n → ℕ) (ch : PhysicalCountChannel n) : ℝ :=
  if k₀ ≤ N (reactionProduct r) then retainedReward V r N ch else 0

def countPotential {n : ℕ} (V : NNReal) (r : Reaction n) (N : Molecule n → ℕ) : ℝ :=
  Real.log (N (reactionProduct r) : ℝ)-foodPenalty V r N

theorem retained_log_le_increment {n : ℕ} (r : Reaction n) (N : Molecule n → ℕ)
    (ch : PhysicalCountChannel n) (hK : 0 < N (reactionProduct r)) :
    retainedLog r N ch ≤
      Real.log (unboundedPhysicalNext N ch (reactionProduct r) : ℝ)-Real.log (N (reactionProduct r) : ℝ) := by
  unfold retainedLog
  split_ifs with hh
  · exact le_rfl
  · have hk : N (reactionProduct r) ≤ unboundedPhysicalNext N ch (reactionProduct r) := by
      exact Nat.le_of_not_lt (fun he => hh (Or.inr he))
    have hp : (0 : ℝ) < N (reactionProduct r) := by exact_mod_cast hK
    have hle : (N (reactionProduct r) : ℝ) ≤ unboundedPhysicalNext N ch (reactionProduct r) := by
      exact_mod_cast hk
    exact sub_nonneg.mpr (Real.log_le_log hp hle)

theorem retained_reward_le_potential_increment {n : ℕ} (V : NNReal) (r : Reaction n)
    (N : Molecule n → ℕ) (ch : PhysicalCountChannel n) (hK : 0 < N (reactionProduct r)) :
    retainedReward V r N ch ≤ countPotential V r (unboundedPhysicalNext N ch)-countPotential V r N := by
  have hh := retained_log_le_increment r N ch hK
  unfold retainedReward countPotential
  linarith only [hh]

theorem cutoff_agrees_above_floor {n : ℕ} (V : NNReal) (r : Reaction n) (k₀ : ℕ)
    (N : Molecule n → ℕ) (ch : PhysicalCountChannel n) (hK : k₀ ≤ N (reactionProduct r)) :
    cutoffReward V r k₀ N ch = retainedReward V r N ch := if_pos hK

theorem retained_path_sum_le {n : ℕ} (V : NNReal) (r : Reaction n)
    (N : ℕ → Molecule n → ℕ) (ch : ℕ → PhysicalCountChannel n) (L : ℕ)
    (hK : ∀ i < L,0 < N i (reactionProduct r))
    (hnext : ∀ i < L,N (i+1) = unboundedPhysicalNext (N i) (ch i)) :
    (∑ i ∈ Finset.range L,retainedReward V r (N i) (ch i)) ≤
      countPotential V r (N L)-countPotential V r (N 0) := by
  have he (j : ℕ) : (∑ i ∈ Finset.range j,
      (countPotential V r (N (i+1))-countPotential V r (N i))) =
      countPotential V r (N j)-countPotential V r (N 0) := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Finset.sum_range_succ,ih]
      ring
  rw [← he L]
  apply Finset.sum_le_sum
  intro i hi
  rw [hnext i (Finset.mem_range.mp hi)]
  exact retained_reward_le_potential_increment V r (N i) (ch i) (hK i (Finset.mem_range.mp hi))

end
end StartupMarked
