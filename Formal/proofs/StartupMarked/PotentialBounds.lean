import proofs.StartupMarked.UniformBounds
import proofs.RandomViability.CollectiveOutput

namespace StartupMarked
open Classical RandomViability RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 50000

theorem count_potential_normalized {n : ℕ} (V : NNReal) (hV : 0 < (V : ℝ))
    (r : Reaction n) (N : Molecule n → ℕ) (hK : 0 < N (reactionProduct r)) :
    countPotential V r N =
      collectivePotential ((N (reactionLeft r) : ℝ)/V) ((N (reactionRight r) : ℝ)/V)
        ((N (reactionProduct r) : ℝ)/V)+Real.log V := by
  have hk : (N (reactionProduct r) : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hK)
  unfold countPotential foodPenalty collectivePotential
  rw [Real.log_div hk hV.ne']
  ring

theorem count_potential_endpoint {n : ℕ} (V : NNReal) (hV : 0 < (V : ℝ))
    (r : Reaction n) (N₀ N₁ : Molecule n → ℕ)
    (hfloor : (1/3000000000000000000 : ℝ) ≤ (N₀ (reactionProduct r) : ℝ)/V)
    (hK : 0 < N₁ (reactionProduct r))
    (hcap : (N₁ (reactionProduct r) : ℝ)/V ≤ 11/4) :
    countPotential V r N₁-countPotential V r N₀ < 52 := by
  have hzero : 0 < N₀ (reactionProduct r) := by
    have hp : (0 : ℝ) < (N₀ (reactionProduct r) : ℝ)/V := lt_of_lt_of_le (by norm_num) hfloor
    have hk := (div_pos_iff.mp hp).resolve_right (by intro h; linarith [h.2])
    exact_mod_cast hk.1
  rw [count_potential_normalized V hV r N₁ hK,count_potential_normalized V hV r N₀ hzero]
  have hh := collective_endpoint_penalty
    ((N₀ (reactionLeft r) : ℝ)/V) ((N₀ (reactionRight r) : ℝ)/V)
    ((N₀ (reactionProduct r) : ℝ)/V) ((N₁ (reactionLeft r) : ℝ)/V)
    ((N₁ (reactionRight r) : ℝ)/V) ((N₁ (reactionProduct r) : ℝ)/V)
    (by positivity) (by positivity) hfloor (by positivity) hcap
  linarith only [hh]

theorem source_cutoff_drift {n : ℕ} (hn : 2 ≤ n) (cfg : SourceMoleculeFibreConfig n)
    (V : NNReal) (hV : 1000000000000000000000000 ≤ (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ) (r : Reaction n)
    (hb : ∀ r,(basal r : ℝ) ≤ 4*(1/500000000 : ℝ))
    (hc : ∀ r z,(cat r z : ℝ) ≤ 16)
    (hfood : ∀ z,molLength z ≤ 2 → cfg z = ∅)
    (hM : (countMass N : ℝ) ≤ 11*V)
    (hl : molLength (reactionLeft r) = 2) (hr : molLength (reactionRight r) = 2)
    (hlen : molLength (reactionProduct r) = 4)
    (huw : reactionLeft r ≠ reactionRight r)
    (huz : reactionLeft r ≠ reactionProduct r) (hwz : reactionRight r ≠ reactionProduct r)
    (hsel : r ∈ cfg (reactionProduct r)) (hcat : 4 ≤ (cat r (reactionProduct r) : ℝ))
    (hK : stockCutoff ≤ N (reactionProduct r)) :
    19/10-624*nonfoodMass (fun z => (N z : ℝ)/V) ≤
      ∑ ch,unboundedPhysicalRate cfg V 1 basal cat N ch*cutoffReward V r stockCutoff N ch := by
  simp only [cutoffReward,if_pos hK]
  have hk : (333334 : ℝ) ≤ N (reactionProduct r) := by exact_mod_cast hK
  have hd := source_retained_reward_drift hn cfg V (by linarith) basal cat N r hb hc hfood hM
    hl hr hlen huw huz hwz hsel hcat (by change 333334 ≤ _ at hK; omega)
  have hm := marked_drift_margin V _ hV hk
  linarith only [hd,hm]

end
end StartupMarked
