import proofs.RandomViability.PhysicalPairEnvelope
import proofs.RandomViability.MarkedRewardInterval

set_option Elab.async false
namespace RandomViability
open Classical RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 70000

def reactionInputMultiplicity {n : ℕ} (r : Reaction n) (q : Molecule n) (d : Bool) : ℝ :=
  if d then (singleCount (reactionLeft r) q : ℝ)+singleCount (reactionRight r) q
  else singleCount (reactionProduct r) q

def internalInputMultiplicity {n : ℕ} (q : Molecule n) : PhysicalCountChannel n → ℝ
  | .inl _ => 0
  | .inr (.inl (r,d)) => reactionInputMultiplicity r q d
  | .inr (.inr (r,_,d)) => reactionInputMultiplicity r q d

def internalCoordinateLossReward {n : ℕ} (q : Molecule n) (V : NNReal)
    (N : Molecule n → ℕ) : PhysicalCountChannel n → ℝ
  | .inl _ => 0
  | .inr ch => max 0 ((N q : ℝ)-(unboundedPhysicalNext N (.inr ch) q : ℝ))/V

theorem internal_coordinate_loss_rate_bound {n : ℕ} (q : Molecule n) (V : NNReal)
    (hV : 0 < (V : ℝ)) (c : SourceMoleculeFibreConfig n)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ) (ch : PhysicalCountChannel n) :
    unboundedPhysicalRate c V 1 basal cat N ch*internalCoordinateLossReward q V N ch ≤
      unboundedPhysicalRate c V 1 basal cat N ch/V*internalInputMultiplicity q ch := by
  by_cases he : ∀ z,physicalChannelInput ch z ≤ N z
  · have hb (r : Reaction n) (d : Bool) :
      max 0 (-(if d then (singleCount (reactionProduct r) q : ℝ)-
        ((singleCount (reactionLeft r) q : ℝ)+singleCount (reactionRight r) q)
        else ((singleCount (reactionLeft r) q : ℝ)+singleCount (reactionRight r) q)-
          singleCount (reactionProduct r) q)) ≤ reactionInputMultiplicity r q d := by
      have hl := (singleCount_real_bounds (reactionLeft r) q).1
      have hr := (singleCount_real_bounds (reactionRight r) q).1
      have hp := (singleCount_real_bounds (reactionProduct r) q).1
      cases d <;> simp only [reactionInputMultiplicity,Bool.false_eq_true,↓reduceIte] <;>
        apply max_le <;> linarith
    have hR := unboundedPhysicalRate_nonneg c V 1 basal cat N ch
    rcases ch with external | (⟨r,d⟩ | ⟨r,z,d⟩)
    · simp [internalCoordinateLossReward,internalInputMultiplicity]
    · have hc := basal_coordinate_raw_change N r d q he
      have hh : max 0 ((N q : ℝ)-(unboundedPhysicalNext N (.inr (.inl (r,d))) q : ℝ)) ≤
          reactionInputMultiplicity r q d := by
        rw [unboundedPhysicalNext,if_pos he,← neg_sub, hc]
        exact hb r d
      have hu := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hh hV.le) hR
      simpa only [internalCoordinateLossReward,internalInputMultiplicity,div_mul_eq_mul_div,mul_div_assoc] using hu
    · have hc := catalytic_coordinate_raw_change N r z d q he
      have hh : max 0 ((N q : ℝ)-(unboundedPhysicalNext N (.inr (.inr (r,z,d))) q : ℝ)) ≤
          reactionInputMultiplicity r q d := by
        rw [unboundedPhysicalNext,if_pos he,← neg_sub, hc]
        exact hb r d
      have hu := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hh hV.le) hR
      simpa only [internalCoordinateLossReward,internalInputMultiplicity,div_mul_eq_mul_div,mul_div_assoc] using hu
  · simp [unboundedPhysicalRate,he]

theorem internal_input_sum_pair {n : ℕ} (q : Molecule n) (V : NNReal)
    (c : SourceMoleculeFibreConfig n) (basal : Reaction n → NNReal)
    (cat : Reaction n → Molecule n → NNReal) (N : Molecule n → ℕ) :
    (∑ ch,unboundedPhysicalRate c V 1 basal cat N ch/V*internalInputMultiplicity q ch) =
      ∑ r : Reaction n,∑ d : Bool,physicalPairFlux c V basal cat N r d*reactionInputMultiplicity r q d := by
  simp only [Fintype.sum_sum_type,Fintype.sum_prod_type,internalInputMultiplicity,
    mul_zero,Finset.sum_const_zero,zero_add]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.sum_comm,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _
  simp only [physicalPairFlux,add_div,Finset.sum_div,add_mul,Finset.sum_mul]

theorem physical_internal_loss_le_envelope {n : ℕ} (q : Molecule n) (V : NNReal)
    (hV : 0 < (V : ℝ)) (c : SourceMoleculeFibreConfig n)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ) :
    markedRewardDrift c V basal cat (internalCoordinateLossReward q V) N ≤
      collectiveLoss (collectivePairSpeed c (fun r => basal r) (fun r z => cat r z)
        (fun z => (N z : ℝ)/V)) (fun z => (N z : ℝ)/V) q := by
  calc
    _ ≤ ∑ ch,unboundedPhysicalRate c V 1 basal cat N ch/V*internalInputMultiplicity q ch :=
      Finset.sum_le_sum (fun ch _ => internal_coordinate_loss_rate_bound q V hV c basal cat N ch)
    _ = ∑ r : Reaction n,∑ d : Bool,physicalPairFlux c V basal cat N r d*reactionInputMultiplicity r q d :=
      internal_input_sum_pair q V c basal cat N
    _ ≤ _ := by
      unfold collectiveLoss
      rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro r _
      have hf := physical_pair_flux_envelope c V hV basal cat N r true
      have hb := physical_pair_flux_envelope c V hV basal cat N r false
      simp only [↓reduceIte,Bool.false_eq_true] at hf hb
      simp only [Fintype.sum_bool,reactionInputMultiplicity,↓reduceIte,Bool.false_eq_true]
      unfold singleCount
      simp only [eq_comm (a := q)]
      split_ifs <;> norm_num <;> nlinarith only [hf,hb]

end
end RandomViability
