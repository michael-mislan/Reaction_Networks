import proofs.RandomViability.SingleIncidenceErasure
import proofs.RandomViability.PhysicalCoordinateDrift

set_option Elab.async false
namespace RandomViability
open Classical RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 160000

theorem reward_drift_erase_identity {n : ℕ} (c : SourceMoleculeFibreConfig n)
    (z₀ : Molecule n) (r₀ : Reaction n) (V : NNReal)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (reward : (Molecule n → ℕ) → PhysicalCountChannel n → ℝ) (N : Molecule n → ℕ) :
    markedRewardDrift c V basal cat reward N =
      markedRewardDrift (eraseLocalIncidence c z₀ r₀) V basal cat reward N+
      ∑ d : Bool,unboundedPhysicalRate c V 1 basal cat N (.inr (.inr (r₀,z₀,d)))*
        reward N (.inr (.inr (r₀,z₀,d))) := by
  let localTerm : PhysicalCountChannel n → ℝ := fun ch =>
    match ch with
    | .inr (.inr (r,z,d)) => if r = r₀ then if z = z₀ then
        unboundedPhysicalRate c V 1 basal cat N (.inr (.inr (r,z,d)))*reward N (.inr (.inr (r,z,d))) else 0 else 0
    | _ => 0
  have hpoint (ch : PhysicalCountChannel n) :
      unboundedPhysicalRate c V 1 basal cat N ch*reward N ch =
        unboundedPhysicalRate (eraseLocalIncidence c z₀ r₀) V 1 basal cat N ch*reward N ch+localTerm ch := by
    rcases ch with external | (⟨r,d⟩ | ⟨r,z,d⟩)
    · simp only [localTerm,add_zero]
      rfl
    · simp only [localTerm,add_zero]
      rfl
    · by_cases hz : z = z₀
      · subst z
        by_cases hr : r = r₀
        · subst r
          have hzero : unboundedPhysicalRate (eraseLocalIncidence c z₀ r₀) V 1 basal cat N
              (.inr (.inr (r₀,z₀,d))) = 0 := by
            simp [unboundedPhysicalRate,physicalChannelRate,physicalChannelCoefficient,eraseLocalIncidence]
          simp only [localTerm,↓reduceIte,hzero,zero_mul,zero_add]
        · have hmem : (r ∈ eraseLocalIncidence c z₀ r₀ z₀) ↔ r ∈ c z₀ := by simp [eraseLocalIncidence,hr]
          simp only [localTerm,hr,↓reduceIte,add_zero,unboundedPhysicalRate,physicalChannelRate,physicalChannelCoefficient,hmem]
      · have hrow : eraseLocalIncidence c z₀ r₀ z = c z := if_neg hz
        simp only [localTerm,hz,↓reduceIte,ite_self,add_zero,unboundedPhysicalRate,physicalChannelRate,physicalChannelCoefficient,hrow]
  unfold markedRewardDrift
  conv_lhs => arg 2; ext ch; rw [hpoint]
  rw [Finset.sum_add_distrib]
  congr 1
  simp [localTerm,Fintype.sum_sum_type,Fintype.sum_prod_type,Finset.sum_add_distrib]

theorem outsider_coordinate_drift_erase {n : ℕ} (c : SourceMoleculeFibreConfig n)
    (z₀ : Molecule n) (r₀ : Reaction n) (h : OutsiderFoodIncidence r₀ z₀)
    (V : NNReal) (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ) :
    physicalCoordinateDrift c V basal cat N z₀ =
      physicalCoordinateDrift (eraseLocalIncidence c z₀ r₀) V basal cat N z₀ := by
  have hl : z₀ ≠ reactionLeft r₀ := by
    intro he
    have hh := congrArg molLength he
    have hf := h.1
    have hz := h.2.2.2.1
    omega
  have hr : z₀ ≠ reactionRight r₀ := by
    intro he
    have hh := congrArg molLength he
    have hf := h.2.1
    have hz := h.2.2.2.1
    omega
  have hp : z₀ ≠ reactionProduct r₀ := h.2.2.2.2
  have hj (d : Bool) : coordinateConcentrationJump V z₀ N (.inr (.inr (r₀,z₀,d))) = 0 := by
    unfold coordinateConcentrationJump
    by_cases he : ∀ q,physicalChannelInput (.inr (.inr (r₀,z₀,d))) q ≤ N q
    · rw [unboundedPhysicalNext,if_pos he,catalytic_coordinate_raw_change N r₀ z₀ d z₀ he]
      cases d <;> simp [singleCount,hl,hr,hp]
    · simp [unboundedPhysicalNext,he]
  have hh := reward_drift_erase_identity c z₀ r₀ V basal cat (coordinateConcentrationJump V z₀) N
  simpa only [markedRewardDrift,physicalCoordinateDrift,hj,mul_zero,Finset.sum_const_zero,add_zero] using hh

end
end RandomViability
