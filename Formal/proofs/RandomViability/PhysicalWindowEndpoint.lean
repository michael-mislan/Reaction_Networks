import proofs.RandomViability.PhysicalWindowPotential

namespace RandomViability
open Classical RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 100000

/-- Bind the abstract endpoint penalty to actual counts and the same stopped
coordinate compensation bounds used by startup. -/
theorem physical_potential_endpoint_penalty {n : ℕ}
    (c : SourceMoleculeFibreConfig n) (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (r : Reaction n) (hlen : molLength (reactionProduct r) = 4) (T : ℝ)
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n))
    (J L : ℕ) (a b : ℝ)
    (hJ : ¬censoredNonfoodStop V T (massExitStop V) J (Preorder.frestrictLe J z))
    (hL : ¬censoredNonfoodStop V T (massExitStop V) L (Preorder.frestrictLe L z))
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b)
    (ha : a ≤ min (z (J+1)).2.2 (T-prefixElapsed J (Preorder.frestrictLe J z)))
    (hb : b ≤ min (z (L+1)).2.2 (T-prefixElapsed L (Preorder.frestrictLe L z)))
    (hxJ : (1/3000000000000000000 : ℝ) ≤ ((z J).1 (reactionProduct r) : ℝ)/V)
    (hxL : (1/3000000000000000000 : ℝ) ≤ ((z L).1 (reactionProduct r) : ℝ)/V)
    (hM : (countMass (z L).1 : ℝ) ≤ 11*V)
    (hnoiseU : coordinateNoiseBound c V basal cat (reactionLeft r) T (1/100000) z)
    (hnoiseW : coordinateNoiseBound c V basal cat (reactionRight r) T (1/100000) z)
    (hnoiseX : coordinateNoiseBound c V basal cat (reactionProduct r) T (1/300000000000000000000) z) :
    correctedPotential c V basal cat r T z L b-correctedPotential c V basal cat r T z J a < 54 := by
  have hnu := hnoiseU J a ha0 ha
  have hnw := hnoiseW J a ha0 ha
  have hnx0 := hnoiseX J a ha0 ha
  have hnx1 := hnoiseX L b hb0 hb
  have hu0 : 0 ≤ ((z J).1 (reactionLeft r) : ℝ)/V := by positivity
  have hw0 : 0 ≤ ((z J).1 (reactionRight r) : ℝ)/V := by positivity
  have hmass : polymerMass (fun q => ((z L).1 q : ℝ)/V) ≤ 11 := by
    rw [normalized_count_mass]
    exact (div_le_iff₀ hV).mpr hM
  have hcap := collective_product_cap (fun q => ((z L).1 q : ℝ)/V)
    (fun _ => by positivity) hmass (reactionProduct r) hlen
  unfold correctedPotential
  rw [corrected_coordinate_noise_identity c V basal cat (reactionLeft r) T z L b hL,
    corrected_coordinate_noise_identity c V basal cat (reactionRight r) T z L b hL,
    corrected_coordinate_noise_identity c V basal cat (reactionProduct r) T z L b hL,
    corrected_coordinate_noise_identity c V basal cat (reactionLeft r) T z J a hJ,
    corrected_coordinate_noise_identity c V basal cat (reactionRight r) T z J a hJ,
    corrected_coordinate_noise_identity c V basal cat (reactionProduct r) T z J a hJ]
  apply compensated_endpoint_penalty
  · linarith only [hu0,(abs_le.mp hnu).2]
  · linarith only [hw0,(abs_le.mp hnw).2]
  · linarith only [hxJ,(abs_le.mp hnx0).2]
  · linarith only [hxL,(abs_le.mp hnx1).2]
  · linarith only [hcap,(abs_le.mp hnx1).1]

end
end RandomViability
