import proofs.RandomViability.PhysicalInternalLoss
import proofs.RandomViability.PhysicalStartupDrift
import proofs.RandomViability.CollectivePathBounds

namespace RandomViability
open Classical RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section

def adverseCopyFlux {n : ℕ} (c : SourceMoleculeFibreConfig n) (V : NNReal)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ) (q : Molecule n) : ℝ :=
  ∑ ch, unboundedPhysicalRate c V 1 basal cat N ch *
    max 0 ((N q : ℝ)-(unboundedPhysicalNext N ch q : ℝ))

theorem physical_downward_jump_le_two {n : ℕ} (N : Molecule n → ℕ)
    (q : Molecule n) (ch : PhysicalCountChannel n) :
    (N q : ℝ)-(unboundedPhysicalNext N ch q : ℝ) ≤ 2 := by
  have h := unbounded_coordinate_jump_sq N q ch
  nlinarith

theorem rate_weighted_adverse_change {n : ℕ} (c : SourceMoleculeFibreConfig n)
    (V : NNReal) (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ) (q : Molecule n) (ch : PhysicalCountChannel n) :
    unboundedPhysicalRate c V 1 basal cat N ch *
        max 0 ((N q : ℝ)-(unboundedPhysicalNext N ch q : ℝ)) =
      unboundedPhysicalRate c V 1 basal cat N ch *
        max 0 ((physicalChannelInput ch q : ℝ)-(physicalChannelOutput ch q : ℝ)) := by
  by_cases he : ∀ z,physicalChannelInput ch z ≤ N z
  · rw [unboundedPhysicalNext,if_pos he,← neg_sub,coordinate_raw_change N _ _ he,neg_sub]
  · simp [unboundedPhysicalRate,he]

theorem adverse_flux_decomposition {n : ℕ} (c : SourceMoleculeFibreConfig n)
    (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ) (q : Molecule n) :
    adverseCopyFlux c V basal cat N q / V = (N q : ℝ)/V +
      markedRewardDrift c V basal cat (internalCoordinateLossReward q V) N := by
  let R := unboundedPhysicalRate c V 1 basal cat N
  have hf (f : ↥(binaryFood n 2)) :
      R (.inl (.inl f))*max 0 ((N q : ℝ)-(unboundedPhysicalNext N (.inl (.inl f)) q : ℝ)) = 0 := by
    rw [rate_weighted_adverse_change]
    simp only [physicalChannelInput,physicalChannelOutput,Nat.cast_zero,zero_sub]
    rw [max_eq_left (by have h := (singleCount_real_bounds f.val q).1; linarith),mul_zero]
  have ho (z : Molecule n) :
      R (.inl (.inr z))*max 0 ((N q : ℝ)-(unboundedPhysicalNext N (.inl (.inr z)) q : ℝ)) =
        if q = z then (N q : ℝ) else 0 := by
    rw [rate_weighted_adverse_change]
    have hr : R (.inl (.inr z)) = (N z : ℝ) := by
      simpa only [NNReal.coe_one,one_mul] using
        bounded_outflow_rate c V 1 hV basal cat (countsAtOwnMass N) z
    dsimp only [R] at hr
    rw [hr]
    simp [physicalChannelInput,physicalChannelOutput,singleCount]
    split_ifs with he <;> simp_all
  unfold adverseCopyFlux markedRewardDrift
  simp only [Fintype.sum_sum_type]
  change ((∑ f, R (.inl (.inl f))*_) + (∑ z, R (.inl (.inr z))*_) + _)/_ = _
  simp only [hf,ho,Finset.sum_const_zero,zero_add,Finset.sum_ite_eq,Finset.mem_univ,if_true]
  simp only [internalCoordinateLossReward,mul_zero,Finset.sum_const_zero,zero_add]
  simp only [add_div,Finset.sum_div,mul_div_assoc]

/-- Literal negative copy flux, including washout and repeated substrate roles.
The statement is uniform over every nonfood catalytic assignment. -/
theorem adverse_copy_flux_bound {n : ℕ} (c : SourceMoleculeFibreConfig n)
    (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ)
    (hb : ∀ r,(basal r : ℝ) ≤ 4*(1/500000000 : ℝ))
    (hc : ∀ r z,(cat r z : ℝ) ≤ 16)
    (hfood : ∀ z,molLength z ≤ 2 → c z = ∅)
    (hM : (countMass N : ℝ) ≤ 11*V) (q : Molecule n) (hq : molLength q = 4) :
    adverseCopyFlux c V basal cat N q ≤ 1476*(N q : ℝ) := by
  let x : Molecule n → ℝ := fun z => (N z : ℝ)/V
  let C : ℝ := 4*(1/500000000)+(16/3)*nonfoodMass x
  have hx : ∀ z,0 ≤ x z := fun z => by dsimp [x]; positivity
  have hnf : 0 ≤ nonfoodMass x := by
    apply Finset.sum_nonneg
    intro z _
    split_ifs <;> positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hm : polymerMass x ≤ 11 := by
    rw [normalized_count_mass]
    exact (div_le_iff₀ hV).mpr hM
  have hnfm : nonfoodMass x ≤ 11 := (nonfoodMass_le_mass x hx).trans hm
  have hC59 : C ≤ 59 := by dsimp [C]; linarith
  have hs := collective_pair_speed_bound c (fun r => basal r) (fun r z => cat r z)
    x hx (1/500000000) hb hc hfood
  have hl := collective_loss_bound
    (collectivePairSpeed c (fun r => basal r) (fun r z => cat r z) x) x hx C hC hs q
  have hlen : (molLength q : ℝ) = 4 := by exact_mod_cast hq
  rw [hlen] at hl
  have hinternal := physical_internal_loss_le_envelope q V hV c basal cat N
  have hmul := mul_le_mul_of_nonneg_right hm (mul_nonneg hC (hx q))
  have hmulC := mul_le_mul_of_nonneg_right hC59 (hx q)
  have hsum : adverseCopyFlux c V basal cat N q / V ≤ 1476*x q := by
    rw [adverse_flux_decomposition c V hV basal cat N q]
    change x q + _ ≤ _
    change _ ≤ collectiveLoss (collectivePairSpeed c (fun r => basal r) (fun r z => cat r z) x) x q at hinternal
    nlinarith only [hl,hinternal,hmul,hmulC]
  have hh := (div_le_iff₀ hV).mp hsum
  simpa [x,div_mul_cancel₀ _ (ne_of_gt hV),mul_assoc] using hh

end
end RandomViability
