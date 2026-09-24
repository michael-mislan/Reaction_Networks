import proofs.RandomViability.MassCompensationDecomposition

namespace RandomViability
open Classical RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 100000

theorem mass_raw_change {n : ℕ} (N input output : Molecule n → ℕ)
    (he : ∀ z,input z ≤ N z) :
    (countMass (applyCountChannel N input output) : ℝ)-(countMass N : ℝ) =
      (countMass output : ℝ)-(countMass input : ℝ) := by
  have hh : (countMass (applyCountChannel N input output) : ℝ)+(countMass input : ℝ) =
      (countMass N : ℝ)+(countMass output : ℝ) := by
    exact_mod_cast applyCountChannel_mass_accounting N input output he
  linarith only [hh]

theorem rate_weighted_mass_change {n : ℕ} (c : SourceMoleculeFibreConfig n) (V : NNReal)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ) (ch : PhysicalCountChannel n) :
    unboundedPhysicalRate c V 1 basal cat N ch*massConcentrationJump V N ch =
      unboundedPhysicalRate c V 1 basal cat N ch*
        ((countMass (physicalChannelOutput ch) : ℝ)-(countMass (physicalChannelInput ch) : ℝ))/V := by
  by_cases he : ∀ z,physicalChannelInput ch z ≤ N z
  · simp only [massConcentrationJump,unboundedPhysicalNext,if_pos he]
    rw [mass_raw_change N _ _ he]
    ring
  · simp [unboundedPhysicalRate,he]

/-- Exact unbounded literal mass generator: chemistry cancels, with no caps
or food-row conditions on the ambient catalytic source. -/
theorem physical_mass_drift_identity {n : ℕ} (hn : 2 ≤ n)
    (c : SourceMoleculeFibreConfig n) (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ) :
    physicalMassDrift c V basal cat N = 10-(countMass N : ℝ)/V := by
  have hb : ∀ r d,unboundedPhysicalRate c V 1 basal cat N (.inr (.inl (r,d)))*
      massConcentrationJump V N (.inr (.inl (r,d))) = 0 := by
    intro r d
    rw [rate_weighted_mass_change]
    cases d <;> simp only [physicalChannelOutput,physicalChannelInput,Bool.false_eq_true,
      if_false,if_true,basal_count_channel_balance,sub_self,mul_zero,zero_div]
  have hc : ∀ r z d,unboundedPhysicalRate c V 1 basal cat N (.inr (.inr (r,z,d)))*
      massConcentrationJump V N (.inr (.inr (r,z,d))) = 0 := by
    intro r z d
    rw [rate_weighted_mass_change]
    cases d <;> simp only [physicalChannelOutput,physicalChannelInput,Bool.false_eq_true,
      if_false,if_true,catalytic_count_channel_balance,sub_self,mul_zero,zero_div]
  have hf : ∀ f : ↥(binaryFood n 2),unboundedPhysicalRate c V 1 basal cat N (.inl (.inl f))*
      massConcentrationJump V N (.inl (.inl f)) = (molLength f.val : ℝ) := by
    intro f
    rw [rate_weighted_mass_change,unbounded_feed_rate]
    simp only [NNReal.coe_one,one_mul,physicalChannelOutput,physicalChannelInput,countMass_single]
    have hz : countMass (fun _ : Molecule n => 0) = 0 := by simp [countMass]
    rw [hz,Nat.cast_zero,sub_zero]
    exact mul_div_cancel_left₀ _ (ne_of_gt hV)
  have ho : ∀ z,unboundedPhysicalRate c V 1 basal cat N (.inl (.inr z))*
      massConcentrationJump V N (.inl (.inr z)) = -(molLength z : ℝ)*(N z : ℝ)/V := by
    intro z
    rw [rate_weighted_mass_change]
    have hr := bounded_outflow_rate c V 1 hV basal cat (countsAtOwnMass N) z
    change unboundedPhysicalRate c V 1 basal cat N (.inl (.inr z)) = (1 : NNReal)*(N z : ℝ) at hr
    rw [hr]
    simp only [NNReal.coe_one,one_mul,physicalChannelOutput,physicalChannelInput,countMass_single]
    have hz : countMass (fun _ : Molecule n => 0) = 0 := by simp [countMass]
    rw [hz,Nat.cast_zero]
    ring
  unfold physicalMassDrift
  simp only [Fintype.sum_sum_type,hb,hc,Finset.sum_const_zero,add_zero,hf,ho]
  rw [food_length_sum hn (fun l => (l : ℝ))]
  simp only [← Finset.sum_div,neg_mul,Finset.sum_neg_distrib,countMass,Nat.cast_sum,Nat.cast_mul]
  ring

end
end RandomViability
