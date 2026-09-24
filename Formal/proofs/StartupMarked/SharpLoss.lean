import proofs.StartupCount.CountFlux

namespace RandomViability
open Classical RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 50000

/-- Keep occupied nonfood mass in the first-order loss bound. The coarser1476K
bound is reserved for quadratic Taylor errors. -/
theorem adverse_copy_flux_mass_bound {n : ℕ} (c : SourceMoleculeFibreConfig n)
    (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ) (eps : ℝ) (heps : 0 ≤ eps)
    (hb : ∀ r,(basal r : ℝ) ≤ 4*eps)
    (hc : ∀ r z,(cat r z : ℝ) ≤ 16)
    (hfood : ∀ z,molLength z ≤ 2 → c z = ∅)
    (hM : (countMass N : ℝ) ≤ 11*V) (q : Molecule n) (hq : molLength q = 4) :
    adverseCopyFlux c V basal cat N q ≤
      (1+25*(4*eps+(16/3)*nonfoodMass (fun z => (N z : ℝ)/V)))*(N q : ℝ) := by
  let x : Molecule n → ℝ := fun z => (N z : ℝ)/V
  let C : ℝ := 4*eps+(16/3)*nonfoodMass x
  have hx : ∀ z,0 ≤ x z := fun z => by dsimp [x]; positivity
  have hnf : 0 ≤ nonfoodMass x := by
    apply Finset.sum_nonneg
    intro z _
    split_ifs <;> positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hm : polymerMass x ≤ 11 := by
    rw [normalized_count_mass]
    exact (div_le_iff₀ hV).mpr hM
  have hs := collective_pair_speed_bound c (fun r => basal r) (fun r z => cat r z)
    x hx eps hb hc hfood
  have hl := collective_loss_bound
    (collectivePairSpeed c (fun r => basal r) (fun r z => cat r z) x) x hx C hC hs q
  have hlen : (molLength q : ℝ) = 4 := by exact_mod_cast hq
  rw [hlen] at hl
  have hinternal := physical_internal_loss_le_envelope q V hV c basal cat N
  have hmul := mul_le_mul_of_nonneg_right hm (mul_nonneg hC (hx q))
  have hsum : adverseCopyFlux c V basal cat N q / V ≤ (1+25*C)*x q := by
    rw [adverse_flux_decomposition c V hV basal cat N q]
    change x q + _ ≤ _
    change _ ≤ collectiveLoss (collectivePairSpeed c (fun r => basal r) (fun r z => cat r z) x) x q at hinternal
    nlinarith only [hl,hinternal,hmul]
  have hh := (div_le_iff₀ hV).mp hsum
  simpa [x,C,div_mul_cancel₀ _ (ne_of_gt hV),mul_assoc] using hh

end
end RandomViability
