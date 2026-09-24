import proofs.RandomViability.CollectiveCountVariance

namespace RandomViability
open Classical RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 100000

/-- Total hazard on the collective trajectory's mass corridor. -/
theorem unbounded_total_rate_mass_eleven {n : ℕ} (hn : 2 ≤ n)
    (c : SourceMoleculeFibreConfig n) (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ) (hM : (countMass N : ℝ) ≤ 11*V)
    (hbasal : ∀ r, (basal r : ℝ) ≤ 1) (hcat : ∀ r z, (cat r z : ℝ) ≤ 16) :
    (∑ ch, unboundedPhysicalRate c V 1 basal cat N ch) ≤ 24000*V := by
  let R := unboundedPhysicalRate c V 1 basal cat N
  have hb : (∑ r : Reaction n, ∑ d : Bool, R (.inr (.inl (r,d)))) ≤ 132*V := by
    have hh := bounded_basal_intensity_cutoff_bound c V 1 hV basal cat
      (countsAtOwnMass N) 1 11 (by norm_num) (by norm_num) hbasal hM
    have he : boundedBasalIntensity c V 1 basal cat (countsAtOwnMass N) =
        ∑ r : Reaction n, ∑ d : Bool, R (.inr (.inl (r,d))) := by
      simp only [boundedBasalIntensity, Fintype.sum_sum_type, Fintype.sum_prod_type,
        isBasalChannel, if_true, if_false, Finset.sum_const_zero, zero_add, add_zero]
      rfl
    rw [he] at hh
    convert hh using 1
    ring
  have hc : (∑ r : Reaction n, ∑ z : Molecule n, ∑ d : Bool, R (.inr (.inr (r,z,d)))) ≤ 23232*V := by
    have hh := unbounded_catalytic_total_bound c V 1 hV basal cat N 16 (by norm_num) hcat
    have hM0 : 0 ≤ (countMass N : ℝ) := Nat.cast_nonneg _
    have hsq : (countMass N : ℝ)^2/V ≤ 121*V := by
      calc
        _ ≤ (11*(V : ℝ))^2/V := div_le_div_of_nonneg_right
          (pow_le_pow_left₀ hM0 hM 2) hV.le
        _ = _ := by field_simp; ring
    have hcube : (countMass N : ℝ)^3/(V : ℝ)^2 ≤ 1331*V := by
      calc
        _ ≤ (11*(V : ℝ))^3/(V : ℝ)^2 := div_le_div_of_nonneg_right
          (pow_le_pow_left₀ hM0 hM 3) (sq_nonneg _)
        _ = _ := by field_simp; ring
    change (∑ r : Reaction n, ∑ z : Molecule n, ∑ d : Bool, R (.inr (.inr (r,z,d)))) ≤ _ at hh
    linarith
  have hfeed : (∑ f : ↥(binaryFood n 2), R (.inl (.inl f))) = 6*V := by
    have hcard : Fintype.card ↥(binaryFood n 2) = 6 :=
      (Fintype.card_congr (foodWordEquiv hn)).trans (by decide)
    simp only [R, unbounded_feed_rate, NNReal.coe_one, one_mul, Finset.sum_const,
      Finset.card_univ, hcard, nsmul_eq_mul, Nat.cast_ofNat]
  have hout : (∑ z : Molecule n, R (.inl (.inr z))) ≤ 11*V := by
    have he (z : Molecule n) : R (.inl (.inr z)) = (N z : ℝ) := by
      have hh := bounded_outflow_rate c V 1 hV basal cat (countsAtOwnMass N) z
      change R (.inl (.inr z)) = (1 : ℝ)*(N z : ℝ) at hh
      simpa only [one_mul] using hh
    simp_rw [he]
    have hh := concentration_le_mass (fun z => (N z : ℝ)) (fun _ => by positivity)
    have hm : polymerMass (fun z => (N z : ℝ)) = countMass N := by simp [polymerMass, countMass]
    rw [hm] at hh
    exact hh.trans hM
  change (∑ ch, R ch) ≤ _
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [Fintype.sum_prod_type]
  rw [hfeed]
  linarith

end
end RandomViability
