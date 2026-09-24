import proofs.RandomViability.BoundedUptake
import proofs.RandomViability.BasalQuietBound
import proofs.RandomViability.UnboundedPhysicalStep

namespace RandomViability
open Classical RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 30000

def countsAtOwnMass {n : ℕ} (N : Molecule n → ℕ) : BoundedCounts n (countMass N) :=
  ⟨fun z => ⟨N z, Nat.lt_succ_of_le (count_le_countMass N z)⟩, le_rfl⟩

theorem unbounded_catalytic_ligation_rate_le {n : ℕ}
    (c : SourceMoleculeFibreConfig n) (V D : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ) (r : Reaction n) (z : Molecule n)
    (κ : ℝ) (hκ : 0 ≤ κ) (hcap : (cat r z : ℝ) ≤ κ) :
    unboundedPhysicalRate c V D basal cat N (.inr (.inr (r,z,true))) ≤
      κ*((N (reactionLeft r) : ℝ)*N (reactionRight r)*N z)/(V : ℝ)^2 := by
  have hh := bounded_catalytic_ligation_rate_le c V D hV basal cat (countsAtOwnMass N) r z
  change unboundedPhysicalRate c V D basal cat N _ ≤
    if r ∈ c z then (cat r z : ℝ)*((N (reactionLeft r) : ℝ)*N (reactionRight r)*N z)/(V : ℝ)^2 else 0 at hh
  apply hh.trans
  split_ifs
  · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcap (by positivity)) (sq_nonneg _)
  · positivity

theorem unbounded_catalytic_cleavage_rate_le {n : ℕ}
    (c : SourceMoleculeFibreConfig n) (V D : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ) (r : Reaction n) (z : Molecule n)
    (κ : ℝ) (hκ : 0 ≤ κ) (hcap : (cat r z : ℝ) ≤ κ) :
    unboundedPhysicalRate c V D basal cat N (.inr (.inr (r,z,false))) ≤
      κ*((N (reactionProduct r) : ℝ)*N z)/V := by
  unfold unboundedPhysicalRate
  split_ifs with hen
  · by_cases hs : r ∈ c z
    · unfold physicalChannelRate
      have hi : (∑ x, physicalChannelInput (.inr (.inr (r,z,false))) x) = 2 := by
        simp [physicalChannelInput, Finset.sum_add_distrib, singleCount]
      rw [hi]
      simp only [physicalChannelCoefficient, if_pos hs, physicalChannelInput, Bool.false_eq_true, if_false]
      calc
        _ ≤ ((cat r z : ℝ)*V)*((N (reactionProduct r) : ℝ)*N z)/(V : ℝ)^2 :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
            (basal_factorial_product_le N _ _) (by positivity)) (sq_nonneg _)
        _ = (cat r z : ℝ)*((N (reactionProduct r) : ℝ)*N z)/V := by field_simp
        _ ≤ _ := div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hcap (by positivity)) hV.le
    · simp only [physicalChannelRate, physicalChannelCoefficient, if_neg hs,
        NNReal.coe_zero, zero_mul, zero_div]
      positivity
  · positivity

theorem count_pair_sum_le_mass_sq {n : ℕ} (N : Molecule n → ℕ) :
    (∑ r : Reaction n, (N (reactionLeft r) : ℝ)*N (reactionRight r)) ≤ (countMass N : ℝ)^2 := by
  have hh := reaction_sum_le_ordered_pairs (fun u w => (N u : ℝ)*N w)
    (fun _ _ => by positivity)
  have hs : (∑ u, ∑ w, (N u : ℝ)*N w) = (∑ u, (N u : ℝ))^2 := by
    simp only [← Finset.mul_sum, ← Finset.sum_mul]
    ring
  have hm := concentration_le_mass (fun z => (N z : ℝ)) (fun _ => by positivity)
  have he : polymerMass (fun z => (N z : ℝ)) = countMass N := by simp [polymerMass, countMass]
  rw [he] at hm
  rw [hs] at hh
  have hn : 0 ≤ ∑ u, (N u : ℝ) := by positivity
  nlinarith

set_option maxHeartbeats 100000 in
theorem unbounded_catalytic_total_bound {n : ℕ}
    (c : SourceMoleculeFibreConfig n) (V D : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ) (κ : ℝ) (hκ : 0 ≤ κ) (hcap : ∀ r z, (cat r z : ℝ) ≤ κ) :
    (∑ r : Reaction n, ∑ z : Molecule n, ∑ d : Bool,
      unboundedPhysicalRate c V D basal cat N (.inr (.inr (r,z,d)))) ≤
      κ*((countMass N : ℝ)^3/(V : ℝ)^2+(countMass N : ℝ)^2/V) := by
  let M : ℝ := countMass N
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hs : (∑ z, (N z : ℝ)) ≤ M := by
    have hh := concentration_le_mass (fun z => (N z : ℝ)) (fun _ => by positivity)
    simpa [polymerMass, countMass, M] using hh
  have hf := count_pair_sum_le_mass_sq N
  have hb : (∑ r : Reaction n, (N (reactionProduct r) : ℝ)) ≤ M := by
    have hh := reaction_product_sum_le_mass (fun z => (N z : ℝ)) (fun _ => by positivity)
    simpa [polymerMass, countMass, M] using hh
  have hsum : (∑ r : Reaction n, ∑ z : Molecule n, ∑ d : Bool,
      unboundedPhysicalRate c V D basal cat N (.inr (.inr (r,z,d)))) ≤
      ∑ z : Molecule n, (κ*(N z : ℝ)/V*(∑ r : Reaction n, (N (reactionProduct r) : ℝ))+
        κ*(N z : ℝ)/(V : ℝ)^2*(∑ r : Reaction n, (N (reactionLeft r) : ℝ)*N (reactionRight r))) := by
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro z _
    calc
      _ ≤ ∑ r : Reaction n, (κ*((N (reactionProduct r) : ℝ)*N z)/V+
          κ*((N (reactionLeft r) : ℝ)*N (reactionRight r)*N z)/(V : ℝ)^2) := by
        apply Finset.sum_le_sum
        intro r _
        rw [Fintype.sum_bool, add_comm]
        exact add_le_add (unbounded_catalytic_cleavage_rate_le c V D hV basal cat N r z κ hκ (hcap r z))
          (unbounded_catalytic_ligation_rate_le c V D hV basal cat N r z κ hκ (hcap r z))
      _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.mul_sum]
        congr 1 <;> apply Finset.sum_congr rfl <;> intro r _ <;> ring
  calc
    _ ≤ _ := hsum
    _ ≤ ∑ z : Molecule n, (κ*(N z : ℝ)/V*M+κ*(N z : ℝ)/(V : ℝ)^2*M^2) := by
      apply Finset.sum_le_sum
      intro z _
      exact add_le_add (mul_le_mul_of_nonneg_left hb (by positivity))
        (mul_le_mul_of_nonneg_left hf (by positivity))
    _ = (κ*M/V+κ*M^2/(V : ℝ)^2)*(∑ z, (N z : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      ring
    _ ≤ (κ*M/V+κ*M^2/(V : ℝ)^2)*M := mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by dsimp [M]; ring

set_option maxHeartbeats 100000 in
/-- Dimension-free total hazard on the productive path's mass corridor.
Every ambient assignment is allowed, including food catalysts. -/
theorem unbounded_total_rate_mass_ten {n : ℕ} (hn : 2 ≤ n)
    (c : SourceMoleculeFibreConfig n) (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ) (hM : (countMass N : ℝ) ≤ 10*V)
    (hbasal : ∀ r, (basal r : ℝ) ≤ 1) (hcat : ∀ r z, (cat r z : ℝ) ≤ 16) :
    (∑ ch, unboundedPhysicalRate c V 1 basal cat N ch) ≤ 24000*V := by
  let R := unboundedPhysicalRate c V 1 basal cat N
  have hb : (∑ r : Reaction n, ∑ d : Bool, R (.inr (.inl (r,d)))) ≤ 110*V := by
    have hh := bounded_basal_intensity_cutoff_bound c V 1 hV basal cat
      (countsAtOwnMass N) 1 10 (by norm_num) (by norm_num) hbasal hM
    have he : boundedBasalIntensity c V 1 basal cat (countsAtOwnMass N) =
        ∑ r : Reaction n, ∑ d : Bool, R (.inr (.inl (r,d))) := by
      simp only [boundedBasalIntensity, Fintype.sum_sum_type, Fintype.sum_prod_type,
        isBasalChannel, if_true, if_false, Finset.sum_const_zero, zero_add, add_zero]
      rfl
    rw [he] at hh
    convert hh using 1
    ring
  have hc : (∑ r : Reaction n, ∑ z : Molecule n, ∑ d : Bool, R (.inr (.inr (r,z,d)))) ≤ 17600*V := by
    have hh := unbounded_catalytic_total_bound c V 1 hV basal cat N 16 (by norm_num) hcat
    have hM0 : 0 ≤ (countMass N : ℝ) := Nat.cast_nonneg _
    have hsq : (countMass N : ℝ)^2/V ≤ 100*V := by
      calc
        _ ≤ (10*(V : ℝ))^2/V := div_le_div_of_nonneg_right
          (pow_le_pow_left₀ hM0 hM 2) hV.le
        _ = _ := by field_simp; ring
    have hcube : (countMass N : ℝ)^3/(V : ℝ)^2 ≤ 1000*V := by
      calc
        _ ≤ (10*(V : ℝ))^3/(V : ℝ)^2 := div_le_div_of_nonneg_right
          (pow_le_pow_left₀ hM0 hM 3) (sq_nonneg _)
        _ = _ := by field_simp; ring
    change (∑ r : Reaction n, ∑ z : Molecule n, ∑ d : Bool, R (.inr (.inr (r,z,d)))) ≤ _ at hh
    linarith
  have hfeed : (∑ f : ↥(binaryFood n 2), R (.inl (.inl f))) = 6*V := by
    have hcard : Fintype.card ↥(binaryFood n 2) = 6 :=
      (Fintype.card_congr (foodWordEquiv hn)).trans (by decide)
    simp only [R, unbounded_feed_rate, NNReal.coe_one, one_mul, Finset.sum_const,
      Finset.card_univ, hcard, nsmul_eq_mul, Nat.cast_ofNat]
  have hout : (∑ z : Molecule n, R (.inl (.inr z))) ≤ 10*V := by
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
