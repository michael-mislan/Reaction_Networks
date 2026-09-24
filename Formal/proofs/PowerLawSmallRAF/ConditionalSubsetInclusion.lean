import proofs.PowerLawSmallRAF.SeedClosed

namespace PowerLawSmallRAF

/-- Probability that a uniformly sampled `d`-subset of an `R`-set contains a
specified `s`-subset. -/
noncomputable def hypergeometricContain (R s d : Nat) : ℝ :=
  (Nat.choose (R - s) (d - s) : ℝ) / Nat.choose R d

/-- The containment probability is symmetric in the sampled and required
subsets. -/
theorem hypergeometricContain_eq_symmetricChoose
    (R s d : Nat) (hsd : s ≤ d) (hdR : d ≤ R) :
    hypergeometricContain R s d =
      (Nat.choose d s : ℝ) / Nat.choose R s := by
  have hcross : Nat.choose R d * Nat.choose d s =
      Nat.choose R s * Nat.choose (R - s) (d - s) :=
    Nat.choose_mul (n := R) (k := d) (s := s) hsd
  have hdenD : (Nat.choose R d : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos hdR))
  have hdenS : (Nat.choose R s : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos (hsd.trans hdR)))
  dsimp [hypergeometricContain]
  field_simp [hdenD, hdenS]
  have hcross' : Nat.choose (R - s) (d - s) * Nat.choose R s =
      Nat.choose R d * Nat.choose d s := by
    simpa only [mul_comm] using hcross.symm
  exact_mod_cast hcross'

/-- Product form of sampling without replacement. -/
noncomputable def hypergeometricContainProduct (R s d : Nat) : ℝ :=
  ∏ j ∈ Finset.range s,
    (((d - j : Nat) : ℝ) / (R - j : Nat))

theorem hypergeometricContain_eq_product
    (R s d : Nat) (hsd : s ≤ d) (hdR : d ≤ R) :
    hypergeometricContain R s d =
      hypergeometricContainProduct R s d := by
  rw [hypergeometricContain_eq_symmetricChoose R s d hsd hdR]
  have hgateway := symmetricChooseRatio_eq_gatewayMissProduct
    R s (R - d) (by omega)
  have hchoose : R - (R - d) = d := Nat.sub_sub_self hdR
  rw [hchoose] at hgateway
  rw [hgateway]
  dsimp [gatewayMissProduct, hypergeometricContainProduct]
  apply Finset.prod_congr rfl
  intro j hj
  have hjs : j < s := Finset.mem_range.mp hj
  congr 2
  omega

/-- A without-replacement containment probability is bounded by a geometric
power at the worst denominator in the required block. -/
theorem hypergeometricContain_le_power
    (R s d : Nat) (hsd : s ≤ d) (hdR : d ≤ R)
    (hsR : s ≤ R) :
    hypergeometricContain R s d ≤
      ((d : ℝ) / (R - s + 1 : Nat)) ^ s := by
  rw [hypergeometricContain_eq_product R s d hsd hdR,
    hypergeometricContainProduct]
  rw [show ((d : ℝ) / (R - s + 1 : Nat)) ^ s =
      ∏ _j ∈ Finset.range s, ((d : ℝ) / (R - s + 1 : Nat)) by
        rw [div_pow]
        simp]
  apply Finset.prod_le_prod
  · intro j hj
    exact div_nonneg (by positivity) (by positivity)
  · intro j hj
    have hjs : j < s := Finset.mem_range.mp hj
    have hdenpos : (0 : ℝ) < (R - j : Nat) := by
      exact_mod_cast (by omega : 0 < R - j)
    have hworstpos : (0 : ℝ) < (R - s + 1 : Nat) := by
      exact_mod_cast (by omega : 0 < R - s + 1)
    apply (div_le_div_iff₀ hdenpos hworstpos).2
    have hnum : ((d - j : Nat) : ℝ) ≤ (d : ℝ) := by
      exact_mod_cast Nat.sub_le d j
    have hden : ((R - s + 1 : Nat) : ℝ) ≤ (R - j : Nat) := by
      exact_mod_cast (by omega : R - s + 1 ≤ R - j)
    calc
      ((d - j : Nat) : ℝ) * (R - s + 1 : Nat) ≤
          (d : ℝ) * (R - s + 1 : Nat) :=
        mul_le_mul_of_nonneg_right hnum hworstpos.le
      _ ≤ (d : ℝ) * (R - j : Nat) :=
        mul_le_mul_of_nonneg_left hden (by positivity)

/-- After one specified gateway edge has been forced, `d-1` positions remain
uniformly distributed over the other `R-1` channels. -/
noncomputable def gatewayConditionedContain (R q d : Nat) : ℝ :=
  hypergeometricContain (R - 1) q (d - 1)

theorem gatewayConditionedContain_eq_symmetricChoose
    (R q d : Nat) (hd : 1 ≤ d) (hdR : d ≤ R) (hq : q ≤ d - 1) :
    gatewayConditionedContain R q d =
      (Nat.choose (d - 1) q : ℝ) / Nat.choose (R - 1) q := by
  exact hypergeometricContain_eq_symmetricChoose
    (R - 1) q (d - 1) hq (by omega)

theorem gatewayConditionedContain_le_power
    (R q d : Nat) (hd : 1 ≤ d) (hdR : d ≤ R) (hq : q ≤ d - 1) :
    gatewayConditionedContain R q d ≤
      (((d - 1 : Nat) : ℝ) / (R - q : Nat)) ^ q := by
  have hqR : q ≤ R - 1 := by omega
  have h := hypergeometricContain_le_power
    (R - 1) q (d - 1) hq (by omega) hqR
  have hden : R - 1 - q + 1 = R - q := by omega
  simpa only [gatewayConditionedContain, hden] using h

end PowerLawSmallRAF
