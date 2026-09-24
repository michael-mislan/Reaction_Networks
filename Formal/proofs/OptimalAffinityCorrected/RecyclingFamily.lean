import proofs.OptimalAffinityCorrected.ResponseProfile

namespace OptimalAffinityCorrected

noncomputable section

/-! The response geometry of
`X <-> Y`, `m Y <-> 2 X + (m-1) Y`.
Here `m` is represented in `ℝ` for the algebraic statements; source networks
use positive integer values. -/

def recyclingResponseObjective (m t : ℝ) : ℝ :=
  (t / m) * (2 / t + (m - 1) / m)

def recyclingFamilyExpAffinity (m r : ℝ) : ℝ :=
  r + (2 - r) / m

def leakageAdjustedGain (gross productiveFraction : ℝ) : ℝ :=
  1 + productiveFraction * (gross - 1)

theorem leakageAdjustedGain_lt_gross (gross productiveFraction : ℝ)
    (hgross : 1 < gross) (hf0 : 0 ≤ productiveFraction)
    (hf1 : productiveFraction < 1) :
    1 ≤ leakageAdjustedGain gross productiveFraction ∧
      leakageAdjustedGain gross productiveFraction < gross := by
  unfold leakageAdjustedGain
  constructor
  · have hgain : 0 ≤ productiveFraction * (gross - 1) :=
      mul_nonneg hf0 (by linarith)
    linarith
  have hleak : 0 < (1 - productiveFraction) * (gross - 1) :=
    mul_pos (by linarith) (by linarith)
  nlinarith

theorem recyclingProfile_is_leakageAdjustedGain (m : ℝ) (hm : m ≠ 0) :
    (m + 1) / m = leakageAdjustedGain 2 (1 / m) := by
  unfold leakageAdjustedGain
  field_simp [hm]
  ring

theorem recyclingResponseObjective_formula (m t : ℝ)
    (hm : m ≠ 0) (ht : t ≠ 0) :
    recyclingResponseObjective m t =
      2 / m + (m - 1) * t / m ^ 2 := by
  unfold recyclingResponseObjective
  field_simp [hm, ht]

theorem recyclingResponseObjective_lower_gap (m t : ℝ)
    (hm : m ≠ 0) (ht : t ≠ 0) :
    recyclingResponseObjective m t - (m + 1) / m =
      (m - 1) * (t - m) / m ^ 2 := by
  unfold recyclingResponseObjective
  field_simp [hm, ht]
  ring

theorem recyclingResponse_lower_bound (m t : ℝ)
    (hm : 1 ≤ m) (ht : m ≤ t) :
    (m + 1) / m ≤ recyclingResponseObjective m t := by
  have hm0 : 0 < m := lt_of_lt_of_le zero_lt_one hm
  have hmne : m ≠ 0 := ne_of_gt hm0
  have ht0 : 0 < t := lt_of_lt_of_le hm0 ht
  have hcoef : 0 ≤ m - 1 := by linarith
  have htm : 0 ≤ t - m := by linarith
  have hnum : 0 ≤ (m - 1) * (t - m) := mul_nonneg hcoef htm
  have hden : 0 ≤ (m - 1) * (t - m) / m ^ 2 := div_nonneg hnum (sq_nonneg m)
  have hgap := recyclingResponseObjective_lower_gap m t hmne (ne_of_gt ht0)
  linarith

theorem recyclingFamily_formula (m r : ℝ) (hm : m ≠ 0) :
    r ≠ 0 →
    recyclingResponseObjective m (m * r) =
      recyclingFamilyExpAffinity m r := by
  intro hr
  unfold recyclingResponseObjective recyclingFamilyExpAffinity
  field_simp [hm, hr]
  ring

theorem recyclingFamily_lower_gap (m r : ℝ) (hm : m ≠ 0) :
    recyclingFamilyExpAffinity m r - (m + 1) / m =
      (m - 1) * (r - 1) / m := by
  unfold recyclingFamilyExpAffinity
  field_simp [hm]
  ring

theorem recyclingFamily_above_profile_infimum (m r : ℝ)
    (hm : 1 < m) (hr : 1 < r) :
    (m + 1) / m < recyclingFamilyExpAffinity m r := by
  have hm0 : 0 < m := lt_trans zero_lt_one hm
  have hprod : 0 < (m - 1) * (r - 1) := mul_pos (by linarith) (by linarith)
  have hfrac : 0 < (m - 1) * (r - 1) / m := div_pos hprod hm0
  have hgap := recyclingFamily_lower_gap m r (ne_of_gt hm0)
  linarith

theorem recyclingFamily_violates_gross_two (m r : ℝ)
    (hm : 1 < m) (hr : r < 2) :
    recyclingFamilyExpAffinity m r < 2 := by
  have hm0 : 0 < m := lt_trans zero_lt_one hm
  have hprod : 0 < (m - 1) * (2 - r) := mul_pos (by linarith) (by linarith)
  have hfrac : 0 < (m - 1) * (2 - r) / m := div_pos hprod hm0
  have hgap : 2 - recyclingFamilyExpAffinity m r =
      (m - 1) * (2 - r) / m := by
    unfold recyclingFamilyExpAffinity
    field_simp [ne_of_gt hm0]
    ring
  linarith

theorem recyclingFamily_exact_gap (m r : ℝ) (hm : m ≠ 0) :
    2 - recyclingFamilyExpAffinity m r =
      (m - 1) * (2 - r) / m := by
  unfold recyclingFamilyExpAffinity
  field_simp [hm]
  ring

theorem recyclingFamily_rational_reconstruction (m r : ℝ)
    (hm : m ≠ 0) (hr0 : r ≠ 0) (hr1 : r ≠ 1) (hr2 : r ≠ 2) :
    let k1p := r / (r - 1)
    let k1m := 1 / (r - 1)
    let k2m := r * m / (2 - r)
    let k2p := k2m + 1
    k1p - k1m = 1 ∧ k2p - k2m = 1 ∧
      (k1p / k1m) * (k2p / k2m) = recyclingFamilyExpAffinity m r := by
  dsimp
  constructor
  · field_simp [hr1]
  constructor
  · ring
  · unfold recyclingFamilyExpAffinity
    field_simp [hr0, hr1, hr2, hm]

theorem recyclingFamily_special_formula (m : ℝ) (hm : m ≠ 0) :
    recyclingFamilyExpAffinity m (1 + 1 / m) =
      1 + 2 / m - 1 / m ^ 2 := by
  unfold recyclingFamilyExpAffinity
  field_simp [hm]
  ring

theorem integerRecyclingFamily_exactData (m : ℕ) (hm : 2 ≤ m) :
    let mr : ℝ := m
    let r := 1 + 1 / mr
    1 < r ∧ r < 2 ∧
    (0 : ℝ) < r / (r - 1) ∧
    (0 : ℝ) < 1 / (r - 1) ∧
    (0 : ℝ) < r * mr / (2 - r) ∧
    recyclingFamilyExpAffinity mr r = 1 + 2 / mr - 1 / mr ^ 2 ∧
    recyclingFamilyExpAffinity mr r < 2 := by
  dsimp
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < (m : ℝ) := lt_of_lt_of_le (by norm_num) hmR
  have hm1 : (1 : ℝ) < (m : ℝ) := lt_of_lt_of_le (by norm_num) hmR
  have hinv : (0 : ℝ) < 1 / (m : ℝ) := one_div_pos.mpr hm0
  have hr1 : (1 : ℝ) < 1 + 1 / (m : ℝ) := by linarith
  have hr2 : 1 + 1 / (m : ℝ) < 2 := by
    have : 1 / (m : ℝ) < 1 := by
      apply (div_lt_iff₀ hm0).2
      nlinarith
    linarith
  refine ⟨hr1, hr2, ?_, ?_, ?_, ?_, ?_⟩
  · positivity
  · positivity
  · positivity
  · exact recyclingFamily_special_formula (m : ℝ) (ne_of_gt hm0)
  · exact recyclingFamily_violates_gross_two (m : ℝ) (1 + 1 / (m : ℝ)) hm1 hr2

theorem noUniformPositiveAffinityGap :
    ∀ ε : ℝ, 0 < ε →
      ∃ m : ℕ, 2 ≤ m ∧
        let r := 1 + 1 / (m : ℝ)
        1 < recyclingFamilyExpAffinity (m : ℝ) r ∧
        recyclingFamilyExpAffinity (m : ℝ) r < 1 + ε ∧
        recyclingFamilyExpAffinity (m : ℝ) r < 2 := by
  intro ε hε
  rcases exists_nat_gt (max 2 (2 / ε)) with ⟨m, hm⟩
  have hm2R : (2 : ℝ) < (m : ℝ) := lt_of_le_of_lt (le_max_left _ _) hm
  have hm2 : 2 ≤ m := by exact_mod_cast (le_of_lt hm2R)
  have hm0 : (0 : ℝ) < (m : ℝ) := lt_trans (by norm_num) hm2R
  have hm1 : (1 : ℝ) < (m : ℝ) := lt_trans (by norm_num) hm2R
  have hratio : 2 / ε < (m : ℝ) := lt_of_le_of_lt (le_max_right _ _) hm
  have htwo : (2 : ℝ) < ε * (m : ℝ) := by
    have := (div_lt_iff₀ hε).mp hratio
    nlinarith
  have hsmall : 2 / (m : ℝ) < ε := by
    exact (div_lt_iff₀ hm0).2 (by nlinarith)
  refine ⟨m, hm2, ?_, ?_, ?_⟩
  · have hinvpos : (0 : ℝ) < 1 / (m : ℝ) := one_div_pos.mpr hm0
    have hr1 : (1 : ℝ) < 1 + 1 / (m : ℝ) := by linarith
    have habove := recyclingFamily_above_profile_infimum
      (m : ℝ) (1 + 1 / (m : ℝ)) hm1 hr1
    have hbase : (1 : ℝ) < ((m : ℝ) + 1) / (m : ℝ) := by
      have hform : ((m : ℝ) + 1) / (m : ℝ) = 1 + 1 / (m : ℝ) := by
        field_simp [ne_of_gt hm0]
      rw [hform]
      exact hr1
    exact hbase.trans habove
  · rw [recyclingFamily_special_formula (m : ℝ) (ne_of_gt hm0)]
    have hsquare : (0 : ℝ) < 1 / (m : ℝ) ^ 2 := by positivity
    linarith
  · have hr2 : 1 + 1 / (m : ℝ) < 2 := by
      have hinv : 1 / (m : ℝ) < 1 := by
        apply (div_lt_iff₀ hm0).2
        nlinarith
      linarith
    exact recyclingFamily_violates_gross_two (m : ℝ)
      (1 + 1 / (m : ℝ)) hm1 hr2

end
end OptimalAffinityCorrected
