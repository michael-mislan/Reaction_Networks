import proofs.PowerLawSmallRAF.TargetUnionConditions
import proofs.PowerLawSmallRAF.SourceLigationTargetUnion

namespace PowerLawSmallRAF
open RAF.Polymer Filter Topology
noncomputable section

/-- Compare the explicit error bound, not the adaptive production event,
when the actual high-field parameter exceeds a deterministic floor. -/
theorem source_target_union_bound_with_intensity_floor
    {p q K : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q) (hq : q ≤ 1)
    (n L m : Nat) (W : Finset LigationWord) (hK : (W.card : ℝ) ≤ K)
    (hW : ∀ w ∈ W, m ≤ w.length ∧ w.length ≤ n)
    (T : Finset (Reaction n) → Finset (Reaction n)) (hT : ∀ H, H ⊆ T H)
    (hL : 4 ≤ L) (hLm : L ≤ m) (hlarge : 32*Real.log 2 ≤ p*(L : ℝ)) :
    sourceLigationTargetsFailureMass q n L W T ≤
      K*(Real.exp (-p*(m : ℝ)/2)+2*(n : ℝ)^2*Real.exp (-p*(L : ℝ)^2/32)) := by
  have hb := source_ligation_targets_failure_bound (hp.trans hpq) hq n L m W hW T hT hL hLm
    (hlarge.trans (mul_le_mul_of_nonneg_right hpq (Nat.cast_nonneg _)))
  have h1 : Real.exp (-q*(m : ℝ)/2) ≤ Real.exp (-p*(m : ℝ)/2) := by
    apply Real.exp_le_exp.mpr
    nlinarith only [mul_nonneg (sub_nonneg.mpr hpq) (Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have h2 : Real.exp (-q*(L : ℝ)^2/32) ≤ Real.exp (-p*(L : ℝ)^2/32) := by
    apply Real.exp_le_exp.mpr
    nlinarith only [mul_nonneg (sub_nonneg.mpr hpq) (sq_nonneg (L : ℝ))]
  have he := add_le_add h1 (mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 2*(n : ℝ)^2))
  exact hb.trans ((mul_le_mul_of_nonneg_left he (Nat.cast_nonneg _)).trans
    (mul_le_mul_of_nonneg_right hK (by positivity)))

/-- Uniform source high-target bound, valid after fixing degrees/low rows.
The target set stays fixed during the high-field experiment; T may depend on it. -/
theorem source_high_target_uniform_bound :
    ∀ᶠ n : Nat in atTop, ∀ q : ℝ, targetIntensity n ≤ q → q ≤ 1 →
      ∀ W : Finset LigationWord,
      (W.card : ℝ) ≤ (n : ℝ)^3*(2 : ℝ)^(shrinkingBandWidth n) →
      (∀ w ∈ W, n-2*shrinkingBandWidth n ≤ w.length ∧ w.length ≤ n) →
      ∀ T : Finset (Reaction n) → Finset (Reaction n), (∀ H, H ⊆ T H) →
      sourceLigationTargetsFailureMass q n (targetNucleusLength n) W T ≤ highTargetError n := by
  filter_upwards [targetUnion_eventual_conditions] with n hn
  intro q hpq hq W hK hW T hT
  exact source_target_union_bound_with_intensity_floor hn.1 hpq hq n (targetNucleusLength n)
    (n-2*shrinkingBandWidth n) W hK hW T hT hn.2.2.1 hn.2.2.2.2.1 hn.2.2.2.2.2

theorem source_low_target_uniform_bound :
    ∀ᶠ n : Nat in atTop, ∀ q : ℝ, targetIntensity n ≤ q → q ≤ 1 →
      ∀ W : Finset LigationWord,
      (W.card : ℝ) ≤ (2 : ℝ)^(targetNucleusLength n+1) →
      (∀ w ∈ W, n/200 ≤ w.length ∧ w.length ≤ n) →
      ∀ T : Finset (Reaction n) → Finset (Reaction n), (∀ H, H ⊆ T H) →
      sourceLigationTargetsFailureMass q n (targetNucleusLength n) W T ≤ lowTargetError n := by
  filter_upwards [targetUnion_eventual_conditions] with n hn
  intro q hpq hq W hK hW T hT
  exact source_target_union_bound_with_intensity_floor hn.1 hpq hq n (targetNucleusLength n)
    (n/200) W hK hW T hT hn.2.2.1 hn.2.2.2.1 hn.2.2.2.2.2

end
end PowerLawSmallRAF
