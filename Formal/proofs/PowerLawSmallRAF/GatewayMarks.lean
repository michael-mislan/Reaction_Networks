import proofs.PowerLawSmallRAF.DegreeBands
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace PowerLawSmallRAF

open Filter Topology

/-- Bayes' rule for a uniformly specified potential catalytic edge.  If a
molecule has degree `d`, that edge is present with probability `d / R`; hence
conditioning on the edge size-biases the degree law exactly. -/
theorem conditionalSpecifiedEdgeMass_eq_sizeBiased
    (mass degree meanDegree R : ℝ) (hmean : meanDegree ≠ 0) (hR : R ≠ 0) :
    (mass * (degree / R)) / (meanDegree / R) =
      degree * mass / meanDegree := by
  field_simp

/-- The interior mass of the capped Zipf degree law.  A Zipf mark `k < R`
produces catalytic degree `k - 1`. -/
noncomputable def cappedZipfInteriorMass (a : ℝ) (k : Nat) : ℝ :=
  (k : ℝ) ^ (-a) / zipfNormalizer a

/-- Exact conditional law at an interior Zipf mark after requiring one fixed
catalytic edge.  This is the finite-model size-biased distribution, before
any asymptotics are taken. -/
theorem cappedZipfInterior_givenSpecifiedEdge
    (a : ℝ) (R k : Nat) (hR : R ≠ 0)
    (hnum : windowDirectNumerator a R ≠ 0)
    (hden : zipfNormalizer a ≠ 0) :
    (cappedZipfInteriorMass a k * (((k - 1 : Nat) : ℝ) / (R : ℝ))) /
        (windowZipfMean a R / (R : ℝ)) =
      (((k - 1 : Nat) : ℝ) * (k : ℝ) ^ (-a)) /
        windowDirectNumerator a R := by
  rw [cappedZipfInteriorMass, windowZipfMean]
  have hRreal : (R : ℝ) ≠ 0 := by exact_mod_cast hR
  field_simp [hRreal, hnum, hden]

/-- Exponential-coordinate limit at a general moving degree threshold. -/
theorem movingThresholdRpow_window
    (m : Nat → Nat) (b ell : ℝ)
    (hlog : Tendsto (fun n : Nat => Real.log (m n : ℝ) / (n : ℝ))
      atTop (𝓝 ell))
    (hm : Tendsto m atTop atTop) :
    Tendsto (fun n : Nat => (m n : ℝ) ^ (-b / (n : ℝ))) atTop
      (𝓝 (Real.exp (-b * ell))) := by
  have hprod : Tendsto (fun n : Nat =>
      (-b) * (Real.log (m n : ℝ) / (n : ℝ))) atTop
      (𝓝 (-b * ell)) := tendsto_const_nhds.mul hlog
  have hexp := Real.continuous_exp.continuousAt.tendsto.comp hprod
  apply hexp.congr'
  filter_upwards [eventually_ge_atTop 1,
    hm.eventually (eventually_gt_atTop 0)] with n hn hmn
  rw [Real.rpow_def_of_pos (by exact_mod_cast hmn)]
  apply congrArg Real.exp
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  field_simp [hn0]

theorem movingWindowIntegral_eq (m : Nat → Nat) (b : ℝ) (hb : b ≠ 0)
    (n : Nat) (hn : 1 ≤ n) (hm : 1 ≤ m n) :
    (∫ x in (1 : ℝ)..(m n : ℝ), x ^ (-(1 + b / (n : ℝ)))) /
        (n : ℝ) =
      (1 - (m n : ℝ) ^ (-b / (n : ℝ))) / b := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hmreal : (1 : ℝ) ≤ (m n : ℝ) := by exact_mod_cast hm
  have hr : -(1 + b / (n : ℝ)) ≠ -1 := by
    intro h
    have hd : b / (n : ℝ) = 0 := by linarith
    exact hb ((div_eq_zero_iff.mp hd).resolve_right hn0)
  have hzero : (0 : ℝ) ∉ Set.uIcc (1 : ℝ) (m n : ℝ) := by
    rw [Set.uIcc_of_le hmreal]
    simp
  rw [integral_rpow (Or.inr ⟨hr, hzero⟩), Real.one_rpow]
  rw [show -(1 + b / (n : ℝ)) + 1 = -b / (n : ℝ) by ring]
  field_simp [hb, hn0]
  ring

/-- A logarithmic degree band has a nondegenerate amount of size-biased mass
throughout the critical exponent window. -/
theorem movingTiltedHarmonic_window_normalized_of_ne_zero
    (m : Nat → Nat) (b ell : ℝ) (hb : b ≠ 0)
    (hlog : Tendsto (fun n : Nat => Real.log (m n : ℝ) / (n : ℝ))
      atTop (𝓝 ell))
    (hm : Tendsto m atTop atTop) :
    Tendsto (fun n : Nat =>
      tiltedHarmonic (1 + b / (n : ℝ)) (m n) / (n : ℝ)) atTop
      (𝓝 ((1 - Real.exp (-b * ell)) / b)) := by
  have hrpow := movingThresholdRpow_window m b ell hlog hm
  have hI : Tendsto (fun n : Nat =>
      (∫ x in (1 : ℝ)..(m n : ℝ), x ^ (-(1 + b / (n : ℝ)))) /
        (n : ℝ)) atTop (𝓝 ((1 - Real.exp (-b * ell)) / b)) := by
    have hmain : Tendsto (fun n : Nat =>
        ((1 : ℝ) - (m n : ℝ) ^ (-b / (n : ℝ))) / b) atTop
        (𝓝 ((1 - Real.exp (-b * ell)) / b)) :=
      ((tendsto_const_nhds : Tendsto (fun _ : Nat => (1 : ℝ)) atTop (𝓝 1)).sub
        hrpow).div_const b
    apply hmain.congr'
    filter_upwards [eventually_ge_atTop 1,
      hm.eventually (eventually_ge_atTop 1)] with n hn hmn
    exact (movingWindowIntegral_eq m b hb n hn hmn).symm
  have honeDiv : Tendsto (fun n : Nat => (1 : ℝ) / (n : ℝ))
      atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop (R := ℝ))
  have hu : Tendsto (fun n : Nat =>
      (∫ x in (1 : ℝ)..(m n : ℝ), x ^ (-(1 + b / (n : ℝ)))) /
        (n : ℝ) + 1 / (n : ℝ)) atTop
      (𝓝 ((1 - Real.exp (-b * ell)) / b)) := by
    simpa only [add_zero] using hI.add honeDiv
  have hpT : Tendsto (fun n : Nat => 1 + b / (n : ℝ)) atTop (𝓝 1) := by
    have hbn : Tendsto (fun n : Nat => b / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa only [add_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : Nat => (1 : ℝ)) atTop (𝓝 1)).add hbn
  have hpEv : ∀ᶠ n : Nat in atTop, 0 < 1 + b / (n : ℝ) :=
    hpT (Ioi_mem_nhds zero_lt_one)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hI hu
  · filter_upwards [eventually_ge_atTop 1, hpEv,
      hm.eventually (eventually_ge_atTop 2)] with n hn hp hmn
    exact div_le_div_of_nonneg_right
      (tiltedHarmonic_integral_bounds (1 + b / (n : ℝ)) hp (m n) hmn).1
      (by positivity)
  · filter_upwards [eventually_ge_atTop 1, hpEv,
      hm.eventually (eventually_ge_atTop 2)] with n hn hp hmn
    have hbound :=
      (tiltedHarmonic_integral_bounds (1 + b / (n : ℝ)) hp (m n) hmn).2
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    calc
      tiltedHarmonic (1 + b / (n : ℝ)) (m n) / (n : ℝ) ≤
          (1 + ∫ x in (1 : ℝ)..(m n : ℝ),
            x ^ (-(1 + b / (n : ℝ)))) / (n : ℝ) :=
              div_le_div_of_nonneg_right hbound (by positivity)
      _ = (∫ x in (1 : ℝ)..(m n : ℝ),
            x ^ (-(1 + b / (n : ℝ)))) / (n : ℝ) + 1 / (n : ℝ) := by
              field_simp
              ring

/-- Unnormalised size-biased mass below a strict Zipf-mark threshold. -/
noncomputable def windowPartialNumerator (a : ℝ) (M : Nat) : ℝ :=
  ∑ k ∈ Finset.Ico 2 M,
    (((k - 1 : Nat) : ℝ) * (k : ℝ) ^ (-a))

theorem windowPartialNumerator_eq (a : ℝ) (M : Nat) (hM : 2 ≤ M) :
    windowPartialNumerator a M =
      tiltedHarmonic (a - 1) M - 1 -
        ∑ k ∈ Finset.Ico 2 M, (k : ℝ) ^ (-a) := by
  have hdirect := windowDirectNumerator_eq a M hM
  rw [windowDirectNumerator] at hdirect
  dsimp [windowPartialNumerator]
  linarith

theorem movingWindowInterior_normalized
    (m : Nat → Nat) (b : ℝ) :
    Tendsto (fun n : Nat =>
      (∑ k ∈ Finset.Ico 2 (m n),
        (k : ℝ) ^ (-(2 + b / (n : ℝ)))) / (n : ℝ))
      atTop (𝓝 0) := by
  have hupper := (zipfNormalizer_source_window b).div_atTop
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have haT : Tendsto (fun n : Nat => 2 + b / (n : ℝ)) atTop (𝓝 2) := by
    have hbn : Tendsto (fun n : Nat => b / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa only [add_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : Nat => (2 : ℝ)) atTop (𝓝 2)).add hbn
  have haEv : ∀ᶠ n : Nat in atTop, 1 < 2 + b / (n : ℝ) :=
    haT (Ioi_mem_nhds one_lt_two)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _ : Nat => (0 : ℝ)) atTop (𝓝 0)) hupper
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact div_nonneg (windowInterior_nonneg _ _) (by positivity)
  · filter_upwards [eventually_ge_atTop 1, haEv] with n hn ha
    exact div_le_div_of_nonneg_right
      (windowInterior_le_normalizer (2 + b / (n : ℝ)) ha (m n)) (by positivity)

theorem movingWindowPartialNumerator_normalized_of_ne_zero
    (m : Nat → Nat) (b ell : ℝ) (hb : b ≠ 0)
    (hlog : Tendsto (fun n : Nat => Real.log (m n : ℝ) / (n : ℝ))
      atTop (𝓝 ell))
    (hm : Tendsto m atTop atTop) :
    Tendsto (fun n : Nat =>
      windowPartialNumerator (2 + b / (n : ℝ)) (m n) / (n : ℝ)) atTop
      (𝓝 ((1 - Real.exp (-b * ell)) / b)) := by
  have htilt := movingTiltedHarmonic_window_normalized_of_ne_zero m b ell hb hlog hm
  have hone : Tendsto (fun n : Nat => (1 : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop (R := ℝ))
  have hinterior := movingWindowInterior_normalized m b
  have hcombined := htilt.sub hone |>.sub hinterior
  have hlimit : Tendsto (fun n : Nat =>
      tiltedHarmonic (1 + b / (n : ℝ)) (m n) / (n : ℝ) - 1 / (n : ℝ) -
        (∑ k ∈ Finset.Ico 2 (m n),
          (k : ℝ) ^ (-(2 + b / (n : ℝ)))) / (n : ℝ)) atTop
      (𝓝 ((1 - Real.exp (-b * ell)) / b)) := by
    simpa only [sub_zero] using hcombined
  apply hlimit.congr'
  filter_upwards [eventually_ge_atTop 1,
    hm.eventually (eventually_ge_atTop 2)] with n hn hmn
  rw [windowPartialNumerator_eq (2 + b / (n : ℝ)) (m n) hmn]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  ring_nf

/-- Cumulative size-biased mass below `M`; equivalently, the conditional CDF
given a uniformly specified catalytic edge. -/
noncomputable def sizeBiasedLogCdf (a : ℝ) (R M : Nat) : ℝ :=
  windowPartialNumerator a M / windowDirectNumerator a R

theorem sizeBiasedLogCdf_source_window_of_ne_zero
    (m : Nat → Nat) (b ell : ℝ) (hb : b ≠ 0)
    (hlog : Tendsto (fun n : Nat => Real.log (m n : ℝ) / (n : ℝ))
      atTop (𝓝 ell))
    (hm : Tendsto m atTop atTop) :
    Tendsto (fun n : Nat => sizeBiasedLogCdf (2 + b / (n : ℝ))
      (sourceReactionCount n) (m n)) atTop
      (𝓝 (((1 - Real.exp (-b * ell)) / b) /
        ((1 - (2 : ℝ) ^ (-b)) / b))) := by
  have hpartial := movingWindowPartialNumerator_normalized_of_ne_zero
    m b ell hb hlog hm
  have htotal := windowDirectNumerator_source_window_normalized b hb
  have hpowne : (2 : ℝ) ^ (-b) ≠ 1 := by
    intro hpow
    have hexp : Real.exp (-b * Real.log 2) = 1 := by
      calc
        Real.exp (-b * Real.log 2) = Real.exp (Real.log 2 * (-b)) := by ring_nf
        _ = (2 : ℝ) ^ (-b) :=
          (Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2) (-b)).symm
        _ = 1 := hpow
    have harg : -b * Real.log 2 = 0 :=
      Real.exp_injective (by simpa only [Real.exp_zero] using hexp)
    have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
    rcases mul_eq_zero.mp harg with hbzero | hlogzero
    · exact hb (neg_eq_zero.mp hbzero)
    · exact (ne_of_gt hlog2) hlogzero
  have htotalne : (1 - (2 : ℝ) ^ (-b)) / b ≠ 0 := by
    apply div_ne_zero _ hb
    exact sub_ne_zero.mpr hpowne.symm
  have hquot := hpartial.div htotal htotalne
  apply hquot.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  dsimp [sizeBiasedLogCdf]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  field_simp [hn0]

/-- Exact identification of the harmonic endpoint of a logarithmic band. -/
theorem tiltedHarmonic_one_succ (M : Nat) :
    tiltedHarmonic 1 (M + 1) = (harmonic M : ℝ) := by
  rw [tiltedHarmonic, harmonic_eq_sum_Icc, Rat.cast_sum]
  have hsets : Finset.Ico 1 (M + 1) = Finset.Icc 1 M := by
    ext k
    simp only [Finset.mem_Ico, Finset.mem_Icc]
    omega
  rw [hsets]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Real.rpow_neg_one, Rat.cast_inv, Rat.cast_natCast]

/-- At the removable critical coordinate `b=0`, size-biased degree is uniform
on logarithmic scale.  Writing the threshold as a successor makes its exact
harmonic representation visible. -/
theorem movingWindowPartialNumerator_two_succ_normalized
    (m : Nat → Nat) (ell : ℝ)
    (hlog : Tendsto (fun n : Nat => Real.log (m n : ℝ) / (n : ℝ))
      atTop (𝓝 ell))
    (hm : Tendsto m atTop atTop) :
    Tendsto (fun n : Nat => windowPartialNumerator 2 (m n + 1) / (n : ℝ))
      atTop (𝓝 ell) := by
  have herr := Real.tendsto_harmonic_sub_log.comp hm
  have herrDiv := herr.div_atTop (tendsto_natCast_atTop_atTop (R := ℝ))
  have hharm : Tendsto (fun n : Nat => (harmonic (m n) : ℝ) / (n : ℝ))
      atTop (𝓝 ell) := by
    have hsum := herrDiv.add hlog
    apply (show Tendsto (fun n : Nat =>
      ((harmonic (m n) : ℝ) - Real.log (m n : ℝ)) / (n : ℝ) +
        Real.log (m n : ℝ) / (n : ℝ)) atTop (𝓝 ell) by
          simpa only [zero_add] using hsum).congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    field_simp [hn0]
    ring
  have hone : Tendsto (fun n : Nat => (1 : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop (R := ℝ))
  have hinterior := movingWindowInterior_normalized (fun n => m n + 1) 0
  have hcombined := hharm.sub hone |>.sub hinterior
  have hlimit : Tendsto (fun n : Nat =>
      tiltedHarmonic 1 (m n + 1) / (n : ℝ) - 1 / (n : ℝ) -
        (∑ k ∈ Finset.Ico 2 (m n + 1), (k : ℝ) ^ (-(2 : ℝ))) / (n : ℝ))
      atTop (𝓝 ell) := by
    simpa only [sub_zero, zero_div, add_zero, tiltedHarmonic_one_succ] using hcombined
  apply hlimit.congr'
  filter_upwards [eventually_ge_atTop 1,
    hm.eventually (eventually_ge_atTop 1)] with n hn hmn
  rw [windowPartialNumerator_eq 2 (m n + 1) (by omega)]
  ring_nf

theorem sizeBiasedLogCdf_source_window_zero
    (m : Nat → Nat) (ell : ℝ)
    (hlog : Tendsto (fun n : Nat => Real.log (m n : ℝ) / (n : ℝ))
      atTop (𝓝 ell))
    (hm : Tendsto m atTop atTop) :
    Tendsto (fun n : Nat => sizeBiasedLogCdf 2
      (sourceReactionCount n) (m n + 1)) atTop
      (𝓝 (ell / Real.log 2)) := by
  have hpartial := movingWindowPartialNumerator_two_succ_normalized m ell hlog hm
  have htotal : Tendsto (fun n : Nat =>
      windowDirectNumerator 2 (sourceReactionCount n) / (n : ℝ)) atTop
      (𝓝 (Real.log 2)) := by
    apply directCriticalCappedNumerator_source_normalized.congr'
    filter_upwards with n
    rw [windowDirectNumerator_two_eq]
  have hlogne : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos one_lt_two)
  have hquot := hpartial.div htotal hlogne
  apply hquot.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  dsimp [sizeBiasedLogCdf]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  field_simp [hn0]

/-- Fraction of total expected catalytic degree contributed by an interior
logarithmic mark band `[L,U)`.  Equivalently, this is the size-biased mass of
that band. -/
noncomputable def sizeBiasedLogBand
    (a : ℝ) (R L U : Nat) : ℝ :=
  sizeBiasedLogCdf a R U - sizeBiasedLogCdf a R L

theorem sizeBiasedLogBand_source_window_of_ne_zero
    (lo hi : Nat → Nat) (b ellLo ellHi : ℝ) (hb : b ≠ 0)
    (hlogLo : Tendsto (fun n : Nat => Real.log (lo n : ℝ) / (n : ℝ))
      atTop (𝓝 ellLo))
    (hlogHi : Tendsto (fun n : Nat => Real.log (hi n : ℝ) / (n : ℝ))
      atTop (𝓝 ellHi))
    (hlo : Tendsto lo atTop atTop) (hhi : Tendsto hi atTop atTop) :
    Tendsto (fun n : Nat => sizeBiasedLogBand (2 + b / (n : ℝ))
      (sourceReactionCount n) (lo n) (hi n)) atTop
      (𝓝 (((1 - Real.exp (-b * ellHi)) / b) /
          ((1 - (2 : ℝ) ^ (-b)) / b) -
        ((1 - Real.exp (-b * ellLo)) / b) /
          ((1 - (2 : ℝ) ^ (-b)) / b))) := by
  simpa only [sizeBiasedLogBand] using
    (sizeBiasedLogCdf_source_window_of_ne_zero hi b ellHi hb hlogHi hhi).sub
      (sizeBiasedLogCdf_source_window_of_ne_zero lo b ellLo hb hlogLo hlo)

theorem sizeBiasedLogBand_source_window_zero
    (lo hi : Nat → Nat) (ellLo ellHi : ℝ)
    (hlogLo : Tendsto (fun n : Nat => Real.log (lo n : ℝ) / (n : ℝ))
      atTop (𝓝 ellLo))
    (hlogHi : Tendsto (fun n : Nat => Real.log (hi n : ℝ) / (n : ℝ))
      atTop (𝓝 ellHi))
    (hlo : Tendsto lo atTop atTop) (hhi : Tendsto hi atTop atTop) :
    Tendsto (fun n : Nat => sizeBiasedLogBand 2
      (sourceReactionCount n) (lo n + 1) (hi n + 1)) atTop
      (𝓝 (ellHi / Real.log 2 - ellLo / Real.log 2)) := by
  simpa only [sizeBiasedLogBand] using
    (sizeBiasedLogCdf_source_window_zero hi ellHi hlogHi hhi).sub
      (sizeBiasedLogCdf_source_window_zero lo ellLo hlogLo hlo)

/-- Every set of at most `k` candidate hubs is controlled by a threshold term
plus the cumulative mass of the ambient high-degree tail.  This avoids naming
or sorting order statistics and therefore applies, in particular, to the
actual top-`k` set. -/
theorem hubSetMass_le_threshold_add_highMass
    {A : Type*} [DecidableEq A] (U H : Finset A) (w : A → ℝ)
    (k : Nat) (t : ℝ) (ht : 0 ≤ t) (hHU : H ⊆ U) (hcard : H.card ≤ k)
    (hw : ∀ x ∈ U, 0 ≤ w x) :
    ∑ x ∈ H, w x ≤
      (k : ℝ) * t + ∑ x ∈ U.filter (fun x => t < w x), w x := by
  let highH := H.filter (fun x => t < w x)
  let lowH := H.filter (fun x => ¬ t < w x)
  let highU := U.filter (fun x => t < w x)
  have hsplit : ∑ x ∈ H, w x =
      (∑ x ∈ highH, w x) + ∑ x ∈ lowH, w x := by
    dsimp [highH, lowH]
    simpa only [not_lt] using
      (Finset.sum_filter_add_sum_filter_not H (fun x => t < w x) w).symm
  have hhighSub : highH ⊆ highU := by
    intro x hx
    have hx' := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨hHU hx'.1, hx'.2⟩
  have hhigh : ∑ x ∈ highH, w x ≤ ∑ x ∈ highU, w x := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hhighSub
    intro x hxU hxH
    exact hw x (Finset.mem_filter.mp hxU).1
  have hlow : ∑ x ∈ lowH, w x ≤ (lowH.card : ℝ) * t := by
    have h := Finset.sum_le_card_nsmul lowH w t
      (fun x hx => le_of_not_gt (Finset.mem_filter.mp hx).2)
    simpa only [nsmul_eq_mul, Nat.cast_ofNat, Nat.cast_id] using h
  have hlowCard : (lowH.card : ℝ) ≤ (k : ℝ) := by
    have hlowSub : lowH ⊆ H := by
      dsimp [lowH]
      exact Finset.filter_subset _ _
    exact_mod_cast ((Finset.card_le_card hlowSub).trans hcard)
  rw [hsplit]
  nlinarith

theorem tendsto_log_one_sub_div :
    Tendsto (fun x : ℝ => Real.log (1 - x) / x) (𝓝[≠] 0) (𝓝 (-1)) := by
  have hinner : HasDerivAt (fun x : ℝ => 1 - x) (-1) 0 := by
    convert (hasDerivAt_const (𝕜 := ℝ) (F := ℝ) 0 (1 : ℝ)).sub
      (hasDerivAt_id' (𝕜 := ℝ) 0) using 1
    norm_num
  have houter : HasDerivAt Real.log 1 (1 - (0 : ℝ)) := by
    simpa using Real.hasDerivAt_log (by norm_num : (1 : ℝ) ≠ 0)
  have hd : HasDerivAt (fun x : ℝ => Real.log (1 - x)) (-1) 0 := by
    convert houter.comp 0 hinner using 1
    norm_num
  simpa [slope, Real.log_one, div_eq_mul_inv, mul_comm] using hd.tendsto_slope_zero

/-- Binomial zero-count limit in the rare-event regime. -/
theorem binomialNoHit_tendsto_exp_neg
    (N : Nat → Nat) (p : Nat → ℝ) (theta : ℝ)
    (hp : Tendsto p atTop (𝓝 0))
    (hpne : ∀ᶠ n : Nat in atTop, p n ≠ 0)
    (hplt : ∀ᶠ n : Nat in atTop, p n < 1)
    (hNp : Tendsto (fun n : Nat => (N n : ℝ) * p n) atTop (𝓝 theta)) :
    Tendsto (fun n : Nat => (1 - p n) ^ (N n)) atTop
      (𝓝 (Real.exp (-theta))) := by
  have hp' : Tendsto p atTop (𝓝[≠] 0) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hp, by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hpne⟩
  have hratio : Tendsto (fun n : Nat => Real.log (1 - p n) / p n)
      atTop (𝓝 (-1)) := tendsto_log_one_sub_div.comp hp'
  have hlogprod : Tendsto (fun n : Nat =>
      (N n : ℝ) * Real.log (1 - p n)) atTop (𝓝 (-theta)) := by
    have h := hNp.mul hratio
    apply (show Tendsto (fun n : Nat =>
      ((N n : ℝ) * p n) * (Real.log (1 - p n) / p n))
        atTop (𝓝 (-theta)) by simpa only [mul_neg, mul_one] using h).congr'
    filter_upwards [hpne] with n hpn
    field_simp [hpn]
  have hexp := Real.continuous_exp.continuousAt.tendsto.comp hlogprod
  apply hexp.congr'
  filter_upwards [hplt] with n hpn
  have hbase : 0 < 1 - p n := sub_pos.mpr hpn
  rw [← Real.rpow_natCast]
  rw [Real.rpow_def_of_pos hbase]
  apply congrArg Real.exp
  ring

/-- No molecule reaches the molecule-count degree scale.  Under independent
degree draws this is exactly the binomial zero-count probability. -/
theorem calibratedNoMoleculeScaleCatalyst
    (lam : ℝ) (hlam : 0 < lam) :
    Tendsto (fun n : Nat =>
      (1 - zipfTailRatio (calibrationExponent lam hlam n)
        (sourceMoleculeCount n)) ^ (sourceMoleculeCount n)) atTop
      (𝓝 (Real.exp (-(((2 : ℝ) ^
        (-criticalLambdaInv (⟨lam, hlam⟩ : Set.Ioi (0 : ℝ)))) /
          (Real.pi ^ 2 / 6))))) := by
  let p : Nat → ℝ := fun n => zipfTailRatio (calibrationExponent lam hlam n)
    (sourceMoleculeCount n)
  let theta : ℝ := ((2 : ℝ) ^
    (-criticalLambdaInv (⟨lam, hlam⟩ : Set.Ioi (0 : ℝ)))) / (Real.pi ^ 2 / 6)
  have hNp : Tendsto (fun n : Nat => (sourceMoleculeCount n : ℝ) * p n)
      atTop (𝓝 theta) := by
    simpa [p, theta] using calibratedMoleculeScaleTail lam hlam
  have hxreal : Tendsto (fun n : Nat => (sourceMoleculeCount n : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).comp sourceMoleculeCount_tendsto_atTop
  have hxinv : Tendsto (fun n : Nat => (sourceMoleculeCount n : ℝ)⁻¹)
      atTop (𝓝 0) := hxreal.inv_tendsto_atTop
  have hp : Tendsto p atTop (𝓝 0) := by
    have h := hNp.mul hxinv
    have h' : Tendsto (fun n : Nat =>
        ((sourceMoleculeCount n : ℝ) * p n) *
          (sourceMoleculeCount n : ℝ)⁻¹) atTop (𝓝 0) := by
      simpa only [mul_zero] using h
    apply h'.congr'
    filter_upwards [sourceMoleculeCount_tendsto_atTop.eventually (eventually_gt_atTop 0)]
      with n hxn
    field_simp
  have hpne : ∀ᶠ n : Nat in atTop, p n ≠ 0 := by
    have ha : ∀ᶠ n : Nat in atTop, 1 < calibrationExponent lam hlam n :=
      (calibrationExponent_tendsto_two lam hlam) (Ioi_mem_nhds (by norm_num))
    filter_upwards [ha, eventually_ge_atTop 1] with n han hn
    have hpow : 2 ≤ 2 ^ n := by
      have h := Nat.pow_le_pow_right (by norm_num : 0 < 2) hn
      norm_num at h ⊢
      exact h
    have hX : 2 ≤ sourceMoleculeCount n :=
      hpow.trans (sourceMoleculeCount_bounds hn).1
    have htail : 0 < rpowTail (calibrationExponent lam hlam n)
        (sourceMoleculeCount n) := by
      rw [rpowTail_eq_head_add han (sourceMoleculeCount n)]
      exact add_pos_of_pos_of_nonneg (Real.rpow_pos_of_pos (by positivity) _)
        (rpowTail_nonneg _ _)
    have hden : 0 < zipfNormalizer (calibrationExponent lam hlam n) := by
      rw [zipfNormalizer_eq_prefix_add_tail han 2, zipfPrefix_two han]
      nlinarith [rpowTail_nonneg (calibrationExponent lam hlam n) 2]
    exact ne_of_gt (div_pos htail hden)
  have hplt : ∀ᶠ n : Nat in atTop, p n < 1 := hp (Iio_mem_nhds (by norm_num))
  simpa [p, theta] using
    binomialNoHit_tendsto_exp_neg sourceMoleculeCount p theta hp hpne hplt hNp

theorem calibratedExistsMoleculeScaleCatalyst
    (lam : ℝ) (hlam : 0 < lam) :
    Tendsto (fun n : Nat => 1 -
      (1 - zipfTailRatio (calibrationExponent lam hlam n)
        (sourceMoleculeCount n)) ^ (sourceMoleculeCount n)) atTop
      (𝓝 (1 - Real.exp (-(((2 : ℝ) ^
        (-criticalLambdaInv (⟨lam, hlam⟩ : Set.Ioi (0 : ℝ)))) /
          (Real.pi ^ 2 / 6))))) := by
  simpa only using (tendsto_const_nhds : Tendsto (fun _ : Nat => (1 : ℝ)) atTop (𝓝 1)).sub
    (calibratedNoMoleculeScaleCatalyst lam hlam)

end PowerLawSmallRAF
