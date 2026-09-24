import proofs.PowerLawSmallRAF.CriticalProfile
import Mathlib.Analysis.Normed.Group.FunctionSeries

namespace PowerLawSmallRAF

open Filter Topology Set

noncomputable def shiftedZipfNormalizer (a : ℝ) : ℝ :=
  ∑' j : Nat, ((j + 1 : Nat) : ℝ) ^ (-a)

theorem summable_shiftedZipfWeight {a : ℝ} (ha : 1 < a) :
    Summable (fun j : Nat => ((j + 1 : Nat) : ℝ) ^ (-a)) := by
  have hs := Real.summable_nat_rpow.mpr (by linarith : -a < (-1 : ℝ))
  simpa only [Nat.succ_eq_add_one] using hs.comp_injective Nat.succ_injective

theorem zipfNormalizer_eq_shifted {a : ℝ} (ha : 1 < a) :
    zipfNormalizer a = shiftedZipfNormalizer a := by
  have hs : Summable (fun k : Nat => (k : ℝ) ^ (-a)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hsplit := hs.sum_add_tsum_nat_add 1
  rw [zipfNormalizer, shiftedZipfNormalizer]
  calc
    (∑' k : Nat, (k : ℝ) ^ (-a)) =
        (∑ k ∈ Finset.range 1, (k : ℝ) ^ (-a)) +
          ∑' k : Nat, ((k + 1 : Nat) : ℝ) ^ (-a) := hsplit.symm
    _ = ∑' k : Nat, ((k + 1 : Nat) : ℝ) ^ (-a) := by
      simp [Real.zero_rpow (by linarith : -a ≠ 0)]

theorem continuousOn_shiftedZipfNormalizer {c : ℝ} (hc : 1 < c) :
    ContinuousOn shiftedZipfNormalizer (Ici c) := by
  change ContinuousOn (fun a : ℝ =>
    ∑' j : Nat, ((j + 1 : Nat) : ℝ) ^ (-a)) (Ici c)
  refine continuousOn_tsum (fun j => ?_) (summable_shiftedZipfWeight hc) ?_
  · exact ((Real.continuous_const_rpow (by positivity :
        (((j + 1 : Nat) : ℝ)) ≠ 0)).comp continuous_neg).continuousOn
  · intro j a ha
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
    exact Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (by omega : j + 1 ≠ 0)))
      (neg_le_neg ha)

theorem continuousOn_zipfNormalizer {c : ℝ} (hc : 1 < c) :
    ContinuousOn zipfNormalizer (Ici c) := by
  apply continuousOn_shiftedZipfNormalizer hc |>.congr
  intro a ha
  exact zipfNormalizer_eq_shifted (lt_of_lt_of_le hc ha)

theorem continuousAt_zipfNormalizer {a : ℝ} (ha : 1 < a) :
    ContinuousAt zipfNormalizer a := by
  let c := (1 + a) / 2
  have hc : 1 < c := by dsimp [c]; linarith
  have hca : a ∈ Ici c := by dsimp [c]; simp only [mem_Ici]; linarith
  exact (continuousOn_zipfNormalizer hc).continuousAt
    (Ici_mem_nhds (by dsimp [c]; linarith))

def cappedReward (R k : Nat) : ℝ := ((min k R - 1 : Nat) : ℝ)

noncomputable def shiftedCappedNumerator (a : ℝ) (R : Nat) : ℝ :=
  ∑' j : Nat, cappedReward R (j + 1) * ((j + 1 : Nat) : ℝ) ^ (-a)

theorem cappedReward_nonneg (R k : Nat) : 0 ≤ cappedReward R k := by
  simp [cappedReward]

theorem cappedReward_le (R k : Nat) : cappedReward R k ≤ R := by
  dsimp [cappedReward]
  exact_mod_cast (Nat.sub_le (min k R) 1).trans (min_le_right k R)

theorem continuousOn_shiftedCappedNumerator {c : ℝ} (hc : 1 < c) (R : Nat) :
    ContinuousOn (fun a => shiftedCappedNumerator a R) (Ici c) := by
  dsimp [shiftedCappedNumerator]
  let u : Nat → ℝ := fun j =>
    (R : ℝ) * ((j + 1 : Nat) : ℝ) ^ (-c)
  have hu : Summable u := (summable_shiftedZipfWeight hc).mul_left (R : ℝ)
  refine continuousOn_tsum (fun j => ?_) hu ?_
  · exact (continuous_const.mul
      ((Real.continuous_const_rpow (by positivity :
        (((j + 1 : Nat) : ℝ)) ≠ 0)).comp continuous_neg)).continuousOn
  · intro j a ha
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (cappedReward_nonneg R (j + 1))
        (Real.rpow_nonneg (by positivity) _))]
    apply mul_le_mul (cappedReward_le R (j + 1))
    · exact Real.rpow_le_rpow_of_exponent_le
        (by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (by omega : j + 1 ≠ 0)))
        (neg_le_neg ha)
    · exact Real.rpow_nonneg (by positivity) _
    · positivity

theorem continuousAt_shiftedCappedNumerator {a : ℝ} (ha : 1 < a) (R : Nat) :
    ContinuousAt (fun x => shiftedCappedNumerator x R) a := by
  let c := (1 + a) / 2
  have hc : 1 < c := by dsimp [c]; linarith
  exact (continuousOn_shiftedCappedNumerator hc R).continuousAt
    (Ici_mem_nhds (by dsimp [c]; linarith))

noncomputable def finiteZipfMean (a : ℝ) (R : Nat) : ℝ :=
  shiftedCappedNumerator a R / shiftedZipfNormalizer a

theorem shiftedZipfNormalizer_pos {a : ℝ} (ha : 1 < a) :
    0 < shiftedZipfNormalizer a := by
  refine (summable_shiftedZipfWeight ha).tsum_pos
    (fun j => Real.rpow_nonneg (by positivity) _) 0 ?_
  norm_num [Real.one_rpow]

theorem continuousAt_shiftedZipfNormalizer {a : ℝ} (ha : 1 < a) :
    ContinuousAt shiftedZipfNormalizer a := by
  let c := (1 + a) / 2
  have hc : 1 < c := by dsimp [c]; linarith
  exact (continuousOn_shiftedZipfNormalizer hc).continuousAt
    (Ici_mem_nhds (by dsimp [c]; linarith))

theorem continuousAt_finiteZipfMean {a : ℝ} (ha : 1 < a) (R : Nat) :
    ContinuousAt (fun x => finiteZipfMean x R) a := by
  exact (continuousAt_shiftedCappedNumerator ha R).div
    (continuousAt_shiftedZipfNormalizer ha)
    (ne_of_gt (shiftedZipfNormalizer_pos ha))

theorem summable_shiftedRpowWeight {a : ℝ} (ha : 1 < a)
    (R : Nat) :
    Summable (fun j : Nat => ((j + R : Nat) : ℝ) ^ (-a)) := by
  have hs := Real.summable_nat_rpow.mpr (by linarith : -a < (-1 : ℝ))
  exact hs.comp_injective (fun _ _ h => Nat.add_right_cancel h)

theorem continuousOn_rpowTail {c : ℝ} (hc : 1 < c)
    (R : Nat) (hR : 1 ≤ R) :
    ContinuousOn (fun a => rpowTail a R) (Ici c) := by
  dsimp [rpowTail]
  refine continuousOn_tsum (fun j => ?_) (summable_shiftedRpowWeight hc R) ?_
  · exact ((Real.continuous_const_rpow (by
        exact_mod_cast (by omega : j + R ≠ 0))).comp continuous_neg).continuousOn
  · intro j a ha
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
    exact Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast (by omega : 1 ≤ j + R)) (neg_le_neg ha)

theorem continuousOn_windowDirectNumerator {c : ℝ} (hc : 1 < c)
    (R : Nat) (hR : 1 ≤ R) :
    ContinuousOn (fun a => windowDirectNumerator a R) (Ici c) := by
  dsimp [windowDirectNumerator, cappedRpowTail]
  apply ContinuousOn.add
  · apply continuousOn_finsetSum
    intro k hk
    exact (continuous_const.mul
      ((Real.continuous_const_rpow (by
        have hk2 : 2 ≤ k := (Finset.mem_Ico.mp hk).1
        exact_mod_cast (by omega : k ≠ 0))).comp continuous_neg)).continuousOn
  · exact continuousOn_const.mul (continuousOn_rpowTail hc R hR)

theorem continuousOn_windowZipfMean (R : Nat) (hR : 1 ≤ R) :
    ContinuousOn (fun a => windowZipfMean a R) (Ioi 1) := by
  apply continuousOn_of_forall_continuousAt
  intro a ha
  have ha' : 1 < a := ha
  let c := (1 + a) / 2
  have hc : 1 < c := by dsimp [c]; linarith
  have hnum := (continuousOn_windowDirectNumerator hc R hR).continuousAt
    (Ici_mem_nhds (show c < a by dsimp [c]; linarith))
  have hden := continuousAt_zipfNormalizer ha'
  dsimp [windowZipfMean]
  exact hnum.div hden (by
    rw [zipfNormalizer_eq_shifted ha']
    exact ne_of_gt (shiftedZipfNormalizer_pos ha'))

theorem eventually_exists_windowCalibration (lam : ℝ) (hlam : 0 < lam) :
    let target : Ioi (0 : ℝ) := ⟨lam, hlam⟩
    let b₀ := criticalLambdaInv target
    ∀ᶠ n : Nat in atTop, ∃ b ∈ Icc (b₀ - 1) (b₀ + 1),
      windowZipfMean (2 + b / (n : ℝ)) (sourceReactionCount n) / (n : ℝ) = lam := by
  dsimp only
  let target : Ioi (0 : ℝ) := ⟨lam, hlam⟩
  let b₀ := criticalLambdaInv target
  let lower := b₀ - 1
  let upper := b₀ + 1
  have htarget : criticalLambda b₀ = lam := by
    simpa [b₀, target] using criticalLambda_criticalLambdaInv target
  have hlambda : criticalLambda upper < lam := by
    rw [← htarget]
    exact strictAnti_criticalLambda (by dsimp [upper, b₀]; linarith)
  have hlambda' : lam < criticalLambda lower := by
    rw [← htarget]
    exact strictAnti_criticalLambda (by dsimp [lower, b₀]; linarith)
  have hlower := (tendsto_order.1
    (windowZipfMean_source_window_normalized lower)).1 lam hlambda'
  have hupper := (tendsto_order.1
    (windowZipfMean_source_window_normalized upper)).2 lam hlambda
  have halower : Tendsto (fun n : Nat => 2 + lower / (n : ℝ))
      atTop (𝓝 2) := by
    have hdiv : Tendsto (fun n : Nat => lower / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa only [add_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : Nat => (2 : ℝ)) atTop (𝓝 2)).add hdiv
  have halowerPos : ∀ᶠ n : Nat in atTop, 1 < 2 + lower / (n : ℝ) :=
    halower (Ioi_mem_nhds (by norm_num))
  filter_upwards [hlower, hupper, halowerPos, eventually_ge_atTop 4]
    with n hnlow hnup han hn4
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hR : 1 ≤ sourceReactionCount n := by
    have hp : 1 ≤ 2 ^ n := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero n (by norm_num))
    exact hp.trans (sourceReactionCount_bounds hn4).1
  let f : ℝ → ℝ := fun b =>
    windowZipfMean (2 + b / (n : ℝ)) (sourceReactionCount n) / (n : ℝ)
  have hmap : MapsTo (fun b : ℝ => 2 + b / (n : ℝ)) (Icc lower upper) (Ioi 1) := by
    intro b hb
    have hdiv : lower / (n : ℝ) ≤ b / (n : ℝ) :=
      div_le_div_of_nonneg_right hb.1 hnpos.le
    change 1 < 2 + b / (n : ℝ)
    linarith
  have hfcont : ContinuousOn f (Icc lower upper) := by
    apply ContinuousOn.div_const
    exact (continuousOn_windowZipfMean (sourceReactionCount n) hR).comp
      (by fun_prop : Continuous (fun b : ℝ => 2 + b / (n : ℝ))).continuousOn hmap
  have hbounds : lam ∈ Icc (f upper) (f lower) := ⟨hnup.le, hnlow.le⟩
  obtain ⟨b, hb, heq⟩ := intermediate_value_Icc'
    (by dsimp [lower, upper, b₀]; linarith) hfcont hbounds
  exact ⟨b, by simpa [lower, upper] using hb, heq⟩

noncomputable def calibrationB (lam : ℝ) (hlam : 0 < lam) (n : Nat) : ℝ :=
  by
    classical
    let target : Ioi (0 : ℝ) := ⟨lam, hlam⟩
    let b₀ := criticalLambdaInv target
    exact if h : ∃ b ∈ Icc (b₀ - 1) (b₀ + 1),
        windowZipfMean (2 + b / (n : ℝ)) (sourceReactionCount n) / (n : ℝ) = lam
      then Classical.choose h
      else b₀

noncomputable def calibrationExponent (lam : ℝ) (hlam : 0 < lam) (n : Nat) : ℝ :=
  2 + calibrationB lam hlam n / (n : ℝ)

theorem calibrationB_mem (lam : ℝ) (hlam : 0 < lam) (n : Nat) :
    let target : Ioi (0 : ℝ) := ⟨lam, hlam⟩
    let b₀ := criticalLambdaInv target
    calibrationB lam hlam n ∈ Icc (b₀ - 1) (b₀ + 1) := by
  dsimp only
  let target : Ioi (0 : ℝ) := ⟨lam, hlam⟩
  let b₀ := criticalLambdaInv target
  by_cases h : ∃ b ∈ Icc (b₀ - 1) (b₀ + 1),
      windowZipfMean (2 + b / (n : ℝ)) (sourceReactionCount n) / (n : ℝ) = lam
  · rw [calibrationB, dif_pos h]
    exact (Classical.choose_spec h).1
  · rw [calibrationB, dif_neg h]
    constructor <;> dsimp [b₀] <;> linarith

theorem eventually_calibrationExponent_exact (lam : ℝ) (hlam : 0 < lam) :
    ∀ᶠ n : Nat in atTop,
      windowZipfMean (calibrationExponent lam hlam n) (sourceReactionCount n) /
        (n : ℝ) = lam := by
  have hexists := eventually_exists_windowCalibration lam hlam
  filter_upwards [hexists] with n hn
  let target : Ioi (0 : ℝ) := ⟨lam, hlam⟩
  let b₀ := criticalLambdaInv target
  have h : ∃ b ∈ Icc (b₀ - 1) (b₀ + 1),
      windowZipfMean (2 + b / (n : ℝ)) (sourceReactionCount n) / (n : ℝ) = lam := by
    simpa [target, b₀] using hn
  rw [calibrationExponent, calibrationB, dif_pos h]
  exact (Classical.choose_spec h).2

theorem calibrationB_abs_le (lam : ℝ) (hlam : 0 < lam) (n : Nat) :
    |calibrationB lam hlam n| ≤
      |criticalLambdaInv (⟨lam, hlam⟩ : Ioi (0 : ℝ))| + 1 := by
  have hm := calibrationB_mem lam hlam n
  dsimp only at hm
  rw [abs_le]
  constructor
  · have h := neg_abs_le
      (criticalLambdaInv (⟨lam, hlam⟩ : Ioi (0 : ℝ)))
    linarith [hm.1]
  · linarith [hm.2, le_abs_self
      (criticalLambdaInv (⟨lam, hlam⟩ : Ioi (0 : ℝ)))]

theorem calibrationExponent_tendsto_two (lam : ℝ) (hlam : 0 < lam) :
    Tendsto (calibrationExponent lam hlam) atTop (𝓝 2) := by
  let C := |criticalLambdaInv (⟨lam, hlam⟩ : Ioi (0 : ℝ))| + 1
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hupper : Tendsto (fun n : Nat => C / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop (R := ℝ))
  have hlower : Tendsto (fun n : Nat => -C / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop (R := ℝ))
  have hzero : Tendsto (fun n : Nat => calibrationB lam hlam n / (n : ℝ))
      atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper
    · filter_upwards with n
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
      have habs := calibrationB_abs_le lam hlam n
      rw [abs_le] at habs
      exact habs.1
    · filter_upwards with n
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
      exact (le_abs_self (calibrationB lam hlam n)).trans
        (calibrationB_abs_le lam hlam n)
  simpa [calibrationExponent] using
    (tendsto_const_nhds : Tendsto (fun _ : Nat => (2 : ℝ)) atTop (𝓝 2)).add hzero

noncomputable def zipfPrefix (a : ℝ) (m : Nat) : ℝ :=
  ∑ k ∈ Finset.range m, (k : ℝ) ^ (-a)

noncomputable def zipfTailRatio (a : ℝ) (m : Nat) : ℝ :=
  rpowTail a m / zipfNormalizer a

theorem zipfNormalizer_eq_prefix_add_tail {a : ℝ} (ha : 1 < a) (m : Nat) :
    zipfNormalizer a = zipfPrefix a m + rpowTail a m := by
  have hs : Summable (fun k : Nat => (k : ℝ) ^ (-a)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  simpa [zipfNormalizer, zipfPrefix, rpowTail] using
    (hs.sum_add_tsum_nat_add m).symm

theorem scale_rpow_le_rpow_of_le {a₁ a₂ : ℝ} (ha : a₁ < a₂)
    {m k : Nat} (hm : 1 ≤ m) (hmk : m ≤ k) :
    (m : ℝ) ^ (a₂ - a₁) * (k : ℝ) ^ (-a₂) ≤ (k : ℝ) ^ (-a₁) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (hm.trans hmk))
  have hbase : (m : ℝ) ^ (a₂ - a₁) ≤ (k : ℝ) ^ (a₂ - a₁) := by
    exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hmk) (by linarith)
  calc
    (m : ℝ) ^ (a₂ - a₁) * (k : ℝ) ^ (-a₂) ≤
        (k : ℝ) ^ (a₂ - a₁) * (k : ℝ) ^ (-a₂) :=
      mul_le_mul_of_nonneg_right hbase (Real.rpow_nonneg hk0.le _)
    _ = (k : ℝ) ^ ((a₂ - a₁) + (-a₂)) := (Real.rpow_add hk0 _ _).symm
    _ = (k : ℝ) ^ (-a₁) := by ring_nf

theorem rpow_le_scale_rpow_of_le {a₁ a₂ : ℝ} (ha : a₁ < a₂)
    {k m : Nat} (hk : 1 ≤ k) (hkm : k ≤ m) :
    (k : ℝ) ^ (-a₁) ≤ (m : ℝ) ^ (a₂ - a₁) * (k : ℝ) ^ (-a₂) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  have hbase : (k : ℝ) ^ (a₂ - a₁) ≤ (m : ℝ) ^ (a₂ - a₁) := by
    exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hkm) (by linarith)
  calc
    (k : ℝ) ^ (-a₁) = (k : ℝ) ^ ((a₂ - a₁) + (-a₂)) := by ring_nf
    _ = (k : ℝ) ^ (a₂ - a₁) * (k : ℝ) ^ (-a₂) := Real.rpow_add hk0 _ _
    _ ≤ (m : ℝ) ^ (a₂ - a₁) * (k : ℝ) ^ (-a₂) :=
      mul_le_mul_of_nonneg_right hbase (Real.rpow_nonneg hk0.le _)

theorem scale_mul_zipfTail_le {a₁ a₂ : ℝ} (ha₁ : 1 < a₁) (ha : a₁ < a₂)
    {m : Nat} (hm : 1 ≤ m) :
    (m : ℝ) ^ (a₂ - a₁) * rpowTail a₂ m ≤ rpowTail a₁ m := by
  have ha₂ : 1 < a₂ := ha₁.trans ha
  have hs₂ := summable_shiftedRpowWeight ha₂ m
  have hs₁ := summable_shiftedRpowWeight ha₁ m
  rw [rpowTail, rpowTail, ← hs₂.tsum_mul_left ((m : ℝ) ^ (a₂ - a₁))]
  exact (hs₂.mul_left ((m : ℝ) ^ (a₂ - a₁))).tsum_le_tsum
    (fun j => scale_rpow_le_rpow_of_le ha hm (by omega : m ≤ j + m)) hs₁

theorem zipfPrefix_le_scale_mul {a₁ a₂ : ℝ} (ha₁ : 1 < a₁) (ha : a₁ < a₂)
    (m : Nat) :
    zipfPrefix a₁ m ≤ (m : ℝ) ^ (a₂ - a₁) * zipfPrefix a₂ m := by
  rw [zipfPrefix, zipfPrefix, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  by_cases hk0 : k = 0
  · subst k
    simp [Real.zero_rpow (by linarith : -a₁ ≠ 0),
      Real.zero_rpow (by linarith : -a₂ ≠ 0)]
  · exact rpow_le_scale_rpow_of_le ha
      (Nat.one_le_iff_ne_zero.mpr hk0) (Nat.le_of_lt (Finset.mem_range.mp hk))

theorem zipfPrefix_nonneg (a : ℝ) (m : Nat) : 0 ≤ zipfPrefix a m := by
  exact Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (by positivity) _

theorem zipfTailRatio_antitone {a₁ a₂ : ℝ} (ha₁ : 1 < a₁) (ha : a₁ < a₂)
    {m : Nat} (hm : 1 ≤ m) :
    zipfTailRatio a₂ m ≤ zipfTailRatio a₁ m := by
  have ha₂ : 1 < a₂ := ha₁.trans ha
  let C := (m : ℝ) ^ (a₂ - a₁)
  have hC : 0 ≤ C := Real.rpow_nonneg (by positivity) _
  have htail : C * rpowTail a₂ m ≤ rpowTail a₁ m :=
    scale_mul_zipfTail_le ha₁ ha hm
  have hprefix : zipfPrefix a₁ m ≤ C * zipfPrefix a₂ m :=
    zipfPrefix_le_scale_mul ha₁ ha m
  have hcross : rpowTail a₂ m * zipfPrefix a₁ m ≤
      rpowTail a₁ m * zipfPrefix a₂ m := by
    calc
      rpowTail a₂ m * zipfPrefix a₁ m ≤
          rpowTail a₂ m * (C * zipfPrefix a₂ m) :=
        mul_le_mul_of_nonneg_left hprefix (rpowTail_nonneg _ _)
      _ = (C * rpowTail a₂ m) * zipfPrefix a₂ m := by ring
      _ ≤ rpowTail a₁ m * zipfPrefix a₂ m :=
        mul_le_mul_of_nonneg_right htail (zipfPrefix_nonneg _ _)
  rw [zipfTailRatio, zipfTailRatio,
    zipfNormalizer_eq_prefix_add_tail ha₁ m,
    zipfNormalizer_eq_prefix_add_tail ha₂ m]
  rw [div_le_div_iff₀]
  · nlinarith
  · rw [← zipfNormalizer_eq_prefix_add_tail ha₂ m,
      zipfNormalizer_eq_shifted ha₂]
    exact shiftedZipfNormalizer_pos ha₂
  · rw [← zipfNormalizer_eq_prefix_add_tail ha₁ m,
      zipfNormalizer_eq_shifted ha₁]
    exact shiftedZipfNormalizer_pos ha₁

theorem rpowTail_strictAnti {a₁ a₂ : ℝ} (ha₁ : 1 < a₁) (ha : a₁ < a₂)
    {m : Nat} (hm : 2 ≤ m) : rpowTail a₂ m < rpowTail a₁ m := by
  have ha₂ : 1 < a₂ := ha₁.trans ha
  have hs₂ := summable_shiftedRpowWeight ha₂ m
  have hs₁ := summable_shiftedRpowWeight ha₁ m
  rw [rpowTail, rpowTail]
  apply hs₂.tsum_lt_tsum (i := 0)
  · intro j
    exact Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast (by omega : 1 ≤ j + m)) (by linarith)
  · simpa only [Nat.zero_add] using Real.rpow_lt_rpow_of_exponent_lt
      (by exact_mod_cast hm : (1 : ℝ) < m) (by linarith : -a₂ < -a₁)
  · exact hs₁

theorem zipfPrefix_two {a : ℝ} (ha : 1 < a) : zipfPrefix a 2 = 1 := by
  rw [zipfPrefix, Finset.sum_range_succ, Finset.sum_range_succ]
  norm_num [Real.zero_rpow (by linarith : -a ≠ 0)]

theorem zipfTailRatio_two_strictAnti {a₁ a₂ : ℝ} (ha₁ : 1 < a₁) (ha : a₁ < a₂) :
    zipfTailRatio a₂ 2 < zipfTailRatio a₁ 2 := by
  have ha₂ : 1 < a₂ := ha₁.trans ha
  have ht := rpowTail_strictAnti ha₁ ha (m := 2) (by norm_num)
  rw [zipfTailRatio, zipfTailRatio,
    zipfNormalizer_eq_prefix_add_tail ha₁ 2,
    zipfNormalizer_eq_prefix_add_tail ha₂ 2,
    zipfPrefix_two ha₁, zipfPrefix_two ha₂]
  rw [div_lt_div_iff₀]
  · nlinarith [rpowTail_nonneg a₁ 2, rpowTail_nonneg a₂ 2]
  · nlinarith [rpowTail_nonneg a₂ 2]
  · nlinarith [rpowTail_nonneg a₁ 2]

theorem rpowTail_eq_head_add {a : ℝ} (ha : 1 < a) (R : Nat) :
    rpowTail a R = (R : ℝ) ^ (-a) + rpowTail a (R + 1) := by
  have hs := summable_shiftedRpowWeight ha R
  have hsplit := hs.sum_add_tsum_nat_add 1
  simpa [rpowTail, add_assoc, add_comm, add_left_comm] using hsplit.symm

theorem windowDirectNumerator_succ {a : ℝ} (ha : 1 < a)
    {R : Nat} (hR : 2 ≤ R) :
    windowDirectNumerator a (R + 1) =
      windowDirectNumerator a R + rpowTail a (R + 1) := by
  rw [windowDirectNumerator, windowDirectNumerator, cappedRpowTail, cappedRpowTail]
  rw [Finset.sum_Ico_succ_top hR]
  rw [rpowTail_eq_head_add ha R]
  have hsubR : R + 1 - 1 = R := by omega
  have hsub : R - 1 + 1 = R := by omega
  have hcast : ((R - 1 : Nat) : ℝ) + 1 = R := by exact_mod_cast hsub
  simp only [hsubR]
  rw [← hcast]
  ring

theorem windowDirectNumerator_eq_sum_tails {a : ℝ} (ha : 1 < a)
    {R : Nat} (hR : 2 ≤ R) :
    windowDirectNumerator a R =
      ∑ m ∈ Finset.Ico 2 (R + 1), rpowTail a m := by
  induction R, hR using Nat.le_induction with
  | base =>
      norm_num [windowDirectNumerator, cappedRpowTail]
  | succ R hR ih =>
      rw [windowDirectNumerator_succ ha hR, ih]
      rw [Finset.sum_Ico_succ_top (by omega : 2 ≤ R + 1)]

theorem windowZipfMean_eq_sum_tailRatios {a : ℝ} (ha : 1 < a)
    {R : Nat} (hR : 2 ≤ R) :
    windowZipfMean a R =
      ∑ m ∈ Finset.Ico 2 (R + 1), zipfTailRatio a m := by
  rw [windowZipfMean, windowDirectNumerator_eq_sum_tails ha hR]
  rw [Finset.sum_div]
  rfl

theorem strictAntiOn_windowZipfMean (R : Nat) (hR : 2 ≤ R) :
    StrictAntiOn (fun a => windowZipfMean a R) (Ioi 1) := by
  intro a₁ ha₁ a₂ ha₂ ha
  change windowZipfMean a₂ R < windowZipfMean a₁ R
  rw [windowZipfMean_eq_sum_tailRatios ha₁ hR,
    windowZipfMean_eq_sum_tailRatios ha₂ hR]
  apply Finset.sum_lt_sum
  · intro m hm
    exact zipfTailRatio_antitone ha₁ ha (by
      have := (Finset.mem_Ico.mp hm).1
      omega)
  · refine ⟨2, ?_, zipfTailRatio_two_strictAnti ha₁ ha⟩
    simp only [Finset.mem_Ico]
    omega

theorem eventually_existsUnique_calibrationExponent (lam : ℝ) (hlam : 0 < lam) :
    ∀ᶠ n : Nat in atTop, ∃! a : ℝ,
      1 < a ∧ windowZipfMean a (sourceReactionCount n) / (n : ℝ) = lam := by
  have hexact := eventually_calibrationExponent_exact lam hlam
  have hpos : ∀ᶠ n : Nat in atTop, 1 < calibrationExponent lam hlam n :=
    (calibrationExponent_tendsto_two lam hlam) (Ioi_mem_nhds (by norm_num))
  filter_upwards [hexact, hpos, eventually_ge_atTop 4]
    with n hexact hcalpos hn4
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hR : 2 ≤ sourceReactionCount n := by
    have hp : 2 ≤ 2 ^ n := by
      have := Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega : 1 ≤ n)
      norm_num at this ⊢
      exact this
    exact hp.trans (sourceReactionCount_bounds hn4).1
  refine ⟨calibrationExponent lam hlam n, ⟨hcalpos, hexact⟩, ?_⟩
  intro a ha
  apply (strictAntiOn_windowZipfMean (sourceReactionCount n) hR).injOn ha.1 hcalpos
  apply (div_left_inj' hn0).mp
  exact ha.2.trans hexact.symm

theorem every_exact_calibration_tendsto_two (lam : ℝ) (hlam : 0 < lam)
    (a : Nat → ℝ)
    (ha : ∀ᶠ n : Nat in atTop, 1 < a n)
    (hmean : ∀ᶠ n : Nat in atTop,
      windowZipfMean (a n) (sourceReactionCount n) / (n : ℝ) = lam) :
    Tendsto a atTop (𝓝 2) := by
  have hu := eventually_existsUnique_calibrationExponent lam hlam
  have hcalpos : ∀ᶠ n : Nat in atTop, 1 < calibrationExponent lam hlam n :=
    (calibrationExponent_tendsto_two lam hlam) (Ioi_mem_nhds (by norm_num))
  have hcalmean := eventually_calibrationExponent_exact lam hlam
  have heq : a =ᶠ[atTop] calibrationExponent lam hlam := by
    filter_upwards [ha, hmean, hu, hcalpos, hcalmean]
      with n han hmn hun hcp hcm
    exact hun.unique ⟨han, hmn⟩ ⟨hcp, hcm⟩
  exact (calibrationExponent_tendsto_two lam hlam).congr' heq.symm

theorem calibrationB_tendsto_inverse (lam : ℝ) (hlam : 0 < lam) :
    Tendsto (calibrationB lam hlam) atTop
      (𝓝 (criticalLambdaInv (⟨lam, hlam⟩ : Ioi (0 : ℝ)))) := by
  let target : Ioi (0 : ℝ) := ⟨lam, hlam⟩
  let b₀ := criticalLambdaInv target
  have htarget : criticalLambda b₀ = lam := by
    simpa [b₀, target] using criticalLambda_criticalLambdaInv target
  rw [tendsto_order]
  constructor
  · intro c hc
    have hprofile : lam < criticalLambda c := by
      rw [← htarget]
      exact strictAnti_criticalLambda hc
    have hfinite := (tendsto_order.1
      (windowZipfMean_source_window_normalized c)).1 lam hprofile
    have hcexp : Tendsto (fun n : Nat => 2 + c / (n : ℝ)) atTop (𝓝 2) := by
      have hdiv : Tendsto (fun n : Nat => c / (n : ℝ)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop (R := ℝ))
      simpa only [add_zero] using
        (tendsto_const_nhds : Tendsto (fun _ : Nat => (2 : ℝ)) atTop (𝓝 2)).add hdiv
    have hcpos : ∀ᶠ n : Nat in atTop, 1 < 2 + c / (n : ℝ) :=
      hcexp (Ioi_mem_nhds (by norm_num))
    have hbpos : ∀ᶠ n : Nat in atTop, 1 < calibrationExponent lam hlam n :=
      (calibrationExponent_tendsto_two lam hlam) (Ioi_mem_nhds (by norm_num))
    have hbmean := eventually_calibrationExponent_exact lam hlam
    filter_upwards [hfinite, hcpos, hbpos, hbmean, eventually_ge_atTop 4]
      with n hfn hcp hbp hbm hn4
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hR : 2 ≤ sourceReactionCount n := by
      have hp : 2 ≤ 2 ^ n := by
        have hpow := Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega : 1 ≤ n)
        norm_num at hpow ⊢
        exact hpow
      exact hp.trans (sourceReactionCount_bounds hn4).1
    by_contra hnot
    have hbc : calibrationB lam hlam n ≤ c := le_of_not_gt hnot
    have hexp : calibrationExponent lam hlam n ≤ 2 + c / (n : ℝ) := by
      dsimp [calibrationExponent]
      have hd := div_le_div_of_nonneg_right hbc hnpos.le
      linarith
    have hmeanle := (strictAntiOn_windowZipfMean (sourceReactionCount n) hR).antitoneOn
      hbp hcp hexp
    have hnormle :
        windowZipfMean (2 + c / (n : ℝ)) (sourceReactionCount n) / (n : ℝ) ≤ lam := by
      rw [← hbm]
      exact div_le_div_of_nonneg_right hmeanle hnpos.le
    exact (not_lt_of_ge hnormle) hfn

  · intro c hc
    have hprofile : criticalLambda c < lam := by
      rw [← htarget]
      exact strictAnti_criticalLambda hc
    have hfinite := (tendsto_order.1
      (windowZipfMean_source_window_normalized c)).2 lam hprofile
    have hcexp : Tendsto (fun n : Nat => 2 + c / (n : ℝ)) atTop (𝓝 2) := by
      have hdiv : Tendsto (fun n : Nat => c / (n : ℝ)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop (R := ℝ))
      simpa only [add_zero] using
        (tendsto_const_nhds : Tendsto (fun _ : Nat => (2 : ℝ)) atTop (𝓝 2)).add hdiv
    have hcpos : ∀ᶠ n : Nat in atTop, 1 < 2 + c / (n : ℝ) :=
      hcexp (Ioi_mem_nhds (by norm_num))
    have hbpos : ∀ᶠ n : Nat in atTop, 1 < calibrationExponent lam hlam n :=
      (calibrationExponent_tendsto_two lam hlam) (Ioi_mem_nhds (by norm_num))
    have hbmean := eventually_calibrationExponent_exact lam hlam
    filter_upwards [hfinite, hcpos, hbpos, hbmean, eventually_ge_atTop 4]
      with n hfn hcp hbp hbm hn4
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hR : 2 ≤ sourceReactionCount n := by
      have hp : 2 ≤ 2 ^ n := by
        have hpow := Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega : 1 ≤ n)
        norm_num at hpow ⊢
        exact hpow
      exact hp.trans (sourceReactionCount_bounds hn4).1
    by_contra hnot
    have hcb : c ≤ calibrationB lam hlam n := le_of_not_gt hnot
    have hexp : 2 + c / (n : ℝ) ≤ calibrationExponent lam hlam n := by
      dsimp [calibrationExponent]
      have hd := div_le_div_of_nonneg_right hcb hnpos.le
      linarith
    have hmeanle := (strictAntiOn_windowZipfMean (sourceReactionCount n) hR).antitoneOn
      hcp hbp hexp
    have hnormle : lam ≤
        windowZipfMean (2 + c / (n : ℝ)) (sourceReactionCount n) / (n : ℝ) := by
      rw [← hbm]
      exact div_le_div_of_nonneg_right hmeanle hnpos.le
    exact (not_lt_of_ge hnormle) hfn

/-- Source-level critical-window theorem: exact finite calibration is eventually
unique, its exponent tends to two, and its rescaled displacement converges to
the unique inverse of the limiting mean profile. -/
theorem criticalWindow_source_theorem (lam : ℝ) (hlam : 0 < lam) :
    (∀ᶠ n : Nat in atTop, ∃! a : ℝ,
      1 < a ∧ windowZipfMean a (sourceReactionCount n) / (n : ℝ) = lam) ∧
    Tendsto (calibrationExponent lam hlam) atTop (𝓝 2) ∧
    Tendsto (calibrationB lam hlam) atTop
      (𝓝 (criticalLambdaInv (⟨lam, hlam⟩ : Ioi (0 : ℝ)))) ∧
    (∀ᶠ n : Nat in atTop,
      windowZipfMean (calibrationExponent lam hlam n) (sourceReactionCount n) /
        (n : ℝ) = lam) := by
  exact ⟨eventually_existsUnique_calibrationExponent lam hlam,
    calibrationExponent_tendsto_two lam hlam,
    calibrationB_tendsto_inverse lam hlam,
    eventually_calibrationExponent_exact lam hlam⟩

end PowerLawSmallRAF
