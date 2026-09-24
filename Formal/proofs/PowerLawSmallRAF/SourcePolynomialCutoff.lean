import proofs.PowerLawSmallRAF.ReversibleDegreeMixing

namespace PowerLawSmallRAF

open Filter Topology

/-- Mark threshold whose lower degrees are exactly the range covered by the
reversible low-degree certificate: `d < M-1` iff `d <= R/n^3`. -/
def sourcePolynomialCutoff (n : Nat) : Nat :=
  sourceReactionCount n / n ^ 3 + 2

theorem sourcePolynomialCutoff_le_sourceReactionCount
    {n : Nat} (hn : 4 ≤ n) :
    sourcePolynomialCutoff n ≤ sourceReactionCount n := by
  have hnle : n ≤ n ^ 3 := by
    have hp := Nat.pow_le_pow_right (by omega : 0 < n) (by omega : 1 ≤ 3)
    simpa using hp
  have hpow : 2 ≤ n ^ 3 := (by omega : 2 ≤ n).trans hnle
  have htwo : 4 ≤ 2 ^ n := by
    have hp := Nat.pow_le_pow_right (by norm_num : 0 < 2) hn
    norm_num at hp ⊢
    exact (by norm_num : 4 ≤ 16).trans hp
  have hR : 4 ≤ sourceReactionCount n :=
    htwo.trans (sourceReactionCount_bounds hn).1
  have hdiv : sourceReactionCount n / n ^ 3 ≤ sourceReactionCount n / 2 :=
    Nat.div_le_div_left hpow (by norm_num)
  dsimp [sourcePolynomialCutoff]
  omega

theorem eventually_sourcePolynomialCutoff_le_sourceReactionCount :
    ∀ᶠ n : Nat in atTop,
      sourcePolynomialCutoff n ≤ sourceReactionCount n := by
  filter_upwards [eventually_ge_atTop 4] with n hn
  exact sourcePolynomialCutoff_le_sourceReactionCount hn

theorem sourcePolynomialCutoff_log_lower
    {n : Nat} (hn : 1 ≤ n) :
    Real.log (sourceReactionCount n : ℝ) / (n : ℝ) -
        3 * Real.log (n : ℝ) / (n : ℝ) ≤
      Real.log (sourcePolynomialCutoff n : ℝ) / (n : ℝ) := by
  have hn3 : 0 < n ^ 3 := pow_pos hn 3
  have hR : 0 < sourceReactionCount n := by
    dsimp [sourceReactionCount]
    omega
  have hnat := Nat.lt_mul_div_succ (sourceReactionCount n) hn3
  have hreal : (sourceReactionCount n : ℝ) / ((n ^ 3 : Nat) : ℝ) <
      (sourceReactionCount n / n ^ 3 + 1 : Nat) := by
    apply (div_lt_iff₀ (by exact_mod_cast hn3)).2
    exact_mod_cast (by simpa only [mul_comm] using hnat)
  have hcut : (sourceReactionCount n : ℝ) / ((n ^ 3 : Nat) : ℝ) <
      (sourcePolynomialCutoff n : ℝ) := by
    dsimp [sourcePolynomialCutoff]
    exact hreal.trans_le (by exact_mod_cast Nat.le_succ _)
  have hlog : Real.log ((sourceReactionCount n : ℝ) /
        ((n ^ 3 : Nat) : ℝ)) ≤
      Real.log (sourcePolynomialCutoff n : ℝ) := by
    exact Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr (div_pos (by exact_mod_cast hR)
        (by exact_mod_cast hn3)))
      (Set.mem_Ioi.mpr (lt_of_lt_of_le
        (div_pos (by exact_mod_cast hR) (by exact_mod_cast hn3)) hcut.le)) hcut.le
  have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hn3real : (((n ^ 3 : Nat) : ℝ)) ≠ 0 := by exact_mod_cast hn3.ne'
  rw [Real.log_div (by exact_mod_cast hR.ne') hn3real,
    Nat.cast_pow, Real.log_pow] at hlog
  calc
    Real.log (sourceReactionCount n : ℝ) / (n : ℝ) -
          3 * Real.log (n : ℝ) / (n : ℝ) =
        (Real.log (sourceReactionCount n : ℝ) -
          3 * Real.log (n : ℝ)) / (n : ℝ) := by ring
    _ ≤ Real.log (sourcePolynomialCutoff n : ℝ) / (n : ℝ) :=
      div_le_div_of_nonneg_right hlog (by positivity)

theorem sourcePolynomialCutoff_log_normalized :
    Tendsto (fun n : Nat =>
      Real.log (sourcePolynomialCutoff n : ℝ) / (n : ℝ))
      atTop (𝓝 (Real.log 2)) := by
  have hlogn : Tendsto (fun n : Nat =>
      Real.log (n : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hlower : Tendsto (fun n : Nat =>
      Real.log (sourceReactionCount n : ℝ) / (n : ℝ) -
        3 * Real.log (n : ℝ) / (n : ℝ)) atTop (𝓝 (Real.log 2)) := by
    have hthree : Tendsto (fun n : Nat =>
        3 * (Real.log (n : ℝ) / (n : ℝ))) atTop (𝓝 0) := by
      simpa only [mul_zero] using hlogn.const_mul 3
    simpa only [sub_zero, mul_div_assoc] using
      log_sourceReactionCount_normalized.sub hthree
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    hlower log_sourceReactionCount_normalized
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact sourcePolynomialCutoff_log_lower hn
  · filter_upwards [eventually_ge_atTop 4,
      eventually_sourcePolynomialCutoff_le_sourceReactionCount] with n hn hcut
    have hcutPos : (0 : ℝ) < (sourcePolynomialCutoff n : ℝ) := by
      exact_mod_cast (show 0 < sourcePolynomialCutoff n by
        simp [sourcePolynomialCutoff])
    have hRnat : 0 < sourceReactionCount n :=
      (pow_pos (by norm_num) n).trans_le (sourceReactionCount_bounds hn).1
    have hRPos : (0 : ℝ) < (sourceReactionCount n : ℝ) := by exact_mod_cast hRnat
    have hcutReal : (sourcePolynomialCutoff n : ℝ) ≤
        (sourceReactionCount n : ℝ) := by exact_mod_cast hcut
    have hlog := Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr hcutPos) (Set.mem_Ioi.mpr hRPos) hcutReal
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    exact div_le_div_of_nonneg_right hlog hnpos.le

/-- Positive logarithmic endpoint rate forces an integer threshold to diverge. -/
theorem tendsto_atTop_of_log_normalized_pos
    (m : Nat → Nat) (ell : ℝ) (hell : 0 < ell)
    (hlog : Tendsto (fun n : Nat => Real.log (m n : ℝ) / (n : ℝ))
      atTop (𝓝 ell)) :
    Tendsto m atTop atTop := by
  refine tendsto_atTop.2 fun K => ?_
  have hhalf : 0 < ell / 2 := half_pos hell
  have hratio : ∀ᶠ n : Nat in atTop,
      ell / 2 < Real.log (m n : ℝ) / (n : ℝ) :=
    hlog (Ioi_mem_nhds (by linarith))
  have hnlarge : ∀ᶠ n : Nat in atTop,
      Real.log (K + 1 : ℝ) < (n : ℝ) * (ell / 2) := by
    have htop : Tendsto (fun n : Nat => (n : ℝ) * (ell / 2)) atTop atTop :=
      (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_mul_const hhalf
    exact htop.eventually (eventually_gt_atTop (Real.log (K + 1 : ℝ)))
  filter_upwards [hratio, hnlarge, eventually_ge_atTop 1] with n hr hn hn1
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn1
  have hlogm : Real.log (K + 1 : ℝ) < Real.log (m n : ℝ) := by
    have := (lt_div_iff₀ hnreal).mp hr
    nlinarith
  by_contra hnot
  have hmK : m n < K := Nat.lt_of_not_ge hnot
  have hmK1 : (m n : ℝ) < (K + 1 : ℝ) := by
    exact_mod_cast hmK.trans (Nat.lt_succ_self K)
  have hmono : Real.log (m n : ℝ) ≤ Real.log (K + 1 : ℝ) := by
    by_cases hm0 : m n = 0
    · rw [hm0]
      have hKlog : 0 ≤ Real.log (K + 1 : ℝ) :=
        Real.log_nonneg (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le K))
      simp only [Nat.cast_zero, Real.log_zero]
      exact hKlog
    · exact Real.strictMonoOn_log.monotoneOn
        (Set.mem_Ioi.mpr (by exact_mod_cast Nat.pos_of_ne_zero hm0))
        (Set.mem_Ioi.mpr (by exact_mod_cast Nat.succ_pos K)) hmK1.le
  linarith

theorem sourcePolynomialCutoff_tendsto_atTop :
    Tendsto sourcePolynomialCutoff atTop atTop :=
  tendsto_atTop_of_log_normalized_pos sourcePolynomialCutoff (Real.log 2)
    (Real.log_pos one_lt_two) sourcePolynomialCutoff_log_normalized

theorem calibrated_sourcePolynomialCutoff_highTail
    (lam : ℝ) (hlam : 0 < lam) :
    Tendsto (fun n : Nat => 1 -
      sizeBiasedLogCdf (calibrationExponent lam hlam n)
        (sourceReactionCount n) (sourcePolynomialCutoff n))
      atTop (𝓝 0) :=
  calibrated_sizeBiasedHighTail lam hlam sourcePolynomialCutoff
    sourcePolynomialCutoff_log_normalized
    sourcePolynomialCutoff_tendsto_atTop
    eventually_sourcePolynomialCutoff_le_sourceReactionCount

end PowerLawSmallRAF
