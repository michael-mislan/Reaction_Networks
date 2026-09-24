import proofs.PowerLawSmallRAF.TwoStratumEntropyOptimization
import proofs.PowerLawSmallRAF.ReversibleCloudAsymptotics

namespace PowerLawSmallRAF

open Filter Topology RAF RAF.Polymer

/-- For each fixed support cutoff, the optimized two-stratum endpoint vanishes
under exact mean-linear calibration.  This is the exponential-over-polynomial
input used to extract a growing certified cutoff. -/
theorem calibrated_sourceTwoStratumEndpoint_fixed_tendsto_zero
    (lam : ℝ) (hlam : 0 < lam) (m : Nat) :
    Tendsto (fun n : Nat =>
      sourceTwoStratumEndpoint n m
        (powerLawMoleculeGatewayHit (calibrationExponent lam hlam n)
          (sourceReactionCount n) 1)) atTop (𝓝 0) := by
  let p : Nat → ℝ := fun n =>
    powerLawMoleculeGatewayHit (calibrationExponent lam hlam n)
      (sourceReactionCount n) 1
  let q : Nat := 6 + 2 * m
  let C : Nat := q * (q + 1)
  let K : ℝ := (m : ℝ) * ((q : ℝ) + (q ^ m : Nat)) * (C ^ m : Nat)
  have hXp : Tendsto (fun n : Nat =>
      (sourceMoleculeCount n : ℝ) * p n) atTop (𝓝 lam) := by
    simpa [p] using
      calibratedPowerLawMoleculeGatewayHit_scaled lam hlam 1 (by omega)
  have hpoly := sourcePolynomial_div_moleculeCount_tendsto_zero m
  have hupper : Tendsto (fun n : Nat =>
      K * ((n : ℝ) ^ m / (sourceMoleculeCount n : ℝ)) *
        ((sourceMoleculeCount n : ℝ) * p n)) atTop (𝓝 0) := by
    simpa only [zero_mul, mul_zero] using (hpoly.const_mul K).mul hXp
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _ : Nat => (0 : ℝ)) atTop (𝓝 0))
    hupper
  · filter_upwards [eventually_ge_atTop 4,
      (calibrationExponent_tendsto_two lam hlam)
        (Ioi_mem_nhds one_lt_two)] with n hn ha
    let k : Fin n := ⟨1, by omega⟩
    let w : Word (k.val + 1) := ⟨0, by simp [k]⟩
    let s : Fin k.val := ⟨0, by simp [k]⟩
    let r0 : Reaction n := ⟨k, (w, s)⟩
    have hp := source_gatewayHit_nonneg_le_one
      (calibrationExponent lam hlam n) ha hn r0
    dsimp [sourceTwoStratumEndpoint, sourceTwoStratumTerm, p]
    apply mul_nonneg (Nat.cast_nonneg _)
    apply mul_nonneg (by positivity)
    exact add_nonneg
      (mul_nonneg (Nat.cast_nonneg _) hp.1)
      (mul_nonneg (by positivity) (sq_nonneg _))
  · filter_upwards [eventually_ge_atTop 4,
      (calibrationExponent_tendsto_two lam hlam)
        (Ioi_mem_nhds one_lt_two)] with n hn ha
    let k : Fin n := ⟨1, by omega⟩
    let w : Word (k.val + 1) := ⟨0, by simp [k]⟩
    let s : Fin k.val := ⟨0, by simp [k]⟩
    let r0 : Reaction n := ⟨k, (w, s)⟩
    have hp := source_gatewayHit_nonneg_le_one
      (calibrationExponent lam hlam n) ha hn r0
    have hpSq : (p n) ^ 2 ≤ p n := by
      simpa [pow_two] using mul_le_of_le_one_right hp.1 hp.2
    have hqn : q + n ≤ (q + 1) * n := by
      calc
        q + n ≤ q * n + n := Nat.add_le_add_right
          (Nat.le_mul_of_pos_right q (by omega)) n
        _ = (q + 1) * n := by ring
    have hbranch : sourceReversibleBranchCountAt n m ≤ C * n := by
      change q * (q + n) ≤ q * (q + 1) * n
      calc
        q * (q + n) ≤ q * ((q + 1) * n) := Nat.mul_le_mul_left q hqn
        _ = q * (q + 1) * n := by ring
    have hbranchPow : sourceReversibleBranchCountAt n m ^ m ≤
        (C * n) ^ m := Nat.pow_le_pow_left hbranch m
    have hinside : (q : ℝ) * p n + (q ^ m : Nat) * (p n) ^ 2 ≤
        ((q : ℝ) + (q ^ m : Nat)) * p n := by
      calc
        (q : ℝ) * p n + (q ^ m : Nat) * (p n) ^ 2 ≤
            (q : ℝ) * p n + (q ^ m : Nat) * p n := by
              gcongr
        _ = ((q : ℝ) + (q ^ m : Nat)) * p n := by ring
    have hX : (sourceMoleculeCount n : ℝ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt
        ((pow_pos (by norm_num) n).trans_le (sourceMoleculeCount_bounds (by omega)).1)
    calc
      sourceTwoStratumEndpoint n m (p n) =
          (m : ℝ) * (sourceReversibleBranchCountAt n m ^ m : Nat) *
            ((q : ℝ) * p n + (q ^ m : Nat) * (p n) ^ 2) := by
              simp [sourceTwoStratumEndpoint, sourceTwoStratumTerm, q]
              ring
      _ ≤ (m : ℝ) * ((C * n) ^ m : Nat) *
            (((q : ℝ) + (q ^ m : Nat)) * p n) := by
              apply mul_le_mul
              · exact mul_le_mul_of_nonneg_left
                  (by exact_mod_cast hbranchPow) (Nat.cast_nonneg _)
              · exact hinside
              · exact add_nonneg (mul_nonneg (Nat.cast_nonneg _) hp.1)
                  (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg (p n)))
              · positivity
      _ = K * ((n : ℝ) ^ m / (sourceMoleculeCount n : ℝ)) *
            ((sourceMoleculeCount n : ℝ) * p n) := by
              dsimp [K]
              push_cast
              field_simp
              ring

/-- Largest cutoff certified directly by the optimized endpoint.  The
threshold depends on `m`, not on `n`, so every fixed `m` eventually qualifies. -/
noncomputable def sourceCertifiedGrowingCutoff
    (lam : ℝ) (hlam : 0 < lam) (n : Nat) : Nat := by
  classical
  let p := powerLawMoleculeGatewayHit (calibrationExponent lam hlam n)
    (sourceReactionCount n) 1
  let good := (Finset.Icc 0 n).filter fun m =>
    sourceTwoStratumEndpoint n m p ≤ 1 / ((m + 1 : Nat) : ℝ)
  exact good.max' (by
    refine ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr (by omega), ?_⟩⟩
    simp [sourceTwoStratumEndpoint])

theorem sourceCertifiedGrowingCutoff_spec
    (lam : ℝ) (hlam : 0 < lam) (n : Nat) :
    sourceTwoStratumEndpoint n (sourceCertifiedGrowingCutoff lam hlam n)
        (powerLawMoleculeGatewayHit (calibrationExponent lam hlam n)
          (sourceReactionCount n) 1) ≤
      1 / (((sourceCertifiedGrowingCutoff lam hlam n) + 1 : Nat) : ℝ) := by
  classical
  let p := powerLawMoleculeGatewayHit (calibrationExponent lam hlam n)
    (sourceReactionCount n) 1
  let good := (Finset.Icc 0 n).filter fun m =>
    sourceTwoStratumEndpoint n m p ≤ 1 / ((m + 1 : Nat) : ℝ)
  have hne : good.Nonempty := by
    refine ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr (by omega), ?_⟩⟩
    simp [sourceTwoStratumEndpoint]
  have hm := Finset.max'_mem good hne
  exact (Finset.mem_filter.mp hm).2

theorem sourceCertifiedGrowingCutoff_tendsto_atTop
    (lam : ℝ) (hlam : 0 < lam) :
    Tendsto (sourceCertifiedGrowingCutoff lam hlam) atTop atTop := by
  classical
  refine tendsto_atTop.2 fun M => ?_
  have hzero := calibrated_sourceTwoStratumEndpoint_fixed_tendsto_zero lam hlam M
  have hsmall : ∀ᶠ n : Nat in atTop,
      sourceTwoStratumEndpoint n M
          (powerLawMoleculeGatewayHit (calibrationExponent lam hlam n)
            (sourceReactionCount n) 1) < 1 / (((M + 1 : Nat) : ℝ)) :=
    hzero (Iio_mem_nhds (by positivity))
  filter_upwards [hsmall, eventually_ge_atTop M] with n hsmall hn
  let p := powerLawMoleculeGatewayHit (calibrationExponent lam hlam n)
    (sourceReactionCount n) 1
  let good := (Finset.Icc 0 n).filter fun m =>
    sourceTwoStratumEndpoint n m p ≤ 1 / ((m + 1 : Nat) : ℝ)
  have hMmem : M ∈ good := Finset.mem_filter.mpr
    ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le M, hn⟩, hsmall.le⟩
  have hne : good.Nonempty := ⟨M, hMmem⟩
  exact Finset.le_max' good M hMmem

/-- A source-level no-small-RAF theorem at a rigorously growing cutoff. -/
theorem calibrated_sourceCertifiedGrowingCutoff_extinction
    (lam : ℝ) (hlam : 0 < lam) :
    Tendsto (fun n : Nat => sourceBoundedRevRAFProbability
      (calibrationExponent lam hlam n) n
      (sourceCertifiedGrowingCutoff lam hlam n)) atTop (𝓝 0) := by
  have hcut := sourceCertifiedGrowingCutoff_tendsto_atTop lam hlam
  have hupper : Tendsto (fun n : Nat =>
      1 / (((sourceCertifiedGrowingCutoff lam hlam n) + 1 : Nat) : ℝ))
      atTop (𝓝 0) := by
    have hcast0 : Tendsto (fun n : Nat =>
        (sourceCertifiedGrowingCutoff lam hlam n : ℝ)) atTop atTop :=
      (tendsto_natCast_atTop_atTop (R := ℝ)).comp hcut
    have hcast : Tendsto (fun n : Nat =>
        (((sourceCertifiedGrowingCutoff lam hlam n) + 1 : Nat) : ℝ))
        atTop atTop := by
      simpa using tendsto_atTop_add_const_right atTop (1 : ℝ) hcast0
    simpa only [one_div] using hcast.inv_tendsto_atTop
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _ : Nat => (0 : ℝ)) atTop (𝓝 0))
    hupper
  · filter_upwards [eventually_ge_atTop 4,
      (calibrationExponent_tendsto_two lam hlam)
        (Ioi_mem_nhds one_lt_two)] with n hn ha
    rw [sourceBoundedRevRAFProbability]
    apply Finset.sum_nonneg
    intro config hconfig
    split_ifs
    · exact sourcePowerLawConfigWeight_nonneg
        (calibrationExponent lam hlam n) n ha config
    · exact le_rfl
  · filter_upwards [eventually_ge_atTop 4,
      (calibrationExponent_tendsto_two lam hlam)
        (Ioi_mem_nhds one_lt_two)] with n hn ha
    exact (sourceBoundedRevRAFProbability_le_two_stratum_endpoint
      (calibrationExponent lam hlam n) ha hn).trans
        (sourceCertifiedGrowingCutoff_spec lam hlam n)

end PowerLawSmallRAF
