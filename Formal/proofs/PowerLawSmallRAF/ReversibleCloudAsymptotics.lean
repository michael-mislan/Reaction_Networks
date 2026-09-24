import proofs.PowerLawSmallRAF.ReversibleCloudEvent
import proofs.PowerLawSmallRAF.SourcePolynomialCutoff

namespace PowerLawSmallRAF

open Filter Topology
open RAF.Polymer RAF.Concrete

/-- The residual-degree cutoff used for a fixed cloud of conditioned catalysts. -/
def sourceCloudDegreeCutoff (n : Nat) : Nat :=
  sourceReactionCount n / n ^ 3

/-- Floor-free catalogue ratio for the cloud cutoff.  Removing at most `n`
already exposed reactions costs only a factor two. -/
theorem sourceCloudCutoffRatio_le_two_div_cube
    {n s : Nat} (hn : 4 ≤ n) (hs : s ≤ n) :
    ((sourceCloudDegreeCutoff n : Nat) : ℝ) /
        (sourceReactionCount n - 1 - s + 1 : Nat) ≤
      2 / (n : ℝ) ^ 3 := by
  have hroom := sourceReactionCount_has_prefix_room hn
  have hscale : sourceCloudDegreeCutoff n * n ^ 3 ≤ sourceReactionCount n := by
    exact sourceLowDegree_has_cube_scale (by omega) (by simp [sourceCloudDegreeCutoff])
  have hprefix : 2 * s ≤ sourceReactionCount n := by omega
  have hdenNat : 0 < sourceReactionCount n - 1 - s + 1 := by omega
  have hnReal : 0 < (n : ℝ) ^ 3 := by positivity
  have hdenReal : 0 < ((sourceReactionCount n - 1 - s + 1 : Nat) : ℝ) := by
    positivity
  rw [div_le_div_iff₀ hdenReal hnReal]
  exact_mod_cast (show sourceCloudDegreeCutoff n * n ^ 3 ≤
      2 * (sourceReactionCount n - 1 - s + 1) by
    calc
      sourceCloudDegreeCutoff n * n ^ 3 ≤ sourceReactionCount n := hscale
      _ ≤ 2 * (sourceReactionCount n - 1 - s + 1) := by omega)

theorem sourceCloudCutoffRatio_mul_le
    {n k s : Nat} (hn : 4 ≤ n) (hs : s ≤ n) :
    (k : ℝ) * sourceCloudDegreeCutoff n /
        (sourceReactionCount n - 1 - s + 1 : Nat) ≤
      (k : ℝ) * (2 / (n : ℝ) ^ 3) := by
  rw [mul_div_assoc]
  exact mul_le_mul_of_nonneg_left
    (sourceCloudCutoffRatio_le_two_div_cube hn hs) (by positivity)

/-- A cloud can spend its first `k` distinct requirements for free, one per
conditioned hub.  Once those are factored off, ordinary geometric contraction
controls every trace length. -/
theorem shifted_geometric_code_term_le
    (A q : ℝ) (s k : Nat) (hA1 : 1 ≤ A) (hq : 0 ≤ q)
    (hAq : A * q ≤ 1) :
    A ^ s * q ^ (s - k) ≤ A ^ k := by
  have hA0 : 0 ≤ A := le_trans (by norm_num) hA1
  by_cases hsk : s ≤ k
  · rw [Nat.sub_eq_zero_of_le hsk, pow_zero, mul_one]
    exact pow_le_pow_right₀ hA1 hsk
  · have hks : k ≤ s := by omega
    have hsEq : s = k + (s - k) := by omega
    have hpow : (A * q) ^ (s - k) ≤ 1 :=
      pow_le_one₀ (mul_nonneg hA0 hq) hAq
    calc
      A ^ s * q ^ (s - k) =
          A ^ k * (A * q) ^ (s - k) := by
            rw [hsEq, pow_add, Nat.add_sub_cancel_left, mul_pow]
            ring
      _ ≤ A ^ k * 1 := mul_le_mul_of_nonneg_left hpow (pow_nonneg hA0 _)
      _ = A ^ k := mul_one _

theorem shifted_geometric_code_term_le_rho
    (A q ρ : ℝ) (s k : Nat) (hks : k ≤ s) (hA : 0 ≤ A)
    (hq : 0 ≤ q) (hAq : A * q ≤ ρ) :
    A ^ s * q ^ (s - k) ≤ A ^ k * ρ ^ (s - k) := by
  have hsEq : s = k + (s - k) := by omega
  calc
    A ^ s * q ^ (s - k) = A ^ k * (A * q) ^ (s - k) := by
      rw [hsEq, pow_add, Nat.add_sub_cancel_left, mul_pow]
      ring
    _ ≤ A ^ k * ρ ^ (s - k) :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (mul_nonneg hA hq) hAq _) (pow_nonneg hA _)

theorem fourth_pow_le_two_pow {n : Nat} (hn : 16 ≤ n) :
    n ^ 4 ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn16 ih =>
      have hn1 : 1 ≤ n := by omega
      have h16 : 16 * n ^ 3 ≤ n ^ 4 := by
        calc
          16 * n ^ 3 ≤ n * n ^ 3 := Nat.mul_le_mul_right _ hn16
          _ = n ^ 4 := by ring
      have h2 : n ^ 2 ≤ n ^ 3 := by
        exact Nat.pow_le_pow_right hn1 (by omega)
      have h1 : n ≤ n ^ 3 := by
        simpa only [pow_one] using Nat.pow_le_pow_right hn1 (by omega : 1 ≤ 3)
      have h0 : 1 ≤ n ^ 3 := Nat.one_le_pow _ _ hn1
      calc
        (n + 1) ^ 4 ≤ 2 * n ^ 4 := by nlinarith
        _ ≤ 2 * 2 ^ n := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (n + 1) := by rw [pow_succ]; omega

theorem sourceCloudCutoff_ge_n {n : Nat} (hn : 16 ≤ n) :
    n ≤ sourceCloudDegreeCutoff n := by
  rw [sourceCloudDegreeCutoff, Nat.le_div_iff_mul_le (by positivity : 0 < n ^ 3)]
  calc
    n * n ^ 3 = n ^ 4 := by ring
    _ ≤ 2 ^ n := fourth_pow_le_two_pow hn
    _ ≤ sourceReactionCount n := (sourceReactionCount_bounds (by omega)).1

theorem sourceCloudContraction
    {n k : Nat} (hk : 1 ≤ k) (hn : 288 * k ≤ n) :
    (sourceReversibleBranchCount n : ℝ) *
        ((k : ℝ) * (2 / (n : ℝ) ^ 3)) ≤ 1 / 2 := by
  have hn1 : 1 ≤ n := by omega
  have hn0 : (0 : ℝ) < n := by positivity
  have hnk : (288 : ℝ) * k ≤ n := by exact_mod_cast hn
  calc
    (sourceReversibleBranchCount n : ℝ) *
        ((k : ℝ) * (2 / (n : ℝ) ^ 3)) ≤
      (72 * (n : ℝ) ^ 2) * ((k : ℝ) * (2 / (n : ℝ) ^ 3)) := by
        gcongr
        exact sourceReversibleBranchCount_cast_le hn1
    _ = 144 * (k : ℝ) / n := by field_simp; ring
    _ ≤ 1 / 2 := by
      rw [div_le_div_iff₀ hn0 (by norm_num : (0 : ℝ) < 2)]
      nlinarith

noncomputable def sourceCloudSelfGenerationBudget (k n : Nat) : ℝ :=
  6 / (sourceMoleculeCount n : ℝ) +
    2 * (n : ℝ) * (sourceReversibleBranchCount n : ℝ) ^ k /
      (sourceMoleculeCount n : ℝ) +
    (sourceReversibleBranchCount n : ℝ) ^ k * (1 / 2 : ℝ) ^ (n - k)

theorem sourceLowDegreeCloudSelfGenerationEvent_le_budget
    {n k : Nat} (hk : 1 ≤ k) (hn : 288 * k ≤ n)
    (gateway : Fin k → Reaction n) (degree : Fin k → Nat)
    (hdegree : ∀ i, degree i ≤ sourceCloudDegreeCutoff n + 1) :
    ((canonicalCloudSelfGenerationEvent (by omega) gateway degree).card : ℝ) /
        (sourceMoleculeCount n * Fintype.card
          (VariableFixedSizeFibreConfig (sourceReactionCount n - 1)
            (fun i => degree i - 1))) ≤
      sourceCloudSelfGenerationBudget k n := by
  let C : ℝ := sourceReversibleBranchCount n
  let X : ℝ := sourceMoleculeCount n
  let q : ℝ := (k : ℝ) * (2 / (n : ℝ) ^ 3)
  have hn4 : 4 ≤ n := by omega
  have hkn : k ≤ n := by omega
  have hC1 : 1 ≤ C := by
    dsimp [C, sourceReversibleBranchCount]
    push_cast
    calc
      (1 : ℝ) = 1 * 1 := by norm_num
      _ ≤ (6 + 2 * (n : ℝ)) * (6 + 3 * (n : ℝ)) := by
        exact mul_le_mul
          (by
            have hn0 : (0 : ℝ) ≤ n := by positivity
            linarith)
          (by
            have hn0 : (0 : ℝ) ≤ n := by positivity
            linarith)
          (by norm_num) (by positivity)
  have hC0 : 0 ≤ C := le_trans (by norm_num) hC1
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hcontractHalf : C * q ≤ 1 / 2 := by
    exact sourceCloudContraction hk hn
  have hcontract : C * q ≤ 1 := hcontractHalf.trans (by norm_num)
  have hq1 : q ≤ 1 := by
    calc
      q = 1 * q := by ring
      _ ≤ C * q := mul_le_mul_of_nonneg_right hC1 hq0
      _ ≤ 1 := hcontract
  have hbase : ∀ s ≤ n, (k : ℝ) * sourceCloudDegreeCutoff n /
      (sourceReactionCount n - 1 - s + 1 : Nat) ≤ 1 := by
    intro s hs
    exact (sourceCloudCutoffRatio_mul_le hn4 hs).trans hq1
  have hDroom : sourceCloudDegreeCutoff n ≤ sourceReactionCount n - 1 := by
    have hcut := sourcePolynomialCutoff_le_sourceReactionCount hn4
    dsimp [sourcePolynomialCutoff, sourceCloudDegreeCutoff] at hcut ⊢
    omega
  have hfirst :
      (∑ s ∈ Finset.Icc 1 n,
        ((2 * sourceReversibleBranchCount n ^ s : Nat) : ℝ) /
          sourceMoleculeCount n *
            (((k : ℝ) * sourceCloudDegreeCutoff n /
              (sourceReactionCount n - 1 - s + 1 : Nat)) ^ (s - k))) ≤
        2 * (n : ℝ) * C ^ k / X := by
    have hterm : ∀ s ∈ Finset.Icc 1 n,
        ((2 * sourceReversibleBranchCount n ^ s : Nat) : ℝ) /
          sourceMoleculeCount n *
            (((k : ℝ) * sourceCloudDegreeCutoff n /
              (sourceReactionCount n - 1 - s + 1 : Nat)) ^ (s - k)) ≤
          2 * C ^ k / X := by
      intro s hsRange
      have hs : s ≤ n := (Finset.mem_Icc.mp hsRange).2
      let b : ℝ := (k : ℝ) * sourceCloudDegreeCutoff n /
        (sourceReactionCount n - 1 - s + 1 : Nat)
      have hb0 : 0 ≤ b := by dsimp [b]; positivity
      have hbq : b ≤ q := sourceCloudCutoffRatio_mul_le hn4 hs
      have hpowb : b ^ (s - k) ≤ q ^ (s - k) :=
        pow_le_pow_left₀ hb0 hbq _
      have hcore : C ^ s * b ^ (s - k) ≤ C ^ k := by
        calc
          C ^ s * b ^ (s - k) ≤ C ^ s * q ^ (s - k) :=
            mul_le_mul_of_nonneg_left hpowb (pow_nonneg hC0 _)
          _ ≤ C ^ k := shifted_geometric_code_term_le C q s k hC1 hq0 hcontract
      dsimp [C, X] at hcore ⊢
      norm_num only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
      have hX0 : (0 : ℝ) ≤ sourceMoleculeCount n := by positivity
      calc
        2 * (sourceReversibleBranchCount n : ℝ) ^ s /
              sourceMoleculeCount n *
            ((k : ℝ) * sourceCloudDegreeCutoff n /
              (sourceReactionCount n - 1 - s + 1 : Nat)) ^ (s - k) =
            2 * ((sourceReversibleBranchCount n : ℝ) ^ s *
              ((k : ℝ) * sourceCloudDegreeCutoff n /
                (sourceReactionCount n - 1 - s + 1 : Nat)) ^ (s - k)) /
              sourceMoleculeCount n := by ring
        _ ≤ 2 * (sourceReversibleBranchCount n : ℝ) ^ k /
              sourceMoleculeCount n := by
            exact div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_left hcore (by norm_num)) hX0
    calc
      (∑ s ∈ Finset.Icc 1 n,
          ((2 * sourceReversibleBranchCount n ^ s : Nat) : ℝ) /
            sourceMoleculeCount n *
              (((k : ℝ) * sourceCloudDegreeCutoff n /
                (sourceReactionCount n - 1 - s + 1 : Nat)) ^ (s - k))) ≤
          ∑ _s ∈ Finset.Icc 1 n, 2 * C ^ k / X := by
            exact Finset.sum_le_sum hterm
      _ = (n : ℝ) * (2 * C ^ k / X) := by simp
      _ = 2 * (n : ℝ) * C ^ k / X := by ring
  have hsurvival :
      ((sourceReversibleBranchCount n ^ n : Nat) : ℝ) *
          (((k : ℝ) * sourceCloudDegreeCutoff n /
            (sourceReactionCount n - 1 - n + 1 : Nat)) ^ (n - k)) ≤
        C ^ k * (1 / 2 : ℝ) ^ (n - k) := by
    let b : ℝ := (k : ℝ) * sourceCloudDegreeCutoff n /
      (sourceReactionCount n - 1 - n + 1 : Nat)
    have hb0 : 0 ≤ b := by dsimp [b]; positivity
    have hbq : b ≤ q := sourceCloudCutoffRatio_mul_le hn4 le_rfl
    have hpowb : b ^ (n - k) ≤ q ^ (n - k) := pow_le_pow_left₀ hb0 hbq _
    have hmain := shifted_geometric_code_term_le_rho C q (1 / 2) n k
      hkn hC0 hq0 hcontractHalf
    dsimp [C] at hmain ⊢
    rw [Nat.cast_pow]
    exact (mul_le_mul_of_nonneg_left hpowb (pow_nonneg hC0 _)).trans hmain
  refine (canonicalCloudSelfGenerationEvent_uniformMass_le
    (by omega) gateway degree hdegree (sourceCloudCutoff_ge_n (by omega))
      hDroom hbase).trans ?_
  dsimp [sourceCloudSelfGenerationBudget, C, X]
  exact add_le_add (add_le_add le_rfl hfirst) hsurvival

theorem sourcePolynomial_div_moleculeCount_tendsto_zero (m : Nat) :
    Tendsto (fun n : Nat => (n : ℝ) ^ m / (sourceMoleculeCount n : ℝ))
      atTop (𝓝 0) := by
  have hpoly := tendsto_pow_const_div_const_pow_of_one_lt m
    (by norm_num : (1 : ℝ) < 2)
  have hhalf : Tendsto (fun n : Nat =>
      (((n : ℝ) ^ m / (2 : ℝ) ^ n) / 2)) atTop (𝓝 0) := by
    simpa only [zero_div] using hpoly.div_const 2
  have hpower : Tendsto (fun n : Nat =>
      ((2 ^ (n + 1) : Nat) : ℝ) / (sourceMoleculeCount n : ℝ))
      atTop (𝓝 1) := sourcePower_div_moleculeCount_tendsto_one
  have hmul := hhalf.mul hpower
  have hmul' : Tendsto (fun n : Nat =>
      (((n : ℝ) ^ m / (2 : ℝ) ^ n) / 2) *
        (((2 ^ (n + 1) : Nat) : ℝ) /
          (sourceMoleculeCount n : ℝ))) atTop (𝓝 0) := by
    simpa only [zero_mul] using hmul
  apply hmul'.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hX : (sourceMoleculeCount n : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt
      ((pow_pos (by norm_num) n).trans_le (sourceMoleculeCount_bounds hn).1)
  norm_num [Nat.cast_pow, pow_succ]
  field_simp

theorem sourceCloudSelfGenerationBudget_tendsto_zero (k : Nat) :
    Tendsto (sourceCloudSelfGenerationBudget k) atTop (𝓝 0) := by
  have hXreal : Tendsto (fun n : Nat => (sourceMoleculeCount n : ℝ))
      atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).comp sourceMoleculeCount_tendsto_atTop
  have hfood : Tendsto (fun n : Nat => 6 / (sourceMoleculeCount n : ℝ))
      atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_const_nhds.mul hXreal.inv_tendsto_atTop)
  have hfirstUpper : Tendsto (fun n : Nat =>
      (2 * 72 ^ k : ℝ) * ((n : ℝ) ^ (2 * k + 1) /
        (sourceMoleculeCount n : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (sourcePolynomial_div_moleculeCount_tendsto_zero (2 * k + 1)).const_mul
        (2 * 72 ^ k : ℝ)
  have hfirst : Tendsto (fun n : Nat =>
      2 * (n : ℝ) * (sourceReversibleBranchCount n : ℝ) ^ k /
        (sourceMoleculeCount n : ℝ)) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (tendsto_const_nhds : Tendsto (fun _ : Nat => (0 : ℝ)) atTop (𝓝 0))
      hfirstUpper
    · filter_upwards with n
      positivity
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have hC := sourceReversibleBranchCount_cast_le hn
      have hCpow : (sourceReversibleBranchCount n : ℝ) ^ k ≤
          (72 * (n : ℝ) ^ 2) ^ k :=
        pow_le_pow_left₀ (by positivity) hC _
      have hX0 : (0 : ℝ) ≤ sourceMoleculeCount n := by positivity
      calc
        2 * (n : ℝ) * (sourceReversibleBranchCount n : ℝ) ^ k /
            (sourceMoleculeCount n : ℝ) ≤
          2 * (n : ℝ) * (72 * (n : ℝ) ^ 2) ^ k /
            (sourceMoleculeCount n : ℝ) := by
              gcongr
        _ = (2 * 72 ^ k : ℝ) * ((n : ℝ) ^ (2 * k + 1) /
            (sourceMoleculeCount n : ℝ)) := by
              rw [mul_pow]
              ring
  have hsurvivalUpper : Tendsto (fun n : Nat =>
      (144 : ℝ) ^ k * ((n : ℝ) ^ (2 * k) / (2 : ℝ) ^ n))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_const_div_const_pow_of_one_lt (2 * k)
        (by norm_num : (1 : ℝ) < 2)).const_mul ((144 : ℝ) ^ k)
  have hsurvival : Tendsto (fun n : Nat =>
      (sourceReversibleBranchCount n : ℝ) ^ k *
        (1 / 2 : ℝ) ^ (n - k)) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (tendsto_const_nhds : Tendsto (fun _ : Nat => (0 : ℝ)) atTop (𝓝 0))
      hsurvivalUpper
    · filter_upwards with n
      positivity
    · filter_upwards [eventually_ge_atTop (max 1 k)] with n hn
      have hn1 : 1 ≤ n := (Nat.le_max_left 1 k).trans hn
      have hkn : k ≤ n := (Nat.le_max_right 1 k).trans hn
      have hC := sourceReversibleBranchCount_cast_le hn1
      have hCpow : (sourceReversibleBranchCount n : ℝ) ^ k ≤
          (72 * (n : ℝ) ^ 2) ^ k :=
        pow_le_pow_left₀ (by positivity) hC _
      have hhalf : (1 / 2 : ℝ) ^ (n - k) =
          (2 : ℝ) ^ k / (2 : ℝ) ^ n := by
        conv_rhs => rw [show n = (n - k) + k by omega, pow_add]
        field_simp
        rw [← mul_pow]
        norm_num
      rw [hhalf]
      calc
        (sourceReversibleBranchCount n : ℝ) ^ k *
            ((2 : ℝ) ^ k / (2 : ℝ) ^ n) ≤
          (72 * (n : ℝ) ^ 2) ^ k *
            ((2 : ℝ) ^ k / (2 : ℝ) ^ n) := by gcongr
        _ = (144 : ℝ) ^ k * ((n : ℝ) ^ (2 * k) / (2 : ℝ) ^ n) := by
          rw [mul_pow]
          rw [show (144 : ℝ) ^ k = (72 : ℝ) ^ k * (2 : ℝ) ^ k by
            rw [← mul_pow]
            norm_num]
          ring
  simpa only [sourceCloudSelfGenerationBudget, add_zero] using
    (hfood.add hfirst).add hsurvival

end PowerLawSmallRAF
