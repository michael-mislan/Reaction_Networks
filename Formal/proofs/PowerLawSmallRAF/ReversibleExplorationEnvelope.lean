import proofs.PowerLawSmallRAF.SourceLowDegreeScale

namespace PowerLawSmallRAF

open Filter Topology

/-- At any of the first `n` productive reversible steps there are at most this
many encodings: choose either two available inputs, or an available product
and a split position.  The deliberately loose product covers both cases. -/
def sourceReversibleBranchCount (n : Nat) : Nat :=
  (6 + 2 * n) * (6 + 3 * n)

/-- Fixed-length reversible exploration codes.  Semantic legality is imposed
later; this ambient type is only the finite counting envelope. -/
abbrev ReversibleExplorationCode (n s : Nat) :=
  Fin s → Fin (sourceReversibleBranchCount n)

theorem card_reversibleExplorationCode (n s : Nat) :
    Fintype.card (ReversibleExplorationCode n s) =
      sourceReversibleBranchCount n ^ s := by
  simp

/-- First-hit part of the stopped exploration union bound. -/
noncomputable def gatewayReversibleFirstHitEnvelope
    (targetCount reactionCount degree n : Nat) : ℝ :=
  ∑ s ∈ Finset.Icc 1 (min n degree),
    ((sourceReversibleBranchCount n ^ s : Nat) : ℝ) / targetCount *
      gatewayConditionedContain reactionCount (s - 1) degree

/-- Survival part: if the target has not appeared after `n` productive steps,
the first `n` distinct channels themselves form a certificate. -/
noncomputable def gatewayReversibleSurvivalEnvelope
    (reactionCount degree n : Nat) : ℝ :=
  if n ≤ degree then
    ((sourceReversibleBranchCount n ^ n : Nat) : ℝ) *
      gatewayConditionedContain reactionCount (n - 1) degree
  else 0

theorem gatewayReversibleFirstHitEnvelope_le_uniformTerm
    (targetCount reactionCount degree n : Nat) (q : ℝ)
    (hq : 0 ≤ q)
    (hcontract : (sourceReversibleBranchCount n : ℝ) * q ≤ 1)
    (hcontain : ∀ s ∈ Finset.Icc 1 (min n degree),
      gatewayConditionedContain reactionCount (s - 1) degree ≤ q ^ (s - 1)) :
    gatewayReversibleFirstHitEnvelope targetCount reactionCount degree n ≤
      (n : ℝ) * ((sourceReversibleBranchCount n : ℝ) / targetCount) := by
  dsimp [gatewayReversibleFirstHitEnvelope]
  let A : ℝ := sourceReversibleBranchCount n
  calc
    (∑ s ∈ Finset.Icc 1 (min n degree),
        ((sourceReversibleBranchCount n ^ s : Nat) : ℝ) / targetCount *
          gatewayConditionedContain reactionCount (s - 1) degree) ≤
        ∑ _s ∈ Finset.Icc 1 (min n degree), A / targetCount := by
      apply Finset.sum_le_sum
      intro s hs
      have hs1 : 1 ≤ s := (Finset.mem_Icc.mp hs).1
      have htarget0 : (0 : ℝ) ≤ targetCount := by positivity
      calc
        ((sourceReversibleBranchCount n ^ s : Nat) : ℝ) / targetCount *
            gatewayConditionedContain reactionCount (s - 1) degree =
            (A ^ s / targetCount) *
              gatewayConditionedContain reactionCount (s - 1) degree := by
                norm_num [A, Nat.cast_pow]
        _ ≤ (A ^ s / targetCount) * q ^ (s - 1) := by
          apply mul_le_mul_of_nonneg_left (hcontain s hs)
          exact div_nonneg (pow_nonneg (by positivity) _) htarget0
        _ = (A ^ s * q ^ (s - 1)) / targetCount := by ring
        _ ≤ A / targetCount :=
          div_le_div_of_nonneg_right
            (geometric_code_term_le A q s hs1 (by positivity) hq hcontract)
            htarget0
    _ = ((min n degree : Nat) : ℝ) * (A / targetCount) := by simp
    _ ≤ (n : ℝ) * (A / targetCount) := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast Nat.min_le_left n degree
      · exact div_nonneg (by positivity) (by positivity)

theorem sourceReversibleBranchCount_cast_le {n : Nat} (hn : 1 ≤ n) :
    (sourceReversibleBranchCount n : ℝ) ≤ 72 * (n : ℝ) ^ 2 := by
  norm_num [sourceReversibleBranchCount]
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  nlinarith [sq_nonneg ((n : ℝ) - 1)]

theorem sourceReversibleContraction {n : Nat} (hn : 144 ≤ n) :
    (sourceReversibleBranchCount n : ℝ) * (2 / (n : ℝ) ^ 3) ≤ 1 := by
  have hn1 : 1 ≤ n := by omega
  have hn0 : (0 : ℝ) < n := by positivity
  calc
    (sourceReversibleBranchCount n : ℝ) * (2 / (n : ℝ) ^ 3) ≤
        (72 * (n : ℝ) ^ 2) * (2 / (n : ℝ) ^ 3) := by
      gcongr
      exact sourceReversibleBranchCount_cast_le hn1
    _ = 144 / (n : ℝ) := by field_simp; ring
    _ ≤ 1 := by
      rw [div_le_one₀ hn0]
      exact_mod_cast hn

/-- The first-hit polynomial prefactor is negligible relative to the number
of possible marked binary molecules. -/
theorem sourceReversibleFirstHitBudget_tendsto_zero :
    Tendsto (fun n : Nat =>
      (n : ℝ) * (sourceReversibleBranchCount n : ℝ) /
        (sourceMoleculeCount n : ℝ)) atTop (𝓝 0) := by
  have hpoly : Tendsto (fun n : Nat =>
      72 * ((n : ℝ) * ((n : ℝ) + 6) ^ 2 /
        (sourceMoleculeCount n : ℝ)))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using sourceGrammarBudget_tendsto_zero.const_mul 72
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _ : Nat => (0 : ℝ)) atTop (𝓝 0)) hpoly
  · filter_upwards with n
    positivity
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hX : 0 ≤ (sourceMoleculeCount n : ℝ) := by positivity
    calc
      (n : ℝ) * (sourceReversibleBranchCount n : ℝ) /
          (sourceMoleculeCount n : ℝ) ≤
          (n : ℝ) * (72 * (n : ℝ) ^ 2) /
            (sourceMoleculeCount n : ℝ) := by
        apply div_le_div_of_nonneg_right _ hX
        apply mul_le_mul_of_nonneg_left (sourceReversibleBranchCount_cast_le hn)
        positivity
      _ ≤ 72 * ((n : ℝ) * ((n : ℝ) + 6) ^ 2 /
          (sourceMoleculeCount n : ℝ)) := by
        have hnR : (0 : ℝ) ≤ n := by positivity
        have hsquare : (n : ℝ) ^ 2 ≤ ((n : ℝ) + 6) ^ 2 := by nlinarith
        have hnum : (n : ℝ) * (72 * (n : ℝ) ^ 2) ≤
            72 * ((n : ℝ) * ((n : ℝ) + 6) ^ 2) := by nlinarith
        calc
          (n : ℝ) * (72 * (n : ℝ) ^ 2) /
              (sourceMoleculeCount n : ℝ) ≤
              (72 * ((n : ℝ) * ((n : ℝ) + 6) ^ 2)) /
                (sourceMoleculeCount n : ℝ) :=
            div_le_div_of_nonneg_right hnum hX
          _ = 72 * ((n : ℝ) * ((n : ℝ) + 6) ^ 2 /
              (sourceMoleculeCount n : ℝ)) := by ring

theorem gatewayReversibleFirstHitEnvelope_nonneg
    (targetCount reactionCount degree n : Nat) :
    0 ≤ gatewayReversibleFirstHitEnvelope targetCount reactionCount degree n := by
  dsimp [gatewayReversibleFirstHitEnvelope]
  apply Finset.sum_nonneg
  intro s hs
  exact mul_nonneg (div_nonneg (by positivity) (by positivity))
    (div_nonneg (by positivity) (by positivity))

theorem sourceLowDegreeReversibleFirstHitEnvelope_le_budget
    {n degree : Nat} (hn : 144 ≤ n) (hdegree1 : 1 ≤ degree)
    (hdegree : degree ≤ sourceReactionCount n / n ^ 3) :
    gatewayReversibleFirstHitEnvelope (sourceMoleculeCount n)
        (sourceReactionCount n) degree n ≤
      (n : ℝ) * ((sourceReversibleBranchCount n : ℝ) /
        (sourceMoleculeCount n : ℝ)) := by
  have hdegreeR : degree ≤ sourceReactionCount n :=
    hdegree.trans (Nat.div_le_self _ _)
  apply gatewayReversibleFirstHitEnvelope_le_uniformTerm
    (sourceMoleculeCount n) (sourceReactionCount n) degree n
    (2 / (n : ℝ) ^ 3) (by positivity) (sourceReversibleContraction hn)
  intro s hs
  have hsn : s ≤ n := (Finset.mem_Icc.mp hs).2.trans (Nat.min_le_left _ _)
  have hsd : s ≤ degree :=
    (Finset.mem_Icc.mp hs).2.trans (Nat.min_le_right _ _)
  exact (gatewayConditionedContain_le_power
    (sourceReactionCount n) (s - 1) degree hdegree1 hdegreeR (by omega)).trans
      (pow_le_pow_left₀ (div_nonneg (by positivity) (by positivity))
        (sourceConditionedRatio_le_two_div_cube (by omega) hsn hdegree) (s - 1))

theorem sourceLowDegreeReversibleFirstHitEnvelope_tendsto_zero
    (degree : Nat → Nat)
    (hdegree1 : ∀ᶠ n : Nat in atTop, 1 ≤ degree n)
    (hdegree : ∀ᶠ n : Nat in atTop,
      degree n ≤ sourceReactionCount n / n ^ 3) :
    Tendsto (fun n : Nat => gatewayReversibleFirstHitEnvelope
      (sourceMoleculeCount n) (sourceReactionCount n) (degree n) n)
      atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _ : Nat => (0 : ℝ)) atTop (𝓝 0))
    sourceReversibleFirstHitBudget_tendsto_zero
  · filter_upwards with n
    exact gatewayReversibleFirstHitEnvelope_nonneg _ _ _ _
  · filter_upwards [eventually_ge_atTop 144, hdegree1, hdegree] with n hn hd1 hd
    simpa only [mul_div_assoc] using
      sourceLowDegreeReversibleFirstHitEnvelope_le_budget hn hd1 hd

theorem sourceReversibleHalfContraction {n : Nat} (hn : 288 ≤ n) :
    (sourceReversibleBranchCount n : ℝ) * (2 / (n : ℝ) ^ 3) ≤ 1 / 2 := by
  have hn1 : 1 ≤ n := by omega
  have hn0 : (0 : ℝ) < n := by positivity
  calc
    (sourceReversibleBranchCount n : ℝ) * (2 / (n : ℝ) ^ 3) ≤
        (72 * (n : ℝ) ^ 2) * (2 / (n : ℝ) ^ 3) := by
      gcongr
      exact sourceReversibleBranchCount_cast_le hn1
    _ = 144 / (n : ℝ) := by field_simp; ring
    _ ≤ 1 / 2 := by
      rw [div_le_div_iff₀ hn0 (by norm_num : (0 : ℝ) < 2)]
      norm_num
      exact_mod_cast hn

theorem sourceLowDegreeReversibleSurvivalEnvelope_le_budget
    {n degree : Nat} (hn : 288 ≤ n) (hdegree1 : 1 ≤ degree)
    (hdegree : degree ≤ sourceReactionCount n / n ^ 3) :
    gatewayReversibleSurvivalEnvelope (sourceReactionCount n) degree n ≤
      144 * (n : ℝ) ^ 2 / (2 : ℝ) ^ n := by
  rw [gatewayReversibleSurvivalEnvelope]
  split_ifs with hnd
  · have hdegreeR : degree ≤ sourceReactionCount n :=
      hdegree.trans (Nat.div_le_self _ _)
    have hcontain := gatewayConditionedContain_le_power
      (sourceReactionCount n) (n - 1) degree hdegree1 hdegreeR (by omega)
    have hratio := sourceConditionedRatio_le_two_div_cube
      (by omega : 4 ≤ n) (le_refl n) hdegree
    have hcontain' : gatewayConditionedContain (sourceReactionCount n)
        (n - 1) degree ≤ (2 / (n : ℝ) ^ 3) ^ (n - 1) :=
      hcontain.trans (pow_le_pow_left₀
        (div_nonneg (by positivity) (by positivity)) hratio (n - 1))
    have hC0 : 0 ≤ (sourceReversibleBranchCount n : ℝ) := by positivity
    have hq0 : 0 ≤ 2 / (n : ℝ) ^ 3 := by positivity
    calc
      ((sourceReversibleBranchCount n ^ n : Nat) : ℝ) *
          gatewayConditionedContain (sourceReactionCount n) (n - 1) degree ≤
          (sourceReversibleBranchCount n : ℝ) ^ n *
            (2 / (n : ℝ) ^ 3) ^ (n - 1) := by
        rw [Nat.cast_pow]
        exact mul_le_mul_of_nonneg_left hcontain' (pow_nonneg hC0 _)
      _ = (sourceReversibleBranchCount n : ℝ) *
          ((sourceReversibleBranchCount n : ℝ) *
            (2 / (n : ℝ) ^ 3)) ^ (n - 1) := by
        have hpowC : (sourceReversibleBranchCount n : ℝ) ^ n =
            (sourceReversibleBranchCount n : ℝ) ^ (n - 1) *
              sourceReversibleBranchCount n := by
          calc
            (sourceReversibleBranchCount n : ℝ) ^ n =
                (sourceReversibleBranchCount n : ℝ) ^ ((n - 1) + 1) := by
              congr 1
              omega
            _ = (sourceReversibleBranchCount n : ℝ) ^ (n - 1) *
                sourceReversibleBranchCount n := pow_succ _ _
        rw [hpowC]
        rw [mul_pow]
        ring
      _ ≤ (72 * (n : ℝ) ^ 2) * (1 / 2 : ℝ) ^ (n - 1) := by
        exact mul_le_mul (sourceReversibleBranchCount_cast_le (by omega))
          (pow_le_pow_left₀ (mul_nonneg hC0 hq0)
            (sourceReversibleHalfContraction hn) (n - 1))
          (pow_nonneg (mul_nonneg hC0 hq0) _) (by positivity)
      _ = 144 * (n : ℝ) ^ 2 / (2 : ℝ) ^ n := by
        have hpowhalf : (1 / 2 : ℝ) ^ (n - 1) =
            2 / (2 : ℝ) ^ n := by
          conv_rhs => rw [show n = (n - 1) + 1 by omega, pow_succ]
          field_simp
          rw [← mul_pow]
          norm_num
        rw [hpowhalf]
        ring
  · exact div_nonneg (by positivity) (by positivity)

theorem sourceReversibleSurvivalBudget_tendsto_zero :
    Tendsto (fun n : Nat => 144 * (n : ℝ) ^ 2 / (2 : ℝ) ^ n)
      atTop (𝓝 0) := by
  have h := tendsto_pow_const_div_const_pow_of_one_lt 2
    (by norm_num : (1 : ℝ) < 2)
  simpa only [mul_zero, mul_div_assoc] using
    ((tendsto_const_nhds : Tendsto (fun _ : Nat => (144 : ℝ)) atTop (𝓝 144)).mul h)

theorem sourceLowDegreeReversibleSurvivalEnvelope_tendsto_zero
    (degree : Nat → Nat)
    (hdegree1 : ∀ᶠ n : Nat in atTop, 1 ≤ degree n)
    (hdegree : ∀ᶠ n : Nat in atTop,
      degree n ≤ sourceReactionCount n / n ^ 3) :
    Tendsto (fun n : Nat => gatewayReversibleSurvivalEnvelope
      (sourceReactionCount n) (degree n) n) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _ : Nat => (0 : ℝ)) atTop (𝓝 0))
    sourceReversibleSurvivalBudget_tendsto_zero
  · filter_upwards with n
    dsimp [gatewayReversibleSurvivalEnvelope]
    split_ifs
    · exact mul_nonneg (by positivity)
        (div_nonneg (by positivity) (by positivity))
    · exact le_rfl
  · filter_upwards [eventually_ge_atTop 288, hdegree1, hdegree] with n hn hd1 hd
    exact sourceLowDegreeReversibleSurvivalEnvelope_le_budget hn hd1 hd

end PowerLawSmallRAF
