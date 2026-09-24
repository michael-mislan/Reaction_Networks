import proofs.PowerLawSmallRAF.ConditionalSubsetInclusion
import proofs.PowerLawSmallRAF.LigationGrammarCount

namespace PowerLawSmallRAF

/-- Union-bound envelope for a uniform marked target and a gateway-conditioned
fixed-degree fibre.  The `s`-instruction grammar contributes at most
`(F+s)^(2s)` codes and needs at least `s-1` non-gateway channels. -/
noncomputable def gatewayGrammarEnvelope
    (foodCount targetCount reactionCount degree instructionCap : Nat) : ℝ :=
  ∑ s ∈ Finset.Icc 1 instructionCap,
    (((foodCount + s) ^ (2 * s) : Nat) : ℝ) / targetCount *
      gatewayConditionedContain reactionCount (s - 1) degree

/-- Insert the exact without-replacement power bound term by term. -/
theorem gatewayGrammarEnvelope_le_powerSum
    (foodCount targetCount reactionCount degree instructionCap : Nat)
    (hdegree : 1 ≤ degree) (hdegreeR : degree ≤ reactionCount)
    (hcap : instructionCap ≤ degree) :
    gatewayGrammarEnvelope foodCount targetCount reactionCount degree instructionCap ≤
      ∑ s ∈ Finset.Icc 1 instructionCap,
        (((foodCount + s) ^ (2 * s) : Nat) : ℝ) / targetCount *
          ((((degree - 1 : Nat) : ℝ) /
            (reactionCount - (s - 1) : Nat)) ^ (s - 1)) := by
  dsimp [gatewayGrammarEnvelope]
  apply Finset.sum_le_sum
  intro s hs
  have hsCap : s ≤ instructionCap := (Finset.mem_Icc.mp hs).2
  have hq : s - 1 ≤ degree - 1 := by omega
  have hcontain := gatewayConditionedContain_le_power
    reactionCount (s - 1) degree hdegree hdegreeR hq
  apply mul_le_mul_of_nonneg_left hcontain
  exact div_nonneg (by positivity) (by positivity)

/-- The exact conditional terms in the envelope are nonnegative. -/
theorem gatewayGrammarEnvelope_nonneg
    (foodCount targetCount reactionCount degree instructionCap : Nat)
    (hdegree : 1 ≤ degree) (hdegreeR : degree ≤ reactionCount)
    (hcap : instructionCap ≤ degree) :
    0 ≤ gatewayGrammarEnvelope foodCount targetCount reactionCount degree instructionCap := by
  dsimp [gatewayGrammarEnvelope]
  apply Finset.sum_nonneg
  intro s hs
  have hsCap : s ≤ instructionCap := (Finset.mem_Icc.mp hs).2
  have hq : s - 1 ≤ degree - 1 := by omega
  rw [gatewayConditionedContain_eq_symmetricChoose
    reactionCount (s - 1) degree hdegree hdegreeR hq]
  exact mul_nonneg (div_nonneg (by positivity) (by positivity))
    (div_nonneg (by positivity) (by positivity))

theorem programCode_cast_le_cap
    (foodCount s instructionCap : Nat) (hs : s ≤ instructionCap) :
    (((foodCount + s) ^ (2 * s) : Nat) : ℝ) ≤
      (((foodCount + instructionCap : Nat) : ℝ) ^ 2) ^ s := by
  norm_cast
  rw [← pow_mul]
  exact Nat.pow_le_pow_left (Nat.add_le_add_left hs foodCount) (2 * s)

/-- Algebraic core of the low-degree envelope: if one instruction contributes
at most `A` codes and each additional instruction costs a factor `q`, then
`A*q ≤ 1` makes every length contribution at most `A`. -/
theorem geometric_code_term_le
    (A q : ℝ) (s : Nat) (hs : 1 ≤ s)
    (hA : 0 ≤ A) (hq : 0 ≤ q) (hAq : A * q ≤ 1) :
    A ^ s * q ^ (s - 1) ≤ A := by
  have hpow : (A * q) ^ (s - 1) ≤ 1 :=
    pow_le_one₀ (mul_nonneg hA hq) hAq
  have hidentity : A ^ s * q ^ (s - 1) =
      A * (A * q) ^ (s - 1) := by
    have hsEq : s = (s - 1) + 1 := by omega
    have hAs : A ^ s = A ^ (s - 1) * A := by
      calc
        A ^ s = A ^ ((s - 1) + 1) := congrArg (fun k : Nat => A ^ k) hsEq
        _ = A ^ (s - 1) * A := pow_succ A (s - 1)
    rw [hAs, mul_pow]
    ring
  rw [hidentity]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow hA

/-- Generic summation lemma behind the numerical PL43 envelope. -/
theorem gatewayGrammarEnvelope_le_uniformTerm
    (foodCount targetCount reactionCount degree instructionCap : Nat)
    (A q : ℝ) (hA : 0 ≤ A) (hq : 0 ≤ q) (hAq : A * q ≤ 1)
    (hcode : ∀ s ∈ Finset.Icc 1 instructionCap,
      (((foodCount + s) ^ (2 * s) : Nat) : ℝ) ≤ A ^ s)
    (hcontain : ∀ s ∈ Finset.Icc 1 instructionCap,
      gatewayConditionedContain reactionCount (s - 1) degree ≤ q ^ (s - 1))
    (hcontain0 : ∀ s ∈ Finset.Icc 1 instructionCap,
      0 ≤ gatewayConditionedContain reactionCount (s - 1) degree) :
    gatewayGrammarEnvelope foodCount targetCount reactionCount degree instructionCap ≤
      (instructionCap : ℝ) * (A / targetCount) := by
  dsimp [gatewayGrammarEnvelope]
  calc
    (∑ s ∈ Finset.Icc 1 instructionCap,
        (((foodCount + s) ^ (2 * s) : Nat) : ℝ) / targetCount *
          gatewayConditionedContain reactionCount (s - 1) degree) ≤
        ∑ _s ∈ Finset.Icc 1 instructionCap, A / targetCount := by
      apply Finset.sum_le_sum
      intro s hs
      have hs1 : 1 ≤ s := (Finset.mem_Icc.mp hs).1
      have htarget0 : (0 : ℝ) ≤ (targetCount : ℝ) := by positivity
      calc
        (((foodCount + s) ^ (2 * s) : Nat) : ℝ) / targetCount *
            gatewayConditionedContain reactionCount (s - 1) degree ≤
            (A ^ s / targetCount) *
              gatewayConditionedContain reactionCount (s - 1) degree := by
          apply mul_le_mul_of_nonneg_right
          · exact div_le_div_of_nonneg_right (hcode s hs) htarget0
          · exact hcontain0 s hs
        _ ≤ (A ^ s / targetCount) * q ^ (s - 1) := by
          apply mul_le_mul_of_nonneg_left (hcontain s hs)
          exact div_nonneg (pow_nonneg hA _) htarget0
        _ = (A ^ s * q ^ (s - 1)) / targetCount := by ring
        _ ≤ A / targetCount :=
          div_le_div_of_nonneg_right
            (geometric_code_term_le A q s hs1 hA hq hAq) htarget0
    _ = (instructionCap : ℝ) * (A / targetCount) := by simp

end PowerLawSmallRAF
