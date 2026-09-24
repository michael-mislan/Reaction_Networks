import proofs.PowerLawSmallRAF.SourceTwoStratumRAFBound

namespace PowerLawSmallRAF

open RAF RAF.Polymer

/-- The size-`r` summand in the source two-stratum RAF bound, written with an
abstract one-reaction fibre-hit probability `p`. -/
noncomputable def sourceTwoStratumTerm (n r : Nat) (p : ℝ) : ℝ :=
  (sourceReversibleBranchCountAt n r ^ r : ℝ) *
    (((6 + 2 * r : Nat) : ℝ) * p +
      (((6 + 2 * r) ^ r : Nat) : ℝ) * p ^ 2)

/-- Endpoint envelope obtained by replacing every `r ≤ m` factor by its value
at `m` and paying for the `m` possible support sizes. -/
noncomputable def sourceTwoStratumEndpoint (n m : Nat) (p : ℝ) : ℝ :=
  (m : ℝ) * sourceTwoStratumTerm n m p

theorem sourceTwoStratumTerm_le_endpointTerm
    {n r m : Nat} {p : ℝ} (hp : 0 ≤ p) (hrm : r ≤ m) :
    sourceTwoStratumTerm n r p ≤ sourceTwoStratumTerm n m p := by
  let qr := 6 + 2 * r
  let qm := 6 + 2 * m
  let br := sourceReversibleBranchCountAt n r
  let bm := sourceReversibleBranchCountAt n m
  have hq : qr ≤ qm := by simp [qr, qm]; omega
  have hb : br ≤ bm := by
    dsimp [br, bm, sourceReversibleBranchCountAt]
    exact Nat.mul_le_mul hq (Nat.add_le_add_right hq n)
  have hbr : 0 < br := by
    dsimp [br, sourceReversibleBranchCountAt]
    positivity
  have hqr : 0 < qr := by simp [qr]
  have hbpow : br ^ r ≤ bm ^ m :=
    (Nat.pow_le_pow_right hbr hrm).trans (Nat.pow_le_pow_left hb m)
  have hqpow : qr ^ r ≤ qm ^ m :=
    (Nat.pow_le_pow_right hqr hrm).trans (Nat.pow_le_pow_left hq m)
  have hinside : (qr : ℝ) * p + (qr ^ r : Nat) * p ^ 2 ≤
      (qm : ℝ) * p + (qm ^ m : Nat) * p ^ 2 := by
    apply add_le_add
    · exact mul_le_mul_of_nonneg_right (by exact_mod_cast hq) hp
    · exact mul_le_mul_of_nonneg_right (by exact_mod_cast hqpow) (sq_nonneg p)
  have hinside0 : 0 ≤ (qr : ℝ) * p + (qr ^ r : Nat) * p ^ 2 :=
    add_nonneg (mul_nonneg (Nat.cast_nonneg _) hp)
      (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg p))
  dsimp [sourceTwoStratumTerm, br, bm, qr, qm] at hbpow hinside hinside0 ⊢
  exact mul_le_mul (by exact_mod_cast hbpow) hinside hinside0
    (by positivity)

theorem sourceTwoStratumSum_le_endpoint
    (n m : Nat) {p : ℝ} (hp : 0 ≤ p) :
    (∑ r ∈ Finset.Icc 1 m, sourceTwoStratumTerm n r p) ≤
      sourceTwoStratumEndpoint n m p := by
  have hterm : ∀ r ∈ Finset.Icc 1 m,
      sourceTwoStratumTerm n r p ≤ sourceTwoStratumTerm n m p := by
    intro r hr
    exact sourceTwoStratumTerm_le_endpointTerm hp (Finset.mem_Icc.mp hr).2
  have hsum := Finset.sum_le_card_nsmul
    (Finset.Icc 1 m) (sourceTwoStratumTerm n · p)
      (sourceTwoStratumTerm n m p) hterm
  simpa [sourceTwoStratumEndpoint, Nat.card_Icc, nsmul_eq_mul] using hsum

/-- The all-length source probability is controlled by one endpoint expression;
this is the finite entropy-coverage optimization used by the asymptotic step. -/
theorem sourceBoundedRevRAFProbability_le_two_stratum_endpoint
    {n m : Nat} (a : ℝ) (ha : 1 < a) (hn : 4 ≤ n) :
    sourceBoundedRevRAFProbability a n m ≤
      sourceTwoStratumEndpoint n m
        (powerLawMoleculeGatewayHit a (sourceReactionCount n) 1) := by
  let p := powerLawMoleculeGatewayHit a (sourceReactionCount n) 1
  let k : Fin n := ⟨1, by omega⟩
  let w : Word (k.val + 1) := ⟨0, by simp [k]⟩
  let s : Fin k.val := ⟨0, by simp [k]⟩
  let r0 : Reaction n := ⟨k, (w, s)⟩
  have hp : 0 ≤ p := (source_gatewayHit_nonneg_le_one a ha hn r0).1
  refine (sourceBoundedRevRAFProbability_le_two_stratum_sum a ha hn).trans ?_
  simpa only [sourceTwoStratumTerm, p] using
    sourceTwoStratumSum_le_endpoint n m hp

end PowerLawSmallRAF
