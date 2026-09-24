import proofs.HeritableCompositions.BinomialLaw
import proofs.ProductiveChemicalHeredity.Source

namespace ProductiveChemicalHeredity

noncomputable def complementaryPayoff (n l u : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n+1), HeritableCompositions.fairBinomialWeight n i *
    (if l ≤ i ∧ i ≤ u ∧ l ≤ n-i ∧ n-i ≤ u then 1 else 0)

theorem complementary_binomial_law (n l u : ℕ) :
    complementaryPayoff n l u = ∑ i ∈ Finset.range (n+1),
      (PMF.binomial (1/2) (by norm_num) n (Fin.ofNat (n+1) i)).toReal *
      (if l ≤ i ∧ i ≤ u ∧ l ≤ n-i ∧ n-i ≤ u then 1 else 0) := by
  unfold complementaryPayoff
  apply Finset.sum_congr rfl
  intro i hi
  rw [HeritableCompositions.fair_binomial_pmf_weight n i
    (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hi)]

theorem actual_daughters (nx ny i j : ℕ)
    (hxi : 65 ≤ i ∧ i ≤ 195 ∧ 65 ≤ nx-i ∧ nx-i ≤ 195)
    (hyj : 8 ≤ j ∧ j ≤ 64 ∧ 8 ≤ ny-j ∧ ny-j ≤ 64) :
    corridor i j ∧ corridor (nx-i) (ny-j) := by
  unfold corridor
  omega

def fastTail (n k : ℕ) : ℕ :=
  ∑ i ∈ Finset.range k, n.descFactorial i / i.factorial

theorem fastTail_eq_binomial (n k : ℕ) :
    fastTail n k = ∑ i ∈ Finset.range k, n.choose i := by
  simp [fastTail,Nat.choose_eq_descFactorial_div_factorial]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
set_option exponentiation.threshold 1024 in
theorem endpoint_tail_certificate :
    100000 * (2 * (fastTail 186 65 * 2^130 + fastTail 316 121 +
      fastTail 38 8 * 2^278 + fastTail 94 30 * 2^222)) < 43 * 2^316 := by
  decide

end ProductiveChemicalHeredity
