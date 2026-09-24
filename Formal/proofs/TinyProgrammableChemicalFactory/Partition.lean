import proofs.HeritableCompositions.BinomialLaw
import proofs.TinyProgrammableChemicalFactory.Source

namespace TinyProgrammableChemicalFactory
open HeritableCompositions

/-- ONE daughter draw determines both complementary resident counts. -/
noncomputable def jointPartition (n m : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (n+1), fairBinomialWeight n j *
    (if m≤j ∧ m≤n-j then 1 else 0)

theorem partition_is_binomial_expectation (n m : ℕ) :
    jointPartition n m = ∑ j ∈ Finset.range (n+1),
      (PMF.binomial (1/2) (by norm_num) n (Fin.ofNat (n+1) j)).toReal *
      (if m≤j ∧ m≤n-j then 1 else 0) := by
  unfold jointPartition
  apply Finset.sum_congr rfl
  intro j hj
  rw [fair_binomial_pmf_weight n j (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj)]

theorem complementary_restart (n j : ℕ) (hn : n≤80) (hj : j≤n)
    (ha : 8≤j) (hb : 8≤n-j) :
    restartX ![j,0,80-j,0,0,1,0] ∧
    restartX ![n-j,0,80-(n-j),0,0,1,0] := by
  simp [restartX, coreMass]
  omega

theorem impossible_below_two_minima (n m : ℕ) (h : n<2*m) :
    jointPartition n m=0 := by
  unfold jointPartition
  apply Finset.sum_eq_zero
  intro j hj
  have hjn : j≤n := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj
  have hnot : ¬(m≤j ∧ m≤n-j) := by omega
  simp [hnot]

end TinyProgrammableChemicalFactory
