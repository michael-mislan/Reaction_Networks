import proofs.HeritableCompositions.PartitionDaughters
import proofs.HeritableCompositions.PartitionTail
import proofs.FiniteCopy.WellDomains

namespace HeritableCompositions
open FiniteCopy

theorem partition_failure_bound (E : Point → ℝ)
    (hreturn : ∀ (y v : Point), E y ≤ 2*innerEnergy → (∀ i, |v i| ≤ 1/1000000) →
      E (fun i => y i+v i) < 4*innerEnergy)
    (n : Counts) (N : ℕ) (hN : 0 < N) (s : Point)
    (hn : ∀ i, (n i : ℝ) ≤ 70*(N : ℝ))
    (hparent : E (fun i => concentration (2*N) n i-s i) ≤ 2*innerEnergy) :
    (∑ d ∈ daughterDraws n, daughterWeight n d*
      (if ¬(E (fun i => concentration N d i-s i) < 4*innerEnergy ∧
        E (fun i => concentration N (fun j => n j-d j) i-s i) < 4*innerEnergy) then 1 else 0)) ≤
      8*Real.exp (-(N : ℝ)*(1/1000000)^2/35) := by
  classical
  have hpoint (d : Counts) (hd : d ∈ daughterDraws n) :
      daughterWeight n d*(if ¬(E (fun i => concentration N d i-s i) < 4*innerEnergy ∧
        E (fun i => concentration N (fun j => n j-d j) i-s i) < 4*innerEnergy) then 1 else 0) ≤
      daughterWeight n d*(if ∃ i, (N : ℝ)*(1/1000000) ≤ |(d i : ℝ)-(n i : ℝ)/2| then 1 else 0) := by
    by_cases hbad : ∃ i, (N : ℝ)*(1/1000000) ≤ |(d i : ℝ)-(n i : ℝ)/2|
    · rw [if_pos hbad,mul_one]
      split_ifs
      · simpa only [mul_zero] using daughterWeight_nonneg n d
      · simp
    · have hg (i) : |(d i : ℝ)-(n i : ℝ)/2| < (N : ℝ)*(1/1000000) :=
        lt_of_not_ge (fun hi => hbad ⟨i,hi⟩)
      have hr := both_daughters_return E hreturn n d hd N hN s hparent hg
      rw [if_neg (not_not.mpr hr),mul_zero]
      exact mul_nonneg (daughterWeight_nonneg n d) (by positivity)
  exact (Finset.sum_le_sum (fun d hd => hpoint d hd)).trans
    (daughter_joint_tail n N hN hn (1/1000000) (by norm_num))

theorem parent_count_bound (E : Point → ℝ) (hE : ∀ y, (1/200)*normSq y ≤ E y)
    (n : Counts) (N : ℕ) (hN : 0 < N) (s : Point) (hs : ∀ i, s i ≤ 34)
    (hparent : E (fun i => concentration (2*N) n i-s i) ≤ 2*innerEnergy) :
    ∀ i, (n i : ℝ) ≤ 70*(N : ℝ) := by
  have he : E (fun i => concentration (2*N) n i-s i) < 1/32000000 := by
    norm_num [innerEnergy,outerEnergy] at hparent ⊢
    linarith only [hparent]
  have hbox := (mem_countBox (2*N) n).mp (small_energy_in_countBox (2*N) (by omega) n s hs E hE he)
  intro i
  have h := hbox i
  have hn : n i ≤ 70*N := by omega
  exact_mod_cast hn

theorem low_partition_failure (n : Counts) (N : ℕ) (hN : 0 < N) (s : Point)
    (hs : ∀ i, s i ≤ 34)
    (hparent : lowEnergy (fun i => concentration (2*N) n i-s i) ≤ 2*innerEnergy) :
    (∑ d ∈ daughterDraws n, daughterWeight n d*
      (if ¬(lowEnergy (fun i => concentration N d i-s i) < 4*innerEnergy ∧
        lowEnergy (fun i => concentration N (fun j => n j-d j) i-s i) < 4*innerEnergy) then 1 else 0)) ≤
      8*Real.exp (-(N : ℝ)*(1/1000000)^2/35) :=
  partition_failure_bound lowEnergy low_partition_return n N hN s
    (parent_count_bound lowEnergy lowEnergy_lower n N hN s hs hparent) hparent

theorem high_partition_failure (n : Counts) (N : ℕ) (hN : 0 < N) (s : Point)
    (hs : ∀ i, s i ≤ 34)
    (hparent : highEnergy (fun i => concentration (2*N) n i-s i) ≤ 2*innerEnergy) :
    (∑ d ∈ daughterDraws n, daughterWeight n d*
      (if ¬(highEnergy (fun i => concentration N d i-s i) < 4*innerEnergy ∧
        highEnergy (fun i => concentration N (fun j => n j-d j) i-s i) < 4*innerEnergy) then 1 else 0)) ≤
      8*Real.exp (-(N : ℝ)*(1/1000000)^2/35) :=
  partition_failure_bound highEnergy high_partition_return n N hN s
    (parent_count_bound highEnergy highEnergy_lower n N hN s hs hparent) hparent

end HeritableCompositions
