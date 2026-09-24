import proofs.CompositionalMemory.WordPartitionLaw
import proofs.CompositionalMemory.WordGeometry
import proofs.HeritableCompositions.PartitionFailure

namespace CompositionalMemory
open FiniteCopy CoreCouplingCAC HeritableCompositions Set

theorem word_energy_return {k : ℕ} (σ : Fin k → Bool) (i : Fin k) (y v : Point)
    (hy : wordEnergy σ i y ≤ 2*innerEnergy) (hv : ∀ a, |v a| ≤ 1/1000000) :
    wordEnergy σ i (fun a => y a+v a) < 4*innerEnergy := by
  cases h : σ i
  · simpa only [wordEnergy,h,Bool.false_eq_true,ite_false] using
      low_partition_return y v (by simpa only [wordEnergy,h,Bool.false_eq_true,ite_false] using hy) hv
  · simpa only [wordEnergy,h,ite_true] using
      high_partition_return y v (by simpa only [wordEnergy,h,ite_true] using hy) hv

def wordSibling {k : ℕ} (n : Fin k → Counts) (d : WordDraw k) (i : Fin k) : Counts :=
  fun a => n i a-d (i,a)

noncomputable def wordBothReturn {k : ℕ} (N : ℕ) (center : Fin k → Point)
    (σ : Fin k → Bool) (n : Fin k → Counts) (d : WordDraw k) : Prop :=
  ∀ i, wordEnergy σ i (fun a => concentration N (drawModule d i) a-center i a) < 4*innerEnergy ∧
    wordEnergy σ i (fun a => concentration N (wordSibling n d i) a-center i a) < 4*innerEnergy

noncomputable instance {k : ℕ} (N : ℕ) (center : Fin k → Point)
    (σ : Fin k → Bool) (n : Fin k → Counts) (d : WordDraw k) :
    Decidable (wordBothReturn N center σ n d) := Classical.propDecidable _

theorem word_both_return {k : ℕ} (N : ℕ) (hN : 0 < N) (center : Fin k → Point)
    (σ : Fin k → Bool) (n : Fin k → Counts) (d : WordDraw k) (hd : d ∈ wordDraws n)
    (hparent : ∀ i, wordEnergy σ i (fun a => concentration (2*N) (n i) a-center i a) ≤ 2*innerEnergy)
    (hgood : ∀ j : Fin k × Fin 4, |(d j : ℝ)-(n j.1 j.2 : ℝ)/2| < (N : ℝ)*(1/1000000)) :
    wordBothReturn N center σ n d := by
  intro i
  exact both_daughters_return (wordEnergy σ i) (word_energy_return σ i)
    (n i) (drawModule d i) (draw_module_valid n d hd i) N hN (center i) (hparent i)
    (fun a => hgood (i,a))

theorem word_partition_failure {k : ℕ} (N : ℕ) (hN : 0 < N)
    (center : Fin k → Point) (hc : ∀ i a, center i a ≤ 34)
    (σ : Fin k → Bool) (n : Fin k → Counts)
    (hparent : ∀ i, wordEnergy σ i (fun a => concentration (2*N) (n i) a-center i a) ≤ 2*innerEnergy) :
    (∑ d ∈ wordDraws n, wordDrawWeight n d*(if ¬ wordBothReturn N center σ n d then 1 else 0)) ≤
      8*(k : ℝ)*Real.exp (-(N : ℝ)*(1/1000000)^2/35) := by
  classical
  have hn (i a) : (n i a : ℝ) ≤ 70*(N : ℝ) :=
    parent_count_bound (wordEnergy σ i) (word_energy_lower σ i) (n i) N hN (center i) (hc i) (hparent i) a
  have hpoint (d : WordDraw k) (hd : d ∈ wordDraws n) :
      wordDrawWeight n d*(if ¬ wordBothReturn N center σ n d then 1 else 0) ≤
      wordDrawWeight n d*(if ∃ i : Fin k × Fin 4, (N : ℝ)*(1/1000000) ≤
        |(d i : ℝ)-(n i.1 i.2 : ℝ)/2| then 1 else 0) := by
    by_cases hbad : ∃ i : Fin k × Fin 4, (N : ℝ)*(1/1000000) ≤ |(d i : ℝ)-(n i.1 i.2 : ℝ)/2|
    · rw [if_pos hbad,mul_one]
      split_ifs
      · simpa only [mul_zero] using word_draw_weight_nonneg n d
      · simp
    · have hg (i : Fin k × Fin 4) : |(d i : ℝ)-(n i.1 i.2 : ℝ)/2| < (N : ℝ)*(1/1000000) :=
        lt_of_not_ge (fun hi => hbad ⟨i,hi⟩)
      have hr := word_both_return N hN center σ n d hd hparent hg
      rw [if_neg (not_not.mpr hr),mul_zero]
      exact mul_nonneg (word_draw_weight_nonneg n d) (by positivity)
  exact (Finset.sum_le_sum (fun d hd => hpoint d hd)).trans
    (word_draw_joint_tail n N hN hn (1/1000000) (by norm_num))

end CompositionalMemory
