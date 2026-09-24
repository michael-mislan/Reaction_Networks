import proofs.CompositionalMemory.WordPartition
import proofs.HeritableCompositions.FiniteLaw

namespace CompositionalMemory
open FiniteCopy HeritableCompositions

noncomputable def wordBirthCounts {k : ℕ} (N : ℕ) (center : Fin k → Point)
    (σ : Fin k → Bool) : Finset (Fin k → Counts) := by
  classical
  exact (modularCountBox k N).filter (fun n => ∀ i,
    wordEnergy σ i (fun a => concentration N (n i) a-center i a) ≤ 4*innerEnergy)

abbrev WordBirthCount {k : ℕ} (N : ℕ) (center : Fin k → Point) (σ : Fin k → Bool) :=
  {n : Fin k → Counts // n ∈ wordBirthCounts N center σ}

abbrev WordBirthOutcome {k : ℕ} (N : ℕ) (center : Fin k → Point) (σ : Fin k → Bool) :=
  Option (WordBirthCount N center σ × WordBirthCount N center σ)

theorem mem_wordBirthCounts {k : ℕ} (N : ℕ) (hN : 1 ≤ N)
    (center : Fin k → Point) (hc : ∀ i a, center i a ≤ 34) (σ : Fin k → Bool)
    (n : Fin k → Counts) :
    n ∈ wordBirthCounts N center σ ↔ ∀ i,
      wordEnergy σ i (fun a => concentration N (n i) a-center i a) ≤ 4*innerEnergy := by
  classical
  rw [wordBirthCounts,Finset.mem_filter]
  constructor
  · exact And.right
  · intro he
    refine ⟨(mem_modularCountBox N n).mpr ?_,he⟩
    intro i a
    have hb : wordEnergy σ i (fun j => concentration N (n i) j-center i j) < 1/32000000 := by
      have h := he i
      norm_num [innerEnergy,outerEnergy] at h ⊢
      linarith only [h]
    exact ((mem_countBox N (n i)).mp (small_energy_in_countBox N hN (n i) (center i) (hc i)
      (wordEnergy σ i) (word_energy_lower σ i) hb)) a

noncomputable def wordDaughterLaw {k : ℕ} (n : Fin k → Counts) :
    FiniteLaw {d : WordDraw k // d ∈ wordDraws n} := {
  mass := fun d => wordDrawWeight n d.val
  nonneg := fun d => word_draw_weight_nonneg n d.val
  total := by rw [Finset.sum_coe_sort]; exact word_draw_weight_sum n }

/-- Pushforward of literal fair partition, censoring draws outside the strict
certified return event. Accepted outputs are complementary closed-region newborns. -/
noncomputable def wordPartitionLaw {k : ℕ} (N : ℕ) (hN : 1 ≤ N)
    (center : Fin k → Point) (hc : ∀ i a, center i a ≤ 34) (σ : Fin k → Bool)
    (n : Fin k → Counts) : FiniteLaw (WordBirthOutcome N center σ) := by
  classical
  exact (wordDaughterLaw n).bind (fun d =>
    if h : wordBothReturn N center σ n d.val then
      FiniteLaw.pure (some
        (⟨drawModule d.val,(mem_wordBirthCounts N hN center hc σ _).mpr (fun i => (h i).1.le)⟩,
         ⟨wordSibling n d.val,(mem_wordBirthCounts N hN center hc σ _).mpr (fun i => (h i).2.le)⟩))
    else FiniteLaw.pure none)

theorem wordPartitionLaw_failure {k : ℕ} (N : ℕ) (hN : 1 ≤ N)
    (center : Fin k → Point) (hc : ∀ i a, center i a ≤ 34) (σ : Fin k → Bool)
    (n : Fin k → Counts)
    (hparent : ∀ i, wordEnergy σ i (fun a => concentration (2*N) (n i) a-center i a) ≤ 2*innerEnergy) :
    (wordPartitionLaw N hN center hc σ n).mass none ≤
      8*(k : ℝ)*Real.exp (-(N : ℝ)*(1/1000000)^2/35) := by
  classical
  have hraw := word_partition_failure N (by omega) center hc σ n hparent
  have heq : (wordPartitionLaw N hN center hc σ n).mass none =
      ∑ d ∈ wordDraws n, wordDrawWeight n d*(if ¬ wordBothReturn N center σ n d then 1 else 0) := by
    unfold wordPartitionLaw FiniteLaw.bind
    change (∑ d : {d : WordDraw k // d ∈ wordDraws n}, wordDrawWeight n d.val*_) = _
    conv_rhs => rw [← Finset.sum_coe_sort]
    apply Finset.sum_congr rfl
    intro d _
    split_ifs with h
    · simp [FiniteLaw.pure,h]
    · simp [FiniteLaw.pure,h]
  rw [heq]
  exact hraw

end CompositionalMemory
