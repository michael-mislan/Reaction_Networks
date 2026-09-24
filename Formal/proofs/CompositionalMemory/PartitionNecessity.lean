import proofs.CompositionalMemory.EmptyProduct

namespace CompositionalMemory
open FiniteCopy HeritableCompositions

theorem source_return_nonempty {k : ℕ} (N : ℕ) (hN : 1 ≤ N) (σ : Fin k → Bool)
    (n : Fin k → Counts) (d : WordDraw k)
    (h : wordBothReturn N (sourceWordCenter σ) σ n d) :
    ∀ i, drawModule d i ≠ (fun _ => 0) := by
  let b : WordBirthCount N (sourceWordCenter σ) σ :=
    ⟨drawModule d,(mem_wordBirthCounts N hN _ (sourceWordCenter_upper σ) σ _).mpr
      (fun i => (h i).1.le)⟩
  exact source_birth_module_nonzero N hN σ b

theorem source_partition_necessary_event {k : ℕ} (N : ℕ) (hN : 1 ≤ N)
    (σ : Fin k → Bool) (n : Fin k → Counts) (M : ℕ) (hcap : ∀ i, ∑ a, n i a ≤ M) :
    (∑ d ∈ wordDraws n, wordDrawWeight n d*
      (if wordBothReturn N (sourceWordCenter σ) σ n d then 1 else 0)) ≤
        (1-(1/2 : ℝ)^M)^k := by
  classical
  apply le_trans _ (word_nonempty_cap n M hcap)
  apply Finset.sum_le_sum
  intro d _
  apply mul_le_mul_of_nonneg_left _ (word_draw_weight_nonneg n d)
  by_cases h : wordBothReturn N (sourceWordCenter σ) σ n d
  · simp [h,source_return_nonempty N hN σ n d h]
  · simp only [if_neg h]
    positivity

theorem source_partition_failure_lower {k : ℕ} (N : ℕ) (hN : 1 ≤ N)
    (σ : Fin k → Bool) (n : Fin k → Counts) (M : ℕ) (hcap : ∀ i, ∑ a, n i a ≤ M) :
    1-(1-(1/2 : ℝ)^M)^k ≤
      (wordPartitionLaw N hN (sourceWordCenter σ) (sourceWordCenter_upper σ) σ n).mass none := by
  classical
  have hsuccess := source_partition_necessary_event N hN σ n M hcap
  have heq : (wordPartitionLaw N hN (sourceWordCenter σ) (sourceWordCenter_upper σ) σ n).mass none =
      ∑ d ∈ wordDraws n, wordDrawWeight n d*(if wordBothReturn N (sourceWordCenter σ) σ n d then 0 else 1) := by
    unfold wordPartitionLaw FiniteLaw.bind
    change (∑ d : {d : WordDraw k // d ∈ wordDraws n}, wordDrawWeight n d.val*_) = _
    conv_rhs => rw [← Finset.sum_coe_sort]
    apply Finset.sum_congr rfl
    intro d _
    split_ifs with h <;> simp [FiniteLaw.pure,h]
  have htotal :
      (∑ d ∈ wordDraws n, wordDrawWeight n d*(if wordBothReturn N (sourceWordCenter σ) σ n d then 1 else 0)) +
      (∑ d ∈ wordDraws n, wordDrawWeight n d*(if wordBothReturn N (sourceWordCenter σ) σ n d then 0 else 1)) = 1 := by
    calc
      _ = ∑ d ∈ wordDraws n, wordDrawWeight n d := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro d _
        split_ifs <;> ring
      _ = 1 := word_draw_weight_sum n
  rw [heq]
  linarith only [hsuccess,htotal]

end CompositionalMemory
