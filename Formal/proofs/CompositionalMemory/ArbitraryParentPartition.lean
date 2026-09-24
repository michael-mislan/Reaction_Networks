import proofs.CompositionalMemory.DivisionNecessity

namespace CompositionalMemory
open FiniteCopy HeritableCompositions

noncomputable def closedWordReturn {k : ℕ} (N : ℕ) (σ : Fin k → Bool)
    (n : Fin k → Counts) (d : WordDraw k) : Prop :=
  drawModule d ∈ wordBirthCounts N (sourceWordCenter σ) σ ∧
    wordSibling n d ∈ wordBirthCounts N (sourceWordCenter σ) σ

noncomputable instance {k : ℕ} (N : ℕ) (σ : Fin k → Bool)
    (n : Fin k → Counts) (d : WordDraw k) : Decidable (closedWordReturn N σ n d) :=
  Classical.propDecidable _

theorem closed_return_parent_cap {k : ℕ} (N : ℕ) (σ : Fin k → Bool)
    (n : Fin k → Counts) (d : WordDraw k) (hd : d ∈ wordDraws n)
    (hreturn : closedWordReturn N σ n d) : ∀ i, ∑ a, n i a ≤ 280*N := by
  have hfirst := (mem_modularCountBox N (drawModule d)).mp (Finset.mem_filter.mp hreturn.1).1
  have hsecond := (mem_modularCountBox N (wordSibling n d)).mp (Finset.mem_filter.mp hreturn.2).1
  have hcoord (i a) : n i a ≤ 70*N := by
    have hle : d (i,a) ≤ n i a := Nat.le_of_lt_succ (Finset.mem_range.mp (Fintype.mem_piFinset.mp hd (i,a)))
    have h₀ := hfirst i a
    have h₁ := hsecond i a
    change d (i,a) ≤ 35*N at h₀
    change n i a-d (i,a) ≤ 35*N at h₁
    omega
  intro i
  calc
    _ ≤ ∑ _a : Fin 4, 70*N := Finset.sum_le_sum (fun a _ => hcoord i a)
    _ = _ := by simp; omega

theorem closed_return_nonempty {k : ℕ} (N : ℕ) (hN : 1 ≤ N) (σ : Fin k → Bool)
    (n : Fin k → Counts) (d : WordDraw k) (h : closedWordReturn N σ n d) :
    ∀ i, drawModule d i ≠ (fun _ => 0) :=
  source_birth_module_nonzero N hN σ ⟨drawModule d,h.1⟩

/-- No tube membership or parent-size hypothesis: conservation handles every
oversized parent, and literal independent allocations handle the remaining case. -/
theorem arbitrary_parent_closed_success_bound {k : ℕ} (N : ℕ) (hN : 1 ≤ N)
    (σ : Fin k → Bool) (n : Fin k → Counts) :
    (∑ d ∈ wordDraws n, wordDrawWeight n d*(if closedWordReturn N σ n d then 1 else 0)) ≤
      (1-(1/2 : ℝ)^(280*N))^k := by
  classical
  by_cases hcap : ∀ i, ∑ a, n i a ≤ 280*N
  · apply le_trans _ (word_nonempty_cap n (280*N) hcap)
    apply Finset.sum_le_sum
    intro d _
    apply mul_le_mul_of_nonneg_left _ (word_draw_weight_nonneg n d)
    by_cases h : closedWordReturn N σ n d
    · simp [h,closed_return_nonempty N hN σ n d h]
    · simp only [if_neg h]
      positivity
  · have hzero : (∑ d ∈ wordDraws n, wordDrawWeight n d*(if closedWordReturn N σ n d then 1 else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro d hd
      have hr : ¬ closedWordReturn N σ n d := fun h => hcap (closed_return_parent_cap N σ n d hd h)
      simp [hr]
    rw [hzero]
    apply pow_nonneg
    exact sub_nonneg.mpr (pow_le_one₀ (by norm_num) (by norm_num))

theorem arbitrary_parent_closed_failure_bound {k : ℕ} (N : ℕ) (hN : 1 ≤ N)
    (σ : Fin k → Bool) (n : Fin k → Counts) :
    1-(1-(1/2 : ℝ)^(280*N))^k ≤
      ∑ d ∈ wordDraws n, wordDrawWeight n d*(if ¬closedWordReturn N σ n d then 1 else 0) := by
  classical
  have hsuccess := arbitrary_parent_closed_success_bound N hN σ n
  have htotal :
      (∑ d ∈ wordDraws n, wordDrawWeight n d*(if closedWordReturn N σ n d then 1 else 0)) +
      (∑ d ∈ wordDraws n, wordDrawWeight n d*(if ¬closedWordReturn N σ n d then 1 else 0)) = 1 := by
    calc
      _ = ∑ d ∈ wordDraws n, wordDrawWeight n d := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro d _
        by_cases h : closedWordReturn N σ n d <;> simp [h]
      _ = 1 := word_draw_weight_sum n
  linarith only [hsuccess,htotal]

end CompositionalMemory
