import proofs.CompositionalMemory.ArbitraryParentPartition
import proofs.CompositionalMemory.LineageNecessity

namespace CompositionalMemory
open FiniteCopy HeritableCompositions Set

theorem word_birth_counts_iff_region {k : ℕ} (hk : 1 ≤ k) (N : ℕ) (hN : 1 ≤ N)
    (σ : Fin k → Bool) (n : Fin k → Counts) :
    n ∈ wordBirthCounts N (sourceWordCenter σ) σ ↔
      (n,k*N) ∈ wordBirthRegion N (sourceWordCenter σ) σ := by
  rw [mem_wordBirthCounts N hN _ (sourceWordCenter_upper σ) σ n]
  simp only [wordBirthRegion,Set.mem_setOf_eq,true_and,module_lattice_concentration hk N n]

theorem arbitrary_parent_immediate_failure {k : ℕ} (hk : 1 ≤ k) (N : ℕ) (hN : 1 ≤ N)
    (σ : Fin k → Bool) (n : Fin k → Counts) :
    1-(1-(1/2 : ℝ)^(280*N))^k ≤ ∑ d ∈ wordDraws n, wordDrawWeight n d*
      (if ¬((drawModule d,k*N) ∈ wordBirthRegion N (sourceWordCenter σ) σ ∧
        (wordSibling n d,k*N) ∈ wordBirthRegion N (sourceWordCenter σ) σ) then 1 else 0) := by
  classical
  simp only [← word_birth_counts_iff_region hk N hN σ]
  convert arbitrary_parent_closed_failure_bound N hN σ n using 1
  apply Finset.sum_congr rfl
  intro d _
  by_cases h : drawModule d ∈ wordBirthCounts N (sourceWordCenter σ) σ ∧
      wordSibling n d ∈ wordBirthCounts N (sourceWordCenter σ) σ
  all_goals simp [closedWordReturn,h]

/-- Literal fair allocation, accepting every closed-region pair including its
boundary. This law has no tube-exit or recovery censoring. -/
noncomputable def immediateWordPartitionLaw {k : ℕ} (N : ℕ) (σ : Fin k → Bool)
    (n : Fin k → Counts) : FiniteLaw (WordBirthOutcome N (sourceWordCenter σ) σ) := by
  classical
  exact (wordDaughterLaw n).bind (fun d =>
    if h : closedWordReturn N σ n d.val then
      FiniteLaw.pure (some (⟨drawModule d.val,h.1⟩,⟨wordSibling n d.val,h.2⟩))
    else FiniteLaw.pure none)

theorem immediate_partition_failure {k : ℕ} (N : ℕ) (hN : 1 ≤ N)
    (σ : Fin k → Bool) (n : Fin k → Counts) :
    1-necessitySurvival k N ≤ (immediateWordPartitionLaw N σ n).mass none := by
  classical
  have he : (immediateWordPartitionLaw N σ n).mass none =
      ∑ d ∈ wordDraws n, wordDrawWeight n d*(if ¬closedWordReturn N σ n d then 1 else 0) := by
    unfold immediateWordPartitionLaw FiniteLaw.bind
    change (∑ d : {d : WordDraw k // d ∈ wordDraws n}, wordDrawWeight n d.val*_) = _
    conv_rhs => rw [← Finset.sum_coe_sort]
    apply Finset.sum_congr rfl
    intro d _
    split_ifs with h <;> simp [FiniteLaw.pure,h]
  rw [he]
  exact arbitrary_parent_closed_failure_bound N hN σ n

theorem arbitrary_parent_law_failure {k : ℕ} {β : Type*} [Fintype β]
    (N : ℕ) (hN : 1 ≤ N) (σ : Fin k → Bool)
    (μ : FiniteLaw β) (counts : β → Fin k → Counts) :
    1-necessitySurvival k N ≤ (μ.bind (fun b => immediateWordPartitionLaw N σ (counts b))).mass none :=
  finite_bind_failure_lower _ _ _ (fun b => immediate_partition_failure N hN σ (counts b))

theorem immediate_lineage_upper {k : ℕ} {β : Type*} [Fintype β]
    (N : ℕ) (hN : 1 ≤ N) (σ : Fin k → Bool)
    (parents : WordBirthCount N (sourceWordCenter σ) σ → FiniteLaw β)
    (counts : β → Fin k → Counts) (G : ℕ) (n : WordBirthCount N (sourceWordCenter σ) σ) :
    wordLineageSuccess (fun x => (parents x).bind (fun b => immediateWordPartitionLaw N σ (counts b))) G n ≤
      (1-(1/2 : ℝ)^(280*N))^(k*G) := by
  have h := word_lineage_upper _ (necessitySurvival k N) (necessitySurvival_nonneg k N)
    (fun x => arbitrary_parent_law_failure N hN σ (parents x) counts) G n
  simpa only [necessitySurvival,← pow_mul] using h

end CompositionalMemory
