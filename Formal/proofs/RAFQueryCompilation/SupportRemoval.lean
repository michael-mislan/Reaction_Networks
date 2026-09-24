import proofs.RAFQueryCompilation.ProducerCache

namespace RAFQueryCompilation
open RAF RAF.Frankl
variable {M R : Type*} [DecidableEq M] [DecidableEq R]

def supportPool (Q : CRS M R) (A : Finset R) : Finset M := Q.food ∪ A.biUnion Q.outputs

omit [DecidableEq R] in
theorem closureAt_subset_supportPool (Q : CRS M R) {S A : Finset R} (hsa : S ⊆ A)
    (k : ℕ) : closureAt Q S k ⊆ supportPool Q A := by
  induction k with
  | zero => exact Finset.subset_union_left
  | succ k ih =>
    intro x hx
    simp only [closureAt, closureStep, Finset.mem_union, Finset.mem_biUnion] at hx
    rcases hx with hx | ⟨r,hr,hx⟩
    · exact ih hx
    · apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      refine ⟨r,hsa hr,?_⟩
      split at hx
      · exact hx
      · simp at hx

omit [DecidableEq R] in
theorem supportPool_count (Q : CRS M R) (A : Finset R) (x : M) :
    x ∈ supportPool Q A ↔ x ∈ Q.food ∨ 0 < producerCount Q A x := by
  simp [supportPool,producerCount,Finset.card_pos,Finset.Nonempty]

def countSupported (Q : CRS M R) (cats : R → Finset M) (counts : M → ℕ) (r : R) : Bool :=
  decide ((∀ x ∈ Q.inputs r, x ∈ Q.food ∨ 0 < counts x) ∧
    ∃ x ∈ cats r, x ∈ Q.food ∨ 0 < counts x)

variable [Fintype M]

theorem evaluate_countSupported (Q : CRS M R) (cats : R → Finset M) (A : Finset R)
    (counts : M → ℕ) (hc : ∀ x, counts x = producerCount Q A x) {r : R}
    (hr : r ∈ evaluate Q (fun x r => x ∈ cats r) A) : countSupported Q cats counts r = true := by
  have hs := fixed_supported Q (fun x r => x ∈ cats r) (evaluate_fixed Q _ A) r hr
  rcases hs with ⟨⟨k,hi⟩,x,j,hx,hcat⟩
  simp only [countSupported, decide_eq_true_eq]
  constructor
  · intro y hy
    rw [hc y]
    exact (supportPool_count Q A y).mp
      (closureAt_subset_supportPool Q (evaluate_subset Q _ A) k (hi hy))
  · refine ⟨x,hcat,?_⟩
    rw [hc x]
    exact (supportPool_count Q A x).mp
      (closureAt_subset_supportPool Q (evaluate_subset Q _ A) j hx)

/-- Current candidate counts certify removal without computing food closure. -/
theorem evaluate_erase_unsupported (Q : CRS M R) (cats : R → Finset M) (A : Finset R)
    (counts : M → ℕ) (hc : ∀ x, counts x = producerCount Q A x) (r : R)
    (hu : countSupported Q cats counts r = false) :
    evaluate Q (fun x r => x ∈ cats r) (A.erase r) = evaluate Q (fun x r => x ∈ cats r) A := by
  have hn : r ∉ evaluate Q (fun x r => x ∈ cats r) A := by
    intro hr
    have ht := evaluate_countSupported Q cats A counts hc hr
    rw [hu] at ht
    contradiction
  apply Finset.Subset.antisymm (evaluate_mono Q _ (Finset.erase_subset r A))
  apply supported_subset_evaluate Q _
  · intro s hs
    exact Finset.mem_erase.mpr ⟨fun h => hn (h ▸ hs), evaluate_subset Q _ A hs⟩
  · exact fixed_supported Q _ (evaluate_fixed Q _ A)

end RAFQueryCompilation
