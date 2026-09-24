import proofs.RAFQueryCompilation.ResidualClosure

namespace RAFQueryCompilation
open RAF RAF.Frankl
variable {M R : Type*} [DecidableEq M] [Fintype M] [DecidableEq R]

omit [Fintype M] [DecidableEq R] in
theorem fixed_supported (Q : CRS M R) (C : Catalysis M R) {S : Finset R}
    (hs : prune Q C S = S) : ∀ r ∈ S, Supported Q C S r := by
  intro r hr
  have hp : r ∈ prune Q C S := by rw [hs]; exact hr
  exact (mem_prune Q C S r).mp hp |>.2

theorem supported_subset_evaluate (Q : CRS M R) (C : Catalysis M R)
    [∀ x r, Decidable (C x r)] {S A : Finset R} (hsa : S ⊆ A)
    (hs : ∀ r ∈ S, Supported Q C S r) : S ⊆ evaluate Q C A := by
  by_cases hn : S.Nonempty
  · exact raf_subset_evaluate Q C hsa ⟨hn, fun r hr => (hs r hr).1,
      fun r hr => (hs r hr).2⟩
  · simp [Finset.not_nonempty_iff_eq_empty.mp hn]

theorem residual_supported (Q : CRS M R) (C : Catalysis M R)
    (O S : Finset R) (hO : FoodGenerated Q O) (r : R) :
    Supported (residualSource Q O) C S r ↔ Supported Q C (O ∪ S) r := by
  rw [supported_iff_finite, supported_iff_finite, residual_closure Q O S hO]
  rfl

/-- Exact residual evaluation for any already-stable outside part containing
all globally surviving reactions outside the chosen local availability. -/
theorem evaluate_residual (Q : CRS M R) (C : Catalysis M R)
    [∀ x r, Decidable (C x r)] (A O I : Finset R)
    (ho : prune Q C O = O) (hoa : O ⊆ A) (hia : I ⊆ A)
    (hcover : evaluate Q C A ⊆ O ∪ I) :
    evaluate Q C A = O ∪ evaluate (residualSource Q O) C I := by
  have hos := fixed_supported Q C ho
  have hfg : FoodGenerated Q O := fun r hr => (hos r hr).1
  have hom : O ⊆ evaluate Q C A := supported_subset_evaluate Q C hoa hos
  let L := evaluate (residualSource Q O) C I
  have hl : L ⊆ I := evaluate_subset (residualSource Q O) C I
  have hls : ∀ r ∈ L, Supported (residualSource Q O) C L r :=
    fixed_supported _ C (evaluate_fixed _ C I)
  have hback : O ∪ L ⊆ evaluate Q C A := by
    apply supported_subset_evaluate Q C (Finset.union_subset hoa (hl.trans hia))
    intro r hr
    rcases Finset.mem_union.mp hr with hr | hr
    · exact supported_mono Q C Finset.subset_union_left (hos r hr)
    · exact (residual_supported Q C O L hfg r).mp (hls r hr)
  have hdecomp : O ∪ (evaluate Q C A ∩ I) = evaluate Q C A := by
    apply Finset.Subset.antisymm
    · exact Finset.union_subset hom Finset.inter_subset_left
    · intro r hr
      rcases Finset.mem_union.mp (hcover hr) with ho | hi
      · exact Finset.mem_union_left _ ho
      · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hr, hi⟩)
  have hlocal : evaluate Q C A ∩ I ⊆ L := by
    apply supported_subset_evaluate _ C Finset.inter_subset_right
    intro r hr
    apply (residual_supported Q C O _ hfg r).mpr
    rw [hdecomp]
    exact fixed_supported Q C (evaluate_fixed Q C A) r (Finset.mem_inter.mp hr).1
  apply Finset.Subset.antisymm
  · rw [← hdecomp]
    exact Finset.union_subset_union (Finset.Subset.refl _) hlocal
  · exact hback

end RAFQueryCompilation
