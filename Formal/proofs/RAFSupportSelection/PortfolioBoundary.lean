import proofs.RAFSupportSelection.SelectedCone

namespace RAFSupportSelection
open RAF RAF.Frankl RAFQueryCompilation

variable {M R I : Type*} [DecidableEq M] [Fintype M] [DecidableEq R] [Fintype R]

def retainedUnion (S K : Finset R) (H : Finset I) (p : I → R → Finset R) : Finset R :=
  H.biUnion (fun i => S \ selectedCone S (p i) K)

def portfolioQuery (Q : CRS M R) (cats : R → Finset M) (S K : Finset R)
    (H : Finset I) (p : I → R → Finset R) : Finset R :=
  let O := retainedUnion S K H p
  O ∪ evaluate (residualSource Q O) (fun x r => x ∈ cats r) ((S \ K) \ O)

/-- The union of certificate-retained sets is a sound residual boundary even when
its complement is not descendant-closed in any one certificate. -/
theorem portfolioQuery_correct (Q : CRS M R) (cats : R → Finset M) (S K : Finset R)
    (H : Finset I) (p : I → R → Finset R) (rank : I → R → ℕ)
    (hw : ∀ i ∈ H, RankedSupport Q cats S (p i) (rank i)) :
    portfolioQuery Q cats S K H p = evaluate Q (fun x r => x ∈ cats r) (S \ K) := by
  classical
  let O := retainedUnion S K H p
  have hpart (i : I) (hi : i ∈ H) : S \ selectedCone S (p i) K ⊆ O := by
    intro r hr
    exact Finset.mem_biUnion.mpr ⟨i, hi, hr⟩
  have hsupp : ∀ r ∈ O, Supported Q (fun x r => x ∈ cats r) O r := by
    intro r hr
    obtain ⟨i, hi, hr⟩ := Finset.mem_biUnion.mp hr
    have hf := ranked_retained_fixed Q cats S (S \ selectedCone S (p i) K)
      (p i) (rank i) (hw i hi) Finset.sdiff_subset (selectedCone_retained S (p i) K)
    exact supported_mono Q (fun x r => x ∈ cats r) (hpart i hi)
      (fixed_supported Q (fun x r => x ∈ cats r) hf r hr)
  have hfix : prune Q (fun x r => x ∈ cats r) O = O := by
    apply Finset.Subset.antisymm (prune_subset Q _ O)
    intro r hr
    exact (mem_prune Q _ O r).mpr ⟨hr, hsupp r hr⟩
  have hoa : O ⊆ S \ K := by
    intro r hr
    obtain ⟨i, _, hr⟩ := Finset.mem_biUnion.mp hr
    obtain ⟨hrS, hrD⟩ := Finset.mem_sdiff.mp hr
    refine Finset.mem_sdiff.mpr ⟨hrS, ?_⟩
    intro hrK
    exact hrD (selectedCone_seed S (p i) K (Finset.mem_inter.mpr ⟨hrK, hrS⟩))
  have he := evaluate_residual Q (fun x r => x ∈ cats r) (S \ K) O ((S \ K) \ O)
    hfix hoa Finset.sdiff_subset
    (by
      intro r hr
      by_cases ho : r ∈ O
      · exact Finset.mem_union_left _ ho
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr
          ⟨evaluate_subset Q _ (S \ K) hr, ho⟩))
  exact he.symm

end RAFSupportSelection
