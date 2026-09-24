import proofs.RAFSupportSelection.SelectedCone

namespace RAFSupportSelection
open RAF RAFQueryCompilation
variable {M R : Type*} [DecidableEq M] [Fintype M] [DecidableEq R] [Fintype R]

/-- A local outgoing-edge check suffices to certify exact loss equal to the edits.
This enables a cheap portfolio query path without discovering every full cone. -/
theorem closed_seed_exact_loss (Q : CRS M R) (cats : R → Finset M) (S K : Finset R)
    (p : R → Finset R) (rank : R → ℕ) (hw : RankedSupport Q cats S p rank)
    (hK : K ⊆ S) (hc : ∀ r ∈ K, ∀ t ∈ S, r ∈ p t → t ∈ K) :
    S \ evaluate Q (fun x r => x ∈ cats r) (S \ K) = K := by
  have hcone : selectedCone S p K ⊆ K := by
    apply selectedCone_le S p K K Finset.inter_subset_left
    intro t ht hh
    obtain ⟨r, hr⟩ := hh
    obtain ⟨hrp, hrK⟩ := Finset.mem_inter.mp hr
    exact hc r hrK t ht hrp
  apply Finset.Subset.antisymm ((loss_subset_selectedCone Q cats S K p rank hw).trans hcone)
  intro r hr
  refine Finset.mem_sdiff.mpr ⟨hK hr, ?_⟩
  intro hs
  exact (Finset.mem_sdiff.mp (evaluate_subset Q _ (S \ K) hs)).2 hr

end RAFSupportSelection
