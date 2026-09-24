import proofs.RAFSupportSelection.SurvivorExtension
import proofs.RAFSupportSelection.SelectedCone

namespace RAFSupportSelection
open RAF RAF.Frankl RAFQueryCompilation

variable {M R : Type*} [DecidableEq M] [Fintype M] [DecidableEq R] [Fintype R]

/-- Each query has a perfect certificate, with the certificate chosen after the query.
This is not the existence of one certificate perfect for every query. -/
theorem perfect_query_certificate (Q : CRS M R) (cats : R → Finset M)
    (S K : Finset R) (hS : prune Q (fun x r => x ∈ cats r) S = S) :
    ∃ p : R → Finset R, ∃ rank : R → ℕ,
      RankedSupport Q cats S p rank ∧
      selectedCone S p K = S \ evaluate Q (fun x r => x ∈ cats r) (S \ K) := by
  let T := evaluate Q (fun x r => x ∈ cats r) (S \ K)
  have hTS : T ⊆ S := (evaluate_subset Q (fun x r => x ∈ cats r) (S \ K)).trans Finset.sdiff_subset
  obtain ⟨rT, hwT⟩ := supported_ranked_exists Q cats T
    (fixed_supported Q (fun x r => x ∈ cats r) (evaluate_fixed Q _ (S \ K)))
  obtain ⟨p, rank, hw, _, hc⟩ := survivor_extension Q cats S T hTS (fun _ => T) rT hwT
    (fixed_supported Q (fun x r => x ∈ cats r) hS)
  refine ⟨p, rank, hw, Finset.Subset.antisymm ?_ (loss_subset_selectedCone Q cats S K p rank hw)⟩
  apply selectedCone_le S p K (S \ T)
  · intro r hr
    obtain ⟨hrK, hrS⟩ := Finset.mem_inter.mp hr
    refine Finset.mem_sdiff.mpr ⟨hrS, ?_⟩
    intro hrT
    exact (Finset.mem_sdiff.mp (evaluate_subset Q _ (S \ K) hrT)).2 hrK
  · intro r hrS hh
    refine Finset.mem_sdiff.mpr ⟨hrS, ?_⟩
    intro hrT
    obtain ⟨t, ht⟩ := hh
    obtain ⟨htp, htD⟩ := Finset.mem_inter.mp ht
    exact (Finset.mem_sdiff.mp htD).2 (hc r hrT htp)

/-- Membership in exact loss is equivalent to membership in every valid certificate cone. -/
theorem loss_iff_every_certificate (Q : CRS M R) (cats : R → Finset M)
    (S K : Finset R) (hS : prune Q (fun x r => x ∈ cats r) S = S) (r : R) :
    r ∈ S \ evaluate Q (fun x r => x ∈ cats r) (S \ K) ↔
      ∀ p rank, RankedSupport Q cats S p rank → r ∈ selectedCone S p K := by
  constructor
  · intro hr p rank hw
    exact loss_subset_selectedCone Q cats S K p rank hw hr
  · intro hh
    obtain ⟨p, rank, hw, he⟩ := perfect_query_certificate Q cats S K hS
    rw [← he]
    exact hh p rank hw

end RAFSupportSelection
