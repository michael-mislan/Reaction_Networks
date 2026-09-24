import proofs.RAFStructuredEnumeration.EarliestProducer
import proofs.RAFStructuredEnumeration.DeterministicSuppliers
import proofs.IrrRAFEnumeration.Irreducibility

namespace RAFStructuredEnumeration
open RAF RAF.Frankl RAFQueryCompilation MinRAFApprox.SetCoverSource
variable {M R : Type*} [DecidableEq M] [DecidableEq R] [LinearOrder M]
  [Fintype M] [Fintype R]

omit [LinearOrder M] [Fintype M] [Fintype R] in
theorem thin_unique (Q : CRS M R) (p : M → Option R) (K : Finset R) :
    UniqueSuppliers (thin Q p) K := by
  intro x hn r _ s _ hr hs
  have hrp : p x = some r := (Finset.mem_filter.mp hr).2.resolve_left hn
  have hsp : p x = some s := (Finset.mem_filter.mp hs).2.resolve_left hn
  exact Option.some.inj (hrp.symm.trans hsp)

omit [DecidableEq R] [LinearOrder M] [Fintype R] in
theorem resolvedCats_single (c : R → Option M) (r : R) :
    (↑(resolvedCats c r) : Set M).Subsingleton := by
  intro x hx y hy
  exact Option.some.inj (((mem_resolvedCats c r x).mp hx).symm.trans
    ((mem_resolvedCats c r y).mp hy))

omit [LinearOrder M] [Fintype R] in
theorem deterministic_irr_iff_sink (Q : CRS M R) (cats : R → Finset M)
    (K S : Finset R) (hSK : S ⊆ K)
    (hK : ∀ r ∈ K, Supported Q (fun x r => x ∈ cats r) K r)
    (hu : UniqueSuppliers Q K) (hc : ∀ r ∈ K, (↑(cats r) : Set M).Subsingleton) :
    IsIrreducibleRAF Q (fun x r => x ∈ cats r) S ↔
      S ∈ sinkCandidates K (dependencies Q cats K) := by
  have hdK : DependencyClosed (dependencies Q cats K) K := fun _ _ => Finset.filter_subset _ _
  rw [← minimal_closed_iff_sink K (dependencies Q cats K) hdK S hSK]
  constructor
  · intro h
    obtain ⟨hn, hcl⟩ := (deterministic_raf_iff Q cats K S hSK hK hu hc).mp h.1
    refine ⟨hn, hcl, ?_⟩
    intro T hT hcT hTS
    exact h.2 T (dependency_closed_raf Q cats K T (hTS.trans hSK) hK hT hcT) hTS
  · rintro ⟨hn, hcl, hm⟩
    refine ⟨dependency_closed_raf Q cats K S hSK hK hn hcl, ?_⟩
    intro T hT hTS
    exact hm T hT.1 (raf_dependency_closed Q cats K T (hTS.trans hSK) hu hc hT) hTS

def resolvedMax (Q : CRS M R) (K : Finset R) (p : M → Option R) (c : R → Option M) :
    Finset R := evaluate (thin Q p) (fun x r => x ∈ resolvedCats c r) K

noncomputable def resolutionCandidates (Q : CRS M R) (K : Finset R)
    (p : M → Option R) (c : R → Option M) : Finset (Finset R) :=
  sinkCandidates (resolvedMax Q K p c)
    (dependencies (thin Q p) (resolvedCats c) (resolvedMax Q K p c))

omit [LinearOrder M] [Fintype R] in
theorem resolutionCandidates_card (Q : CRS M R) (K : Finset R)
    (p : M → Option R) (c : R → Option M) :
    (resolutionCandidates Q K p c).card ≤ K.card := by
  exact (sinkCandidates_card _ _).trans (Finset.card_le_card (evaluate_subset _ _ _))

theorem original_irr_candidate (Q : CRS M R) (cats : R → Finset M)
    (K I : Finset R) (hIK : I ⊆ K)
    (hK : ∀ r ∈ K, Supported Q (fun x r => x ∈ cats r) K r)
    (hI : IsIrreducibleRAF Q (fun x r => x ∈ cats r) I) :
    ∃ p c, (p,c) ∈ resolutions Q cats K ∧ I ∈ resolutionCandidates Q K p c := by
  obtain ⟨p, c, hpc, hpres⟩ := preserving_resolution Q cats K I hIK hK hI.1
  have hirr : IsIrreducibleRAF (thin Q p) (fun x r => x ∈ resolvedCats c r) I := by
    refine ⟨hpres, ?_⟩
    intro T hT hTI
    exact hI.2 T (resolved_raf_sound Q cats K p c hpc T hT) hTI
  have hsub : I ⊆ resolvedMax Q K p c := raf_subset_evaluate _ _ hIK hpres
  refine ⟨p, c, hpc, ?_⟩
  exact (deterministic_irr_iff_sink (thin Q p) (resolvedCats c) (resolvedMax Q K p c)
    I hsub (fixed_supported _ _ (evaluate_fixed _ _ K))
    (thin_unique Q p _) (fun r _ => resolvedCats_single c r)).mp hirr

end RAFStructuredEnumeration
