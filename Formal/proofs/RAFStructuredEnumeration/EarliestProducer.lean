import proofs.RAFStructuredEnumeration.SupplierParameter

namespace RAFStructuredEnumeration
open RAF RAF.Frankl RAFQueryCompilation
variable {M R : Type*} [DecidableEq M] [DecidableEq R] [LinearOrder M]
  [Fintype M] [Fintype R]

def resolvedCats (c : R → Option M) (r : R) : Finset M :=
  Finset.univ.filter (fun x => c r = some x)

omit [DecidableEq R] [LinearOrder M] [Fintype R] in
@[simp] theorem mem_resolvedCats (c : R → Option M) (r : R) (x : M) :
    x ∈ resolvedCats c r ↔ c r = some x := by simp [resolvedCats]

theorem preserving_resolution (Q : CRS M R) (cats : R → Finset M)
    (K S : Finset R) (hSK : S ⊆ K)
    (hK : ∀ r ∈ K, Supported Q (fun x r => x ∈ cats r) K r)
    (hS : IsRAF Q (fun x r => x ∈ cats r) S) :
    ∃ p c, (p,c) ∈ resolutions Q cats K ∧
      IsRAF (thin Q p) (fun x r => x ∈ resolvedCats c r) S := by
  classical
  choose fallback hf using producerOptions_nonempty Q K
  let p := earliestChoice Q S fallback
  have hp : ∀ x, p x ∈ producerOptions Q K x := earliestChoice_options Q K S hSK fallback hf
  have choice_exists (r : R) : ∃ z : Option M, z ∈ catalystOptions Q cats K r ∧
      (r ∈ S → ∃ x k, z = some x ∧ x ∈ closureAt Q S k) := by
    by_cases hr : r ∈ S
    · obtain ⟨x, k, hx, hg, _⟩ := catalystOption_available Q cats K S hSK hr
        ⟨hS.2.1 r hr, hS.2.2 r hr⟩
      exact ⟨some x, hx, fun _ => ⟨x,k,rfl,hg⟩⟩
    · obtain ⟨z, hz⟩ := catalystOptions_nonempty Q cats K hK r
      exact ⟨z, hz, fun h => False.elim (hr h)⟩
  choose c hc using choice_exists
  refine ⟨p, c, (mem_resolutions Q cats K p c).mpr ⟨hp, fun r => (hc r).1⟩,
    hS.1, ?_, ?_⟩
  · intro r hr
    obtain ⟨k, hk⟩ := hS.2.1 r hr
    refine ⟨k, ?_⟩
    change Q.inputs r ⊆ closureAt (thin Q (earliestChoice Q S fallback)) S k
    rw [earliestChoice_closure]
    exact hk
  · intro r hr
    obtain ⟨x, k, hx, hg⟩ := (hc r).2 hr
    refine ⟨x, k, ?_, (mem_resolvedCats c r x).mpr hx⟩
    change x ∈ closureAt (thin Q (earliestChoice Q S fallback)) S k
    rw [earliestChoice_closure]
    exact hg

theorem resolved_raf_sound (Q : CRS M R) (cats : R → Finset M) (K : Finset R)
    (p : M → Option R) (c : R → Option M) (hpc : (p,c) ∈ resolutions Q cats K)
    (S : Finset R) (hS : IsRAF (thin Q p) (fun x r => x ∈ resolvedCats c r) S) :
    IsRAF Q (fun x r => x ∈ cats r) S := by
  apply thin_raf_sound Q (fun x r => x ∈ cats r) (fun x r => x ∈ resolvedCats c r) p ?_ S hS
  intro x r hx
  have he := (mem_resolvedCats c r x).mp hx
  have hc := (mem_resolutions Q cats K p c).mp hpc |>.2 r
  rw [he] at hc
  exact catalystOption_sound Q cats K r x hc

end RAFStructuredEnumeration
