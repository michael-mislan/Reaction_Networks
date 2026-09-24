import proofs.RAFStructuredEnumeration.SinkComponents
import proofs.RAFQueryCompilation.RankedExistence

namespace RAFStructuredEnumeration
open RAF RAF.Frankl RAFQueryCompilation
variable {M R : Type*} [DecidableEq M] [DecidableEq R]

def UniqueSuppliers (Q : CRS M R) (K : Finset R) : Prop :=
  ∀ x, x ∉ Q.food → ∀ p ∈ K, ∀ q ∈ K,
    x ∈ Q.outputs p → x ∈ Q.outputs q → p = q

def dependencies (Q : CRS M R) (cats : R → Finset M) (K : Finset R)
    (r : R) : Finset R := K.filter (fun p => ∃ x ∈ Q.outputs p,
      x ∉ Q.food ∧ (x ∈ Q.inputs r ∨ x ∈ cats r))

omit [DecidableEq R] in
theorem closure_producer (Q : CRS M R) (S : Finset R) (k : ℕ) :
    ∀ x ∈ closureAt Q S k, x ∈ Q.food ∨ ∃ p ∈ S, x ∈ Q.outputs p := by
  induction k with
  | zero => intro x hx; exact Or.inl hx
  | succ k ih =>
    intro x hx
    simp only [closureAt, closureStep, Finset.mem_union, Finset.mem_biUnion] at hx
    rcases hx with hx | ⟨p, hp, hout⟩
    · exact ih x hx
    · by_cases he : Enabled Q (closureAt Q S k) p
      · exact Or.inr ⟨p, hp, by simpa only [if_pos he] using hout⟩
      · simp only [if_neg he, Finset.notMem_empty] at hout

omit [DecidableEq R] in
theorem raf_dependency_closed (Q : CRS M R) (cats : R → Finset M)
    (K S : Finset R) (hSK : S ⊆ K) (hu : UniqueSuppliers Q K)
    (hc : ∀ r ∈ K, (↑(cats r) : Set M).Subsingleton)
    (hS : IsRAF Q (fun x r => x ∈ cats r) S) :
    DependencyClosed (dependencies Q cats K) S := by
  intro r hr p hp
  obtain ⟨hpK, x, hxp, hnf, hx⟩ := Finset.mem_filter.mp hp
  have generated : ∃ k, x ∈ closureAt Q S k := by
    rcases hx with hi | hcat
    · obtain ⟨k, hk⟩ := hS.2.1 r hr
      exact ⟨k, hk hi⟩
    · obtain ⟨y, k, hy, hcy⟩ := hS.2.2 r hr
      have heq : x = y := hc r (hSK hr) hcat hcy
      exact ⟨k, heq.symm ▸ hy⟩
  obtain ⟨k, hk⟩ := generated
  rcases closure_producer Q S k x hk with hf | ⟨q, hq, hxq⟩
  · exact False.elim (hnf hf)
  · have heq := hu x hnf p hpK q (hSK hq) hxp hxq
    exact heq.symm ▸ hq

variable [Fintype M]

theorem dependency_closed_raf (Q : CRS M R) (cats : R → Finset M)
    (K S : Finset R) (hSK : S ⊆ K)
    (hK : ∀ r ∈ K, Supported Q (fun x r => x ∈ cats r) K r)
    (hne : S.Nonempty) (hclosed : DependencyClosed (dependencies Q cats K) S) :
    IsRAF Q (fun x r => x ∈ cats r) S := by
  obtain ⟨rank, hw⟩ := supported_ranked_exists Q cats K hK
  have hw' : RankedSupport Q cats K (dependencies Q cats K) rank := by
    constructor
    · intro r hr x hx
      rcases hw.1 r hr x hx with hf | ⟨p, hp, _, hlt, hout⟩
      · exact Or.inl hf
      · by_cases hf : x ∈ Q.food
        · exact Or.inl hf
        · exact Or.inr ⟨p, hp, Finset.mem_filter.mpr
            ⟨hp, x, hout, hf, Or.inl hx⟩, hlt, hout⟩
    · intro r hr
      obtain ⟨x, hc, hx⟩ := hw.2 r hr
      refine ⟨x, hc, ?_⟩
      rcases hx with hf | ⟨p, hp, _, hout⟩
      · exact Or.inl hf
      · by_cases hf : x ∈ Q.food
        · exact Or.inl hf
        · exact Or.inr ⟨p, hp, Finset.mem_filter.mpr
            ⟨hp, x, hout, hf, Or.inr hc⟩, hout⟩
  apply (isRAF_iff_nonempty_prune_eq Q (fun x r => x ∈ cats r) S).mpr
  refine ⟨hne, ranked_retained_fixed Q cats K S (dependencies Q cats K) rank hw' hSK ?_⟩
  intro r hr p hp
  exact hclosed r hr (Finset.mem_inter.mp hp).1

theorem deterministic_raf_iff (Q : CRS M R) (cats : R → Finset M)
    (K S : Finset R) (hSK : S ⊆ K)
    (hK : ∀ r ∈ K, Supported Q (fun x r => x ∈ cats r) K r)
    (hu : UniqueSuppliers Q K) (hc : ∀ r ∈ K, (↑(cats r) : Set M).Subsingleton) :
    IsRAF Q (fun x r => x ∈ cats r) S ↔
      S.Nonempty ∧ DependencyClosed (dependencies Q cats K) S := by
  constructor
  · intro h
    exact ⟨h.1, raf_dependency_closed Q cats K S hSK hu hc h⟩
  · rintro ⟨hn, hcl⟩
    exact dependency_closed_raf Q cats K S hSK hK hn hcl

end RAFStructuredEnumeration
