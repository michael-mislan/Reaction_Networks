import proofs.RAFStructuredEnumeration.SupplierResolution
import proofs.RAFQueryCompilation.Pruning

namespace RAFStructuredEnumeration
open RAF RAF.Frankl RAFQueryCompilation
variable {M R : Type*} [DecidableEq M] [DecidableEq R]

def molecules (Q : CRS M R) (K : Finset R) : Finset M := Q.food ∪ K.biUnion Q.outputs

def producers (Q : CRS M R) (K : Finset R) (x : M) : Finset R :=
  K.filter (fun r => x ∈ Q.outputs r)

/-- Trivial coordinates have a singleton `none` choice and contribute zero excess. -/
def producerOptions (Q : CRS M R) (K : Finset R) (x : M) : Finset (Option R) :=
  if x ∈ Q.food ∨ producers Q K x = ∅ then {none}
  else (producers Q K x).image some

theorem producerOptions_nonempty (Q : CRS M R) (K : Finset R) (x : M) :
    (producerOptions Q K x).Nonempty := by
  unfold producerOptions
  split_ifs with h
  · exact Finset.singleton_nonempty _
  · exact (Finset.nonempty_iff_ne_empty.mpr (not_or.mp h).2).image _

theorem producerOption_of_mem (Q : CRS M R) (K : Finset R) (x : M)
    (hn : x ∉ Q.food) {r : R} (hr : r ∈ K) (hx : x ∈ Q.outputs r) :
    some r ∈ producerOptions Q K x := by
  have hp : r ∈ producers Q K x := Finset.mem_filter.mpr ⟨hr, hx⟩
  have he : producers Q K x ≠ ∅ := Finset.ne_empty_of_mem hp
  simp only [producerOptions, hn, he, or_self, ↓reduceIte]
  exact Finset.mem_image.mpr ⟨r, hp, rfl⟩

theorem earliestChoice_options (Q : CRS M R) (K S : Finset R) (hSK : S ⊆ K)
    (fallback : M → Option R) (hf : ∀ x, fallback x ∈ producerOptions Q K x) :
    ∀ x, earliestChoice Q S fallback x ∈ producerOptions Q K x := by
  classical
  intro x
  by_cases hg : x ∉ Q.food ∧ ∃ k, x ∈ closureAt Q S k
  · obtain ⟨r, hr, hp, hx, _⟩ := earliestChoice_spec Q S fallback x hg.1 hg.2
    rw [hp]
    exact producerOption_of_mem Q K x hg.1 (hSK hr) hx
  · simpa [earliestChoice, hg] using hf x

variable [LinearOrder M]

def catalystOptions (Q : CRS M R) (cats : R → Finset M) (K : Finset R)
    (r : R) : Finset (Option M) :=
  if r ∈ K then
    if h : (cats r ∩ Q.food).Nonempty then {some ((cats r ∩ Q.food).min' h)}
    else ((cats r) ∩ molecules Q K).image some
  else {none}

omit [DecidableEq R] [LinearOrder M] in
theorem closure_mem_molecules (Q : CRS M R) (K S : Finset R) (hSK : S ⊆ K)
    (k : ℕ) : closureAt Q S k ⊆ molecules Q K := by
  induction k with
  | zero => exact Finset.subset_union_left
  | succ k ih =>
    intro x hx
    simp only [closureAt, closureStep, Finset.mem_union, Finset.mem_biUnion] at hx
    rcases hx with hx | ⟨r, hr, hout⟩
    · exact ih hx
    · by_cases he : Enabled Q (closureAt Q S k) r
      · apply Finset.mem_union_right
        exact Finset.mem_biUnion.mpr ⟨r, hSK hr, by simpa only [if_pos he] using hout⟩
      · simp only [if_neg he, Finset.notMem_empty] at hout

/-- An effective catalyst can always be chosen inside the actual RAF closure.
The fixed food catalyst is used whenever present. -/
theorem catalystOption_available (Q : CRS M R) (cats : R → Finset M)
    (K S : Finset R) (hSK : S ⊆ K) {r : R} (hr : r ∈ S)
    (hs : Supported Q (fun x r => x ∈ cats r) S r) :
    ∃ x k, some x ∈ catalystOptions Q cats K r ∧
      x ∈ closureAt Q S k ∧ x ∈ cats r := by
  classical
  have hrK := hSK hr
  by_cases hf : (cats r ∩ Q.food).Nonempty
  · let x := (cats r ∩ Q.food).min' hf
    have hx : x ∈ cats r ∩ Q.food := Finset.min'_mem _ hf
    refine ⟨x, 0, ?_, (Finset.mem_inter.mp hx).2, (Finset.mem_inter.mp hx).1⟩
    simp [catalystOptions, hrK, hf, x]
  · obtain ⟨x, k, hx, hc⟩ := hs.2
    refine ⟨x, k, ?_, hx, hc⟩
    simp only [catalystOptions, hrK, ↓reduceIte, hf]
    exact Finset.mem_image.mpr ⟨x, Finset.mem_inter.mpr
      ⟨hc, closure_mem_molecules Q K S hSK k hx⟩, rfl⟩

theorem catalystOptions_nonempty (Q : CRS M R) (cats : R → Finset M) (K : Finset R)
    (hK : ∀ r ∈ K, Supported Q (fun x r => x ∈ cats r) K r) (r : R) :
    (catalystOptions Q cats K r).Nonempty := by
  by_cases hr : r ∈ K
  · obtain ⟨x, _, hx, _, _⟩ := catalystOption_available Q cats K K
      Finset.Subset.rfl hr (hK r hr)
    exact ⟨some x, hx⟩
  · simp [catalystOptions, hr]

theorem catalystOption_sound (Q : CRS M R) (cats : R → Finset M) (K : Finset R)
    (r : R) (x : M) (hx : some x ∈ catalystOptions Q cats K r) : x ∈ cats r := by
  unfold catalystOptions at hx
  split_ifs at hx with hr hf
  · have he : x = (cats r ∩ Q.food).min' hf :=
      Option.some.inj (Finset.mem_singleton.mp hx)
    rw [he]
    exact (Finset.mem_inter.mp (Finset.min'_mem _ hf)).1
  · obtain ⟨y, hy, he⟩ := Finset.mem_image.mp hx
    have heq := Option.some.inj he
    exact heq ▸ (Finset.mem_inter.mp hy).1
  · simp at hx

variable [Fintype M] [Fintype R]

noncomputable def resolutions (Q : CRS M R) (cats : R → Finset M) (K : Finset R) :
    Finset ((M → Option R) × (R → Option M)) := by
  classical
  exact (Fintype.piFinset (producerOptions Q K)).product
    (Fintype.piFinset (catalystOptions Q cats K))

@[simp] theorem mem_resolutions (Q : CRS M R) (cats : R → Finset M) (K : Finset R)
    (p : M → Option R) (c : R → Option M) :
    (p,c) ∈ resolutions Q cats K ↔
      (∀ x, p x ∈ producerOptions Q K x) ∧ (∀ r, c r ∈ catalystOptions Q cats K r) := by
  classical
  simp [resolutions, Fintype.mem_piFinset]

def supplierExcess (Q : CRS M R) (cats : R → Finset M) (K : Finset R) : ℕ :=
  (∑ x, ((producerOptions Q K x).card - 1)) +
    ∑ r, ((catalystOptions Q cats K r).card - 1)

theorem resolutions_card (Q : CRS M R) (cats : R → Finset M) (K : Finset R) :
    (resolutions Q cats K).card = (∏ x, (producerOptions Q K x).card) *
      ∏ r, (catalystOptions Q cats K r).card := by
  classical
  simp [resolutions]

end RAFStructuredEnumeration
