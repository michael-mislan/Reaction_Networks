import proofs.RAFQueryCompilation.RestrictionReuse

namespace RAFReactionCriticality.FunctionalSource
open RAF RAFQueryCompilation

variable {R : Type*} [DecidableEq R] [Fintype R]

/-- Food is `none`; reaction r produces its private molecule `some r`. -/
def source : CRS (Option R) R where
  inputs := fun _ => {none}
  outputs := fun r => {some r}
  food := {none}

def catalysts (parent : R → R) : Catalysis (Option R) R :=
  fun x r => x = some (parent r)

instance (parent : R → R) (x : Option R) (r : R) :
    Decidable (catalysts parent x r) := inferInstanceAs (Decidable (x = some (parent r)))

omit [Fintype R] in
theorem stage_product {S : Finset R} {r : R} (k : ℕ)
    (h : some r ∈ closureAt (source : CRS (Option R) R) S k) : r ∈ S := by
  induction k with
  | zero => simp [closureAt, source] at h
  | succ k ih =>
    simp only [closureAt, closureStep, Finset.mem_union, Finset.mem_biUnion] at h
    rcases h with h | ⟨t, ht, hx⟩
    · exact ih h
    · by_cases he : Enabled (source : CRS (Option R) R) (closureAt source S k) t
      · rw [if_pos he] at hx
        have : r = t := by simpa [source] using hx
        simpa [this] using ht
      · simp [he] at hx

omit [Fintype R] in
theorem product_stage_one {S : Finset R} {r : R} (h : r ∈ S) :
    some r ∈ closureAt (source : CRS (Option R) R) S 1 := by
  simp only [closureAt, closureStep, Finset.mem_union, Finset.mem_biUnion]
  exact Or.inr ⟨r, h, by simp [Enabled, source]⟩

omit [Fintype R] in
theorem raf_iff (parent : R → R) (S : Finset R) :
    IsRAF source (catalysts parent) S ↔
      S.Nonempty ∧ ∀ r ∈ S, parent r ∈ S := by
  constructor
  · rintro ⟨hne, _, hc⟩
    refine ⟨hne, ?_⟩
    intro r hr
    obtain ⟨x, k, hx, hcat⟩ := hc r hr
    change x = some (parent r) at hcat
    subst x
    exact stage_product k hx
  · rintro ⟨hne, hp⟩
    refine ⟨hne, ?_, ?_⟩
    · intro r _
      exact ⟨0, by simp [source, closureAt]⟩
    · intro r hr
      exact ⟨some (parent r), 1, product_stage_one (hp r hr), rfl⟩

/-- An orbit condition derived from the literal parent map, before querying maxRAF. -/
def Safe (parent : R → R) (A : Finset R) (r : R) : Prop :=
  ∀ k : ℕ, parent^[k] r ∈ A

theorem evaluate_iff_orbit (parent : R → R) (A : Finset R) (r : R) :
    r ∈ evaluate source (catalysts parent) A ↔ Safe parent A r := by
  classical
  rw [evaluate_mem_iff]
  constructor
  · rintro ⟨S, hs, hf, hr⟩ k
    have hp := (raf_iff parent S).mp hf |>.2
    apply hs
    induction k with
    | zero => exact hr
    | succ k ih => simpa only [Function.iterate_succ_apply'] using hp _ ih
  · intro h
    let S := Finset.univ.filter (Safe parent A)
    have hr : r ∈ S := by simp [S, h]
    refine ⟨S, ?_, (raf_iff parent S).mpr ⟨⟨r, hr⟩, ?_⟩, hr⟩
    · intro t ht
      have hh := (Finset.mem_filter.mp ht).2
      exact hh 0
    · intro t ht
      have hh := (Finset.mem_filter.mp ht).2
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, fun k => ?_⟩
      simpa only [Function.iterate_succ_apply] using hh (k+1)

theorem deletion_iff (parent : R → R) (K : Finset R) (r : R) :
    r ∉ evaluate source (catalysts parent) (Finset.univ \ K) ↔
      ∃ k : ℕ, parent^[k] r ∈ K := by
  classical
  simp only [evaluate_iff_orbit, Safe, Finset.mem_sdiff, Finset.mem_univ, true_and,
    not_forall, not_not]

end RAFReactionCriticality.FunctionalSource
