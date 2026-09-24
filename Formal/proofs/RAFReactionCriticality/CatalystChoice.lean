import proofs.RAFQueryCompilation.RestrictionReuse

namespace RAFReactionCriticality
open RAF RAFQueryCompilation

variable {M R : Type*} [DecidableEq M] [Fintype M] [DecidableEq R]

omit [Fintype M] in
/-- Resolving the only ambiguous catalytic site suffices for an entire RAF witness. -/
theorem raf_one_site_choice (Q : CRS M R) (C D : Catalysis M R) (v : R)
    (hagree : ∀ r, r ≠ v → ∀ x, C x r ↔ D x r) (S : Finset R) :
    IsRAF Q (fun x r => C x r ∨ D x r) S ↔ IsRAF Q C S ∨ IsRAF Q D S := by
  constructor
  · rintro ⟨hne, hfood, hcat⟩
    by_cases hv : v ∈ S
    · obtain ⟨x, k, hx, hc | hd⟩ := hcat v hv
      · left
        refine ⟨hne, hfood, ?_⟩
        intro r hr
        by_cases hrv : r = v
        · subst r
          exact ⟨x, k, hx, hc⟩
        · obtain ⟨y, j, hy, hyc | hyd⟩ := hcat r hr
          · exact ⟨y, j, hy, hyc⟩
          · exact ⟨y, j, hy, (hagree r hrv y).mpr hyd⟩
      · right
        refine ⟨hne, hfood, ?_⟩
        intro r hr
        by_cases hrv : r = v
        · subst r
          exact ⟨x, k, hx, hd⟩
        · obtain ⟨y, j, hy, hyc | hyd⟩ := hcat r hr
          · exact ⟨y, j, hy, (hagree r hrv y).mp hyc⟩
          · exact ⟨y, j, hy, hyd⟩
    · left
      refine ⟨hne, hfood, ?_⟩
      intro r hr
      have hrv : r ≠ v := fun h => hv (h ▸ hr)
      obtain ⟨y, j, hy, hyc | hyd⟩ := hcat r hr
      · exact ⟨y, j, hy, hyc⟩
      · exact ⟨y, j, hy, (hagree r hrv y).mpr hyd⟩
  · rintro (⟨hne, hfood, hcat⟩ | ⟨hne, hfood, hcat⟩)
    · refine ⟨hne, hfood, ?_⟩
      intro r hr
      obtain ⟨x, k, hx, hc⟩ := hcat r hr
      exact ⟨x, k, hx, Or.inl hc⟩
    · refine ⟨hne, hfood, ?_⟩
      intro r hr
      obtain ⟨x, k, hx, hc⟩ := hcat r hr
      exact ⟨x, k, hx, Or.inr hc⟩

/-- Exact redundant-catalyst decomposition, with arbitrary food dependencies. -/
theorem evaluate_one_site_choice (Q : CRS M R) (C D : Catalysis M R)
    [∀ x r, Decidable (C x r)] [∀ x r, Decidable (D x r)] (v : R)
    (hagree : ∀ r, r ≠ v → ∀ x, C x r ↔ D x r) (A : Finset R) :
    evaluate Q (fun x r => C x r ∨ D x r) A = evaluate Q C A ∪ evaluate Q D A := by
  ext r
  simp only [Finset.mem_union, evaluate_mem_iff]
  constructor
  · rintro ⟨S, hs, hf, hr⟩
    rcases (raf_one_site_choice Q C D v hagree S).mp hf with hc | hd
    · exact Or.inl ⟨S, hs, hc, hr⟩
    · exact Or.inr ⟨S, hs, hd, hr⟩
  · rintro (⟨S, hs, hc, hr⟩ | ⟨S, hs, hd, hr⟩)
    · exact ⟨S, hs, (raf_one_site_choice Q C D v hagree S).mpr (Or.inl hc), hr⟩
    · exact ⟨S, hs, (raf_one_site_choice Q C D v hagree S).mpr (Or.inr hd), hr⟩

end RAFReactionCriticality
