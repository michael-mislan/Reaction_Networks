import proofs.RAFQueryCompilation.Pruning

namespace RAFQueryCompilation
open RAF

variable {M R : Type*} [DecidableEq M] [Fintype M] [DecidableEq R]

theorem evaluate_mono (Q : CRS M R) (C : Catalysis M R)
    [∀ x r, Decidable (C x r)] {A B : Finset R} (h : A ⊆ B) :
    evaluate Q C A ⊆ evaluate Q C B := by
  intro r hr
  obtain ⟨S, hs, hf, hr⟩ := (evaluate_mem_iff Q C A r).mp hr
  exact (evaluate_mem_iff Q C B r).mpr ⟨S, hs.trans h, hf, hr⟩

/-- Deletion reuse is exact for every finite ordinary RAF source. -/
theorem evaluate_restriction_reuse (Q : CRS M R) (C : Catalysis M R)
    [∀ x r, Decidable (C x r)] (A B : Finset R) :
    evaluate Q C (evaluate Q C A ∩ B) = evaluate Q C (A ∩ B) := by
  apply Finset.Subset.antisymm
  · apply evaluate_mono
    intro r hr
    exact Finset.mem_inter.mpr
      ⟨evaluate_subset Q C A (Finset.mem_inter.mp hr).1, (Finset.mem_inter.mp hr).2⟩
  · intro r hr
    obtain ⟨S, hs, hf, hr⟩ := (evaluate_mem_iff Q C (A ∩ B) r).mp hr
    have ha : S ⊆ A := hs.trans Finset.inter_subset_left
    have hb : S ⊆ B := hs.trans Finset.inter_subset_right
    have he := raf_subset_evaluate Q C ha hf
    exact (evaluate_mem_iff Q C (evaluate Q C A ∩ B) r).mpr
      ⟨S, fun x hx => Finset.mem_inter.mpr ⟨he hx, hb hx⟩, hf, hr⟩

theorem evaluate_nonempty_iff (Q : CRS M R) (C : Catalysis M R)
    [∀ x r, Decidable (C x r)] (A : Finset R) :
    (evaluate Q C A).Nonempty ↔ ∃ S ⊆ A, IsRAF Q C S := by
  constructor
  · rintro ⟨r, hr⟩
    obtain ⟨S, hs, hf, _⟩ := (evaluate_mem_iff Q C A r).mp hr
    exact ⟨S, hs, hf⟩
  · rintro ⟨S, hs, hf⟩
    obtain ⟨r, hr⟩ := hf.1
    exact ⟨r, raf_subset_evaluate Q C hs hf hr⟩

end RAFQueryCompilation
