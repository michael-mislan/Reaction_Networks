import proofs.RAFQueryCompilation.RestrictionReuse

namespace RAFReactionCriticality
open RAF RAFQueryCompilation

variable {M R : Type*} [DecidableEq M] [Fintype M] [DecidableEq R]
variable (Q : CRS M R) (C : Catalysis M R) [∀ x r, Decidable (C x r)]

def loss (S K : Finset R) : Finset R := S \ evaluate Q C (S \ K)

theorem evaluate_idempotent (A : Finset R) :
    evaluate Q C (evaluate Q C A) = evaluate Q C A := by
  apply Finset.Subset.antisymm (evaluate_subset Q C _)
  intro r hr
  obtain ⟨T, ht, hf, hrt⟩ := (evaluate_mem_iff Q C A r).mp hr
  exact raf_subset_evaluate Q C (raf_subset_evaluate Q C ht hf) hf hrt

theorem loss_extensive {S K : Finset R} (h : K ⊆ S) : K ⊆ loss Q C S K := by
  intro r hr
  refine Finset.mem_sdiff.mpr ⟨h hr, ?_⟩
  intro he
  exact (Finset.mem_sdiff.mp (evaluate_subset Q C _ he)).2 hr

theorem loss_mono (S : Finset R) {K H : Finset R} (h : K ⊆ H) :
    loss Q C S K ⊆ loss Q C S H := by
  intro r hr
  obtain ⟨hs, hn⟩ := Finset.mem_sdiff.mp hr
  refine Finset.mem_sdiff.mpr ⟨hs, fun he => hn (evaluate_mono Q C ?_ he)⟩
  intro t ht
  obtain ⟨hts, hth⟩ := Finset.mem_sdiff.mp ht
  exact Finset.mem_sdiff.mpr ⟨hts, fun hk => hth (h hk)⟩

theorem complement_loss (S K : Finset R) :
    S \ loss Q C S K = evaluate Q C (S \ K) := by
  have h : evaluate Q C (S \ K) ⊆ S :=
    (evaluate_subset Q C _).trans Finset.sdiff_subset
  ext r
  simp only [loss, Finset.mem_sdiff]
  constructor
  · tauto
  · intro hr
    exact ⟨h hr, fun hh => hh.2 hr⟩

theorem loss_idempotent (S K : Finset R) :
    loss Q C S (loss Q C S K) = loss Q C S K := by
  change S \ evaluate Q C (S \ loss Q C S K) = loss Q C S K
  rw [complement_loss, evaluate_idempotent]
  rfl

theorem loss_empty {S : Finset R} (hs : evaluate Q C S = S) :
    loss Q C S ∅ = ∅ := by simp [loss, hs]

theorem singleton_loss_nested {S : Finset R} {r t : R}
    (ht : t ∈ loss Q C S {r}) : loss Q C S {t} ⊆ loss Q C S {r} := by
  have h : ({t} : Finset R) ⊆ loss Q C S {r} := Finset.singleton_subset_iff.mpr ht
  simpa only [loss_idempotent] using loss_mono Q C S h

theorem mutual_loss_eq {S : Finset R} {r t : R}
    (ht : t ∈ loss Q C S {r}) (hr : r ∈ loss Q C S {t}) :
    loss Q C S {r} = loss Q C S {t} :=
  Finset.Subset.antisymm (singleton_loss_nested Q C hr) (singleton_loss_nested Q C ht)

theorem loss_union_contains (S K H : Finset R) :
    loss Q C S K ∪ loss Q C S H ⊆ loss Q C S (K ∪ H) :=
  Finset.union_subset (loss_mono Q C S Finset.subset_union_left)
    (loss_mono Q C S Finset.subset_union_right)

end RAFReactionCriticality
