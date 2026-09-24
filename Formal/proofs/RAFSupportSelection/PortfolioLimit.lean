import proofs.RAFSupportSelection.OneLayerSource

namespace RAFSupportSelection.OneLayer
open RAF RAF.Frankl RAFQueryCompilation
variable {P C J : Type*} [DecidableEq P] [DecidableEq C] [Fintype P] [Fintype C]
  [Fintype J]

def isolate (a : P) : Finset (P ⊕ C) :=
  Finset.univ.filter (fun r => (match r with
    | .inl b => decide (b ≠ a)
    | .inr _ => false) = true)

theorem isolate_cone (a : P) :
    selectedCone Finset.univ (parents (fun _ : C => a)) (isolate a) = isolate a := by
  rw [cone_eq_region]
  ext r
  cases r <;> simp [region, isolate]

theorem isolate_exact_loss (a : P) :
    Finset.univ \ evaluate (source (fun _ : C => Finset.univ))
      (fun x r => x ∈ (foodCats r : Finset (Molecule P C)))
      (Finset.univ \ isolate a) = isolate a := by
  let Q := source (fun _ : C => (Finset.univ : Finset P))
  let cats := fun x r => x ∈ (foodCats r : Finset (Molecule P C))
  have hw := source_certificate (fun _ : C => (Finset.univ : Finset P))
    (fun _ => a) (fun _ => Finset.mem_univ _)
  have hc := selectedCone_retained Finset.univ (parents (fun _ : C => a)) (isolate a)
  rw [isolate_cone a] at hc
  have hf := ranked_retained_fixed Q foodCats Finset.univ (Finset.univ \ isolate a)
    (parents (fun _ : C => a)) layerRank hw Finset.sdiff_subset hc
  have he : evaluate Q cats (Finset.univ \ isolate a) = Finset.univ \ isolate a :=
    Finset.Subset.antisymm (evaluate_subset Q cats _) (supported_subset_evaluate Q cats
      (Finset.Subset.refl _) (fixed_supported Q cats hf))
  change Finset.univ \ evaluate Q cats (Finset.univ \ isolate a) = isolate a
  rw [he]
  ext r
  simp

/-- Fixing just one consumer forces at least as many certificates as alternative
producers for zero excess on all deletion queries. Intersections do not evade this. -/
theorem small_portfolio_not_exact (choice : J → C → P)
    (hsize : Fintype.card J < Fintype.card P) (c : C) :
    ∃ a : P, Sum.inr c ∉ isolate a ∧
      ∀ j, Sum.inr c ∈ selectedCone Finset.univ (parents (choice j)) (isolate a) := by
  classical
  have missing : ∃ a : P, ∀ j, choice j c ≠ a := by
    by_contra hn
    push Not at hn
    have hs : Function.Surjective (fun j => choice j c) := hn
    have hh := Fintype.card_le_of_surjective _ hs
    omega
  obtain ⟨a, ha⟩ := missing
  refine ⟨a, by simp [isolate], ?_⟩
  intro j
  simp [cone_eq_region, region, isolate, ha j]

theorem arbitrary_portfolio_lower_bound
    (p : J → P ⊕ C → Finset (P ⊕ C)) (rank : J → P ⊕ C → ℕ)
    (hw : ∀ j, RankedSupport (source (fun _ : C => Finset.univ)) foodCats
      Finset.univ (p j) (rank j))
    (hsize : Fintype.card J < Fintype.card P) (c : C) :
    ∃ a : P,
      Sum.inr c ∉ (Finset.univ \ evaluate (source (fun _ : C => Finset.univ))
        (fun x r => x ∈ (foodCats r : Finset (Molecule P C))) (Finset.univ \ isolate a)) ∧
      ∀ j, Sum.inr c ∈ selectedCone Finset.univ (p j) (isolate a) := by
  classical
  have hn := fun j => normalize_source_certificate (fun _ : C => (Finset.univ : Finset P))
    (p j) (rank j) (hw j)
  choose choice ha hp using hn
  obtain ⟨a, hc, hall⟩ := small_portfolio_not_exact choice hsize c
  refine ⟨a, ?_, ?_⟩
  · simpa only [isolate_exact_loss] using hc
  · intro j
    exact selectedCone_mono_parents Finset.univ (isolate a) (parents (choice j)) (p j)
      (fun r _ => hp j r) (hall j)

end RAFSupportSelection.OneLayer
