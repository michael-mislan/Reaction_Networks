import proofs.RAFSupportSelection.Aggregator
import proofs.RAFQueryCompilation.RankedWitness

namespace RAFSupportSelection.Aggregator
open RAF RAF.Frankl RAFQueryCompilation
variable {P C : Type*} [DecidableEq P] [DecidableEq C] [Fintype P] [Fintype C]

abbrev Molecule (P C : Type*) := Option (P ⊕ (C ⊕ Option C))

def source (allowed : C → Finset P) : CRS (Molecule P C) (Reaction P C) where
  food := {none}
  inputs r := match r with
    | none => Finset.univ.image (fun c => some (Sum.inr (Sum.inr (some c))))
    | some (.inl _) => {none}
    | some (.inr c) => {some (Sum.inr (Sum.inl c))}
  outputs r := match r with
    | none => {some (Sum.inr (Sum.inr none))}
    | some (.inl a) => {some (Sum.inl a)} ∪
        (Finset.univ.filter (fun c => a ∈ allowed c)).image
          (fun c => some (Sum.inr (Sum.inl c)))
    | some (.inr c) => {some (Sum.inr (Sum.inr (some c)))}

def cats (_ : Reaction P C) : Finset (Molecule P C) := {none}

def rank : Reaction P C → ℕ
  | none => 2
  | some (.inl _) => 0
  | some (.inr _) => 1

theorem source_certificate (allowed : C → Finset P) (choice : C → P)
    (hc : ∀ c, choice c ∈ allowed c) :
    RankedSupport (source allowed) cats Finset.univ (parents choice) rank := by
  constructor
  · intro r _ x hx
    cases r with
    | none =>
      obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hx
      right
      exact ⟨some (Sum.inr c), Finset.mem_univ _, by simp [parents],
        by simp [rank], by simp [source]⟩
    | some r =>
      cases r with
      | inl a => exact Or.inl hx
      | inr c =>
        have he : x = some (Sum.inr (Sum.inl c)) := by simpa [source] using hx
        subst x
        right
        exact ⟨some (Sum.inl (choice c)), Finset.mem_univ _, by simp [parents],
          by simp [rank], by simp [source, hc]⟩
  · intro r _
    exact ⟨none, by simp [cats], Or.inl (by simp [source])⟩

/-- On the standard coverable-universe inputs, the constructed baseline really is
the literal maximum RAF, not an unsupported ambient reaction set. -/
theorem source_baseline (allowed : C → Finset P) (hne : ∀ c, (allowed c).Nonempty) :
    evaluate (source allowed) (fun x r => x ∈ (cats r : Finset (Molecule P C)))
      Finset.univ = Finset.univ := by
  classical
  have hh : ∀ c, ∃ a, a ∈ allowed c := hne
  choose choice hc using hh
  have hw := source_certificate allowed choice hc
  have hf := ranked_retained_fixed (source allowed) cats Finset.univ Finset.univ
    (parents choice) rank hw (Finset.Subset.refl _)
    (fun _ _ => Finset.subset_univ _)
  exact Finset.Subset.antisymm (evaluate_subset _ _ _)
    (supported_subset_evaluate _ _ (Finset.Subset.refl _) (fixed_supported _ _ hf))

theorem normalize (allowed : C → Finset P)
    (p : Reaction P C → Finset (Reaction P C)) (ranks : Reaction P C → ℕ)
    (hw : RankedSupport (source allowed) cats Finset.univ p ranks) :
    ∃ choice : C → P, (∀ c, choice c ∈ allowed c) ∧ ∀ r, parents choice r ⊆ p r := by
  classical
  have ha : ∀ c, ∃ a, a ∈ allowed c ∧ some (Sum.inl a) ∈ p (some (Sum.inr c)) := by
    intro c
    rcases hw.1 (some (Sum.inr c)) (Finset.mem_univ _) (some (Sum.inr (Sum.inl c)))
      (by simp [source]) with hf | ⟨r, _, hp, _, hout⟩
    · simp [source] at hf
    · cases r with
      | none => simp [source] at hout
      | some r =>
        cases r with
        | inl a => exact ⟨a, by simpa [source] using hout, hp⟩
        | inr d => simp [source] at hout
  have hb : ∀ c, some (Sum.inr c) ∈ p none := by
    intro c
    rcases hw.1 none (Finset.mem_univ _) (some (Sum.inr (Sum.inr (some c))))
      (by simp [source]) with hf | ⟨r, _, hp, _, hout⟩
    · simp [source] at hf
    · cases r with
      | none => simp [source] at hout
      | some r =>
        cases r with
        | inl a => simp [source] at hout
        | inr d =>
          have he : c = d := by simpa [source] using hout
          simpa only [he] using hp
  choose choice hc hp using ha
  refine ⟨choice, hc, ?_⟩
  intro r
  cases r with
  | none =>
    intro t ht
    obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp ht
    exact hb c
  | some r =>
    cases r with
    | inl a => simp [parents]
    | inr c => simpa [parents] using hp c

/-- Exact source-faithful decision reduction for the primary uniform-singleton
mean objective (multiply the mean by the fixed reaction count). -/
theorem mean_selection_iff_set_cover (allowed : C → Finset P) (k : ℕ) :
    (∃ p : Reaction P C → Finset (Reaction P C), ∃ ranks : Reaction P C → ℕ,
      RankedSupport (source allowed) cats Finset.univ p ranks ∧
      weightedReach Finset.univ p (fun _ => 1) ≤
        Fintype.card P + 3 * Fintype.card C + 1 + k) ↔
    ∃ B : Finset P, B.card ≤ k ∧ ∀ c, (allowed c ∩ B).Nonempty := by
  classical
  constructor
  · rintro ⟨p, ranks, hw, hcost⟩
    obtain ⟨choice, hc, hp⟩ := normalize allowed p ranks hw
    have hmono := weightedReach_mono Finset.univ (parents choice) p (fun _ => 1) (fun r _ => hp r)
    rw [uniform_cost_formula] at hmono
    refine ⟨Finset.univ.image choice, by omega, ?_⟩
    intro c
    exact ⟨choice c, Finset.mem_inter.mpr ⟨hc c, Finset.mem_image.mpr ⟨c, Finset.mem_univ _, rfl⟩⟩⟩
  · rintro ⟨B, hB, hc⟩
    have hh : ∀ c, ∃ a, a ∈ allowed c ∧ a ∈ B := by
      intro c
      obtain ⟨a, ha⟩ := hc c
      exact ⟨a, Finset.mem_inter.mp ha⟩
    choose choice ha hb using hh
    refine ⟨parents choice, rank, source_certificate allowed choice ha, ?_⟩
    rw [uniform_cost_formula]
    have himage : Finset.univ.image choice ⊆ B := by
      intro a h
      obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp h
      exact hb c
    have hs := Finset.card_le_card himage
    omega

end RAFSupportSelection.Aggregator
