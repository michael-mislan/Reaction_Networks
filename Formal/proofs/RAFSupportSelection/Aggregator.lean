import proofs.RAFSupportSelection.Objective

namespace RAFSupportSelection.Aggregator
open RAFQueryCompilation
variable {P C : Type*} [DecidableEq P] [DecidableEq C] [Fintype P] [Fintype C]

abbrev Reaction (P C : Type*) := Option (P ⊕ C)

def parents (choice : C → P) : Reaction P C → Finset (Reaction P C)
  | none => Finset.univ.image (fun c => some (Sum.inr c))
  | some (.inl _) => ∅
  | some (.inr c) => {some (Sum.inl (choice c))}

def region (choice : C → P) (K : Finset (Reaction P C)) : Finset (Reaction P C) :=
  K ∪ Finset.univ.filter (fun r => (match r with
    | none => decide (∃ c : C, some (Sum.inr c) ∈ K ∨ some (Sum.inl (choice c)) ∈ K)
    | some (.inl _) => false
    | some (.inr c) => decide (some (Sum.inl (choice c)) ∈ K)) = true)

private theorem edge (choice : C → P) (K : Finset (Reaction P C)) (t r : Reaction P C)
    (ht : t ∈ selectedCone Finset.univ (parents choice) K) (hp : t ∈ parents choice r) :
    r ∈ selectedCone Finset.univ (parents choice) K := by
  rw [← selectedCone_fixed Finset.univ (parents choice) K]
  exact Finset.mem_union_right _ (Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, t, Finset.mem_inter.mpr ⟨hp, ht⟩⟩)

theorem cone_eq_region (choice : C → P) (K : Finset (Reaction P C)) :
    selectedCone Finset.univ (parents choice) K = region choice K := by
  apply Finset.Subset.antisymm
  · apply selectedCone_le
    · intro r hr
      exact Finset.mem_union_left _ (Finset.mem_inter.mp hr).1
    · intro r _ hh
      obtain ⟨t, ht⟩ := hh
      obtain ⟨htp, htB⟩ := Finset.mem_inter.mp ht
      cases r with
      | none =>
        obtain ⟨c, _, he⟩ := Finset.mem_image.mp htp
        subst t
        have hc : some (Sum.inr c) ∈ K ∨ some (Sum.inl (choice c)) ∈ K := by
          simpa [region] using htB
        exact Finset.mem_union_right _ (by simp; exact ⟨c, hc⟩)
      | some r =>
        cases r with
        | inl a => simp [parents] at htp
        | inr c =>
          have he : t = some (Sum.inl (choice c)) := by simpa [parents] using htp
          subst t
          have hk : some (Sum.inl (choice c)) ∈ K := by simpa [region] using htB
          exact Finset.mem_union_right _ (by simp [hk])
  · have seed {r : Reaction P C} (hr : r ∈ K) :
        r ∈ selectedCone Finset.univ (parents choice) K :=
      selectedCone_seed _ _ _ (Finset.mem_inter.mpr ⟨hr, Finset.mem_univ _⟩)
    intro r hr
    rcases Finset.mem_union.mp hr with hk | hr
    · exact seed hk
    · cases r with
      | none =>
        have hh : ∃ c : C, some (Sum.inr c) ∈ K ∨ some (Sum.inl (choice c)) ∈ K := by
          simpa using hr
        obtain ⟨c, hc | hc⟩ := hh
        · exact edge choice K _ _ (seed hc) (by simp [parents])
        · have hcons := edge choice K _ (some (Sum.inr c)) (seed hc) (by simp [parents])
          exact edge choice K _ _ hcons (by simp [parents])
      | some r =>
        cases r with
        | inl a => simp at hr
        | inr c =>
          have hk : some (Sum.inl (choice c)) ∈ K := by simpa using hr
          exact edge choice K _ _ (seed hk) (by simp [parents])

def ancestors (choice : C → P) (r : Reaction P C) : Finset (Reaction P C) :=
  Finset.univ.filter (fun k => r ∈ selectedCone Finset.univ (parents choice) {k})

theorem ancestors_producer (choice : C → P) (a : P) :
    ancestors choice (some (Sum.inl a)) = {some (Sum.inl a)} := by
  ext k
  cases k with
  | none => simp [ancestors, cone_eq_region, region]
  | some k =>
    cases k <;> simp [ancestors, cone_eq_region, region]
    exact eq_comm

theorem ancestors_consumer (choice : C → P) (c : C) :
    ancestors choice (some (Sum.inr c)) = {some (Sum.inr c), some (Sum.inl (choice c))} := by
  ext k
  cases k with
  | none => simp [ancestors, cone_eq_region, region]
  | some k => cases k <;> simp [ancestors, cone_eq_region, region] <;> exact eq_comm

theorem ancestors_aggregator (choice : C → P) :
    ancestors choice none = insert none
      ((Finset.univ.image (fun c : C => some (Sum.inr c))) ∪
       ((Finset.univ.image choice).image (fun a => some (Sum.inl a)))) := by
  ext k
  cases k with
  | none => simp [ancestors, cone_eq_region, region]
  | some k =>
    cases k with
    | inl a =>
      simp [ancestors, cone_eq_region, region]
    | inr c => simp [ancestors, cone_eq_region, region]

theorem aggregator_ancestor_card (choice : C → P) :
    (ancestors choice none).card = 1 + Fintype.card C + (Finset.univ.image choice).card := by
  rw [ancestors_aggregator, Finset.card_insert_of_notMem (by simp)]
  have hd : Disjoint (Finset.univ.image (fun c : C => (some (Sum.inr c) : Reaction P C)))
      ((Finset.univ.image choice).image (fun a => some (Sum.inl a))) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hx
    simp at hy
  rw [Finset.card_union_of_disjoint hd]
  rw [Finset.card_image_of_injective _ (by intro a b h; simpa using h),
      Finset.card_image_of_injective _ (by intro a b h; simpa using h)]
  simp only [Finset.card_univ]
  omega

/-- A single forced aggregator turns assignment cost into distinct-producer cost. -/
theorem uniform_cost_formula (choice : C → P) :
    weightedReach Finset.univ (parents choice) (fun _ => 1) =
      Fintype.card P + 3 * Fintype.card C + 1 + (Finset.univ.image choice).card := by
  change (∑ r : Reaction P C, ∑ k ∈ ancestors choice r, (1:ℕ)) = _
  simp only [Finset.sum_const, smul_eq_mul, mul_one]
  rw [Fintype.sum_option, Fintype.sum_sum_type]
  simp [ancestors_producer, ancestors_consumer, aggregator_ancestor_card]
  omega

end RAFSupportSelection.Aggregator
