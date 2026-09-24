import proofs.RAFSupportSelection.PortfolioLimit

namespace RAFSupportSelection.OneLayer
open RAF RAFQueryCompilation
variable {C : Type*} [DecidableEq C] [Fintype C]

theorem producer_cone_card (choice : C → Bool) (b : Bool) :
    (selectedCone Finset.univ (parents choice) {Sum.inl b}).card =
      1 + (Finset.univ.filter (fun c => choice c = b)).card := by
  have he : selectedCone Finset.univ (parents choice) {Sum.inl b} =
      insert (Sum.inl b) ((Finset.univ.filter (fun c => choice c = b)).image Sum.inr) := by
    rw [cone_eq_region]
    ext r
    cases r with
    | inl a => simp [region]
    | inr c => simp [region]
  rw [he, Finset.card_insert_of_notMem (by simp),
    Finset.card_image_of_injective _ Sum.inr_injective]
  omega

theorem balanced_two_producer_certificate :
    ∃ choice : C → Bool, ∀ r : Bool ⊕ C,
      (selectedCone Finset.univ (parents choice) {r}).card ≤ 1 + (Fintype.card C + 1)/2 := by
  classical
  have hm : (Fintype.card C + 1)/2 ≤ (Finset.univ : Finset C).card := by
    simp only [Finset.card_univ]
    omega
  obtain ⟨A, _, hA⟩ := Finset.exists_subset_card_eq hm
  let choice : C → Bool := fun c => if c ∈ A then false else true
  have hfalse : Finset.univ.filter (fun c => choice c = false) = A := by
    ext c
    simp [choice]
  have htrue : Finset.univ.filter (fun c => choice c = true) = Finset.univ \ A := by
    ext c
    simp [choice]
  refine ⟨choice, ?_⟩
  intro r
  cases r with
  | inl b =>
    rw [producer_cone_card]
    cases b
    · rw [hfalse, hA]
    · rw [htrue, Finset.card_sdiff_of_subset (Finset.subset_univ A), Finset.card_univ, hA]
      omega
  | inr c =>
    have he : selectedCone Finset.univ (parents choice) {Sum.inr c} = {Sum.inr c} := by
      rw [cone_eq_region]
      ext r
      cases r <;> simp [region]
    rw [he, Finset.card_singleton]
    omega

theorem producer_singleton_loss (b : Bool) :
    Finset.univ \ evaluate (source (fun _ : C => (Finset.univ : Finset Bool)))
      (fun x r => x ∈ (foodCats r : Finset (Molecule Bool C)))
      (Finset.univ \ {Sum.inl b}) = {Sum.inl b} := by
  have he : (isolate (!b) : Finset (Bool ⊕ C)) = {Sum.inl b} := by
    ext r
    cases r with
    | inl a => cases a <;> cases b <;> simp [isolate]
    | inr c => simp [isolate]
  simpa only [he] using (isolate_exact_loss (C := C) (!b))

/-- A parametric unbounded worst-cone gap despite true producer loss being one. -/
theorem two_producer_gap (p : Bool ⊕ C → Finset (Bool ⊕ C)) (rank : Bool ⊕ C → ℕ)
    (hw : RankedSupport (source (fun _ : C => (Finset.univ : Finset Bool))) foodCats
      Finset.univ p rank) :
    ∃ b : Bool, 1 + (Fintype.card C + 1) / 2 ≤ (selectedCone Finset.univ p {Sum.inl b}).card := by
  classical
  obtain ⟨choice, _, hp⟩ := normalize_source_certificate (fun _ : C => (Finset.univ : Finset Bool)) p rank hw
  have hcover : (Finset.univ : Finset (Bool ⊕ C)) ⊆
      selectedCone Finset.univ p {Sum.inl false} ∪ selectedCone Finset.univ p {Sum.inl true} := by
    intro r _
    cases r with
    | inl b =>
      have hs := selectedCone_seed (Finset.univ : Finset (Bool ⊕ C)) p {Sum.inl b}
        (Finset.mem_inter.mpr ⟨Finset.mem_singleton_self _, Finset.mem_univ _⟩)
      cases b
      · exact Finset.mem_union_left _ hs
      · exact Finset.mem_union_right _ hs
    | inr c =>
      have hs : Sum.inr c ∈ selectedCone Finset.univ (parents choice) {Sum.inl (choice c)} := by
        simp [cone_eq_region, region]
      have ht := selectedCone_mono_parents Finset.univ {Sum.inl (choice c)} (parents choice) p
        (fun r _ => hp r) hs
      cases he : choice c
      · exact Finset.mem_union_left _ (by simpa only [he] using ht)
      · exact Finset.mem_union_right _ (by simpa only [he] using ht)
  have hc := Finset.card_le_card hcover
  have hu := Finset.card_union_le (selectedCone Finset.univ p {Sum.inl false})
    (selectedCone Finset.univ p {Sum.inl true})
  have hn : (Finset.univ : Finset (Bool ⊕ C)).card = 2 + Fintype.card C := by simp
  rw [hn] at hc
  by_contra hh
  push Not at hh
  have h0 := hh false
  have h1 := hh true
  omega

end RAFSupportSelection.OneLayer
