import proofs.RAFQueryCompilation.RankedExistence

namespace RAFQueryCompilation
open RAF

variable {M R : Type*} [DecidableEq M] [DecidableEq R]

theorem small_ranked_row (Q : CRS M R) (cats : R → Finset M) (S : Finset R)
    (parents : R → Finset R) (rank : R → ℕ) (hw : RankedSupport Q cats S parents rank)
    (r : R) (hr : r ∈ S) :
    ∃ P : Finset R, P ⊆ S ∩ parents r ∧ P.card ≤ (Q.inputs r \ Q.food).card + 1 ∧
      (∀ x ∈ Q.inputs r, x ∈ Q.food ∨ ∃ p ∈ P, rank p < rank r ∧ x ∈ Q.outputs p) ∧
      (∃ x ∈ cats r, x ∈ Q.food ∨ ∃ p ∈ P, x ∈ Q.outputs p) := by
  classical
  have hneed : ∀ x : {x // x ∈ Q.inputs r \ Q.food},
      ∃ p, p ∈ S ∧ p ∈ parents r ∧ rank p < rank r ∧ x.val ∈ Q.outputs p := by
    intro x
    have hx := Finset.mem_sdiff.mp x.property
    rcases hw.1 r hr x.val hx.1 with hf | hp
    · exact False.elim (hx.2 hf)
    · exact hp
  choose producer hproducer using hneed
  let P := (Q.inputs r \ Q.food).attach.image producer
  have hsub : P ⊆ S ∩ parents r := by
    intro p hp
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_inter.mpr ⟨(hproducer x).1, (hproducer x).2.1⟩
  have hcard : P.card ≤ (Q.inputs r \ Q.food).card := by
    calc
      P.card ≤ (Q.inputs r \ Q.food).attach.card := Finset.card_image_le
      _ = (Q.inputs r \ Q.food).card := Finset.card_attach
  have hinputs : ∀ x ∈ Q.inputs r, x ∈ Q.food ∨
      ∃ p ∈ P, rank p < rank r ∧ x ∈ Q.outputs p := by
    intro x hx
    by_cases hf : x ∈ Q.food
    · exact Or.inl hf
    · let y : {x // x ∈ Q.inputs r \ Q.food} := ⟨x, Finset.mem_sdiff.mpr ⟨hx, hf⟩⟩
      refine Or.inr ⟨producer y, ?_, (hproducer y).2.2.1, (hproducer y).2.2.2⟩
      exact Finset.mem_image.mpr ⟨y, Finset.mem_attach _ _, rfl⟩
  obtain ⟨x, hx, hcat⟩ := hw.2 r hr
  rcases hcat with hf | ⟨p, hpS, hpParents, hout⟩
  · exact ⟨P, hsub, hcard.trans (Nat.le_succ _), hinputs, x, hx, Or.inl hf⟩
  · refine ⟨insert p P, ?_, ?_, ?_, x, hx, Or.inr ⟨p, Finset.mem_insert_self _ _, hout⟩⟩
    · exact Finset.insert_subset (Finset.mem_inter.mpr ⟨hpS, hpParents⟩) hsub
    · exact (Finset.card_insert_le _ _).trans (Nat.add_le_add_right hcard 1)
    · intro y hy
      rcases hinputs y hy with hf | ⟨q, hq, hlt, hprod⟩
      · exact Or.inl hf
      · exact Or.inr ⟨q, Finset.mem_insert_of_mem hq, hlt, hprod⟩

theorem ranked_support_sparsify (Q : CRS M R) (cats : R → Finset M) (S : Finset R)
    (parents : R → Finset R) (rank : R → ℕ) (hw : RankedSupport Q cats S parents rank) :
    ∃ small : R → Finset R, RankedSupport Q cats S small rank ∧
      ∀ r, small r ⊆ S ∩ parents r ∧ (small r).card ≤ (Q.inputs r \ Q.food).card + 1 := by
  classical
  choose row hrow using (fun r hr => small_ranked_row Q cats S parents rank hw r hr)
  let small : R → Finset R := fun r => if hr : r ∈ S then row r hr else ∅
  refine ⟨small, ?_, ?_⟩
  · constructor
    · intro r hr x hx
      rcases (hrow r hr).2.2.1 x hx with hf | ⟨p, hp, hlt, hout⟩
      · exact Or.inl hf
      · refine Or.inr ⟨p, (Finset.mem_inter.mp ((hrow r hr).1 hp)).1, ?_, hlt, hout⟩
        simpa only [small, dif_pos hr] using hp
    · intro r hr
      obtain ⟨x, hx, hcat⟩ := (hrow r hr).2.2.2
      refine ⟨x, hx, ?_⟩
      rcases hcat with hf | ⟨p, hp, hout⟩
      · exact Or.inl hf
      · refine Or.inr ⟨p, (Finset.mem_inter.mp ((hrow r hr).1 hp)).1, ?_, hout⟩
        simpa only [small, dif_pos hr] using hp
  · intro r
    by_cases hr : r ∈ S
    · simpa only [small, dif_pos hr] using And.intro (hrow r hr).1 (hrow r hr).2.1
    · simp [small, hr]

/-- Every ordinary RAF admits sparse ranked witnesses, with no ray or CAF assumption. -/
theorem raf_sparse_ranked_exists (Q : CRS M R) (cats : R → Finset M) (S : Finset R)
    (hs : IsRAF Q (fun x r => x ∈ cats r) S) :
    ∃ (rank : R → ℕ) (parents : R → Finset R), RankedSupport Q cats S parents rank ∧
      ∀ r, parents r ⊆ S ∧ (parents r).card ≤ (Q.inputs r \ Q.food).card + 1 := by
  obtain ⟨rank, hw⟩ := raf_ranked_exists Q cats S hs
  obtain ⟨parents, hp, hsize⟩ := ranked_support_sparsify Q cats S (fun _ => S) rank hw
  exact ⟨rank, parents, hp, by simpa using hsize⟩

/-- The actual maximum, including the empty case, always has a sparse certificate. -/
theorem evaluate_sparse_ranked_exists [Fintype M] (Q : CRS M R)
    (cats : R → Finset M) (A : Finset R) :
    ∃ (rank : R → ℕ) (parents : R → Finset R),
      RankedSupport Q cats (evaluate Q (fun x r => x ∈ cats r) A) parents rank ∧
      ∀ r, parents r ⊆ evaluate Q (fun x r => x ∈ cats r) A ∧
        (parents r).card ≤ (Q.inputs r \ Q.food).card + 1 := by
  classical
  rcases (evaluate_spec Q (fun x r => x ∈ cats r) A).2.1 with he | hraf
  · refine ⟨fun _ => 0, fun _ => ∅, ?_, ?_⟩
    · simp [he, RankedSupport]
    · intro r; simp
  · exact raf_sparse_ranked_exists Q cats _ hraf

omit [DecidableEq R] in
theorem sparse_parent_total (Q : CRS M R) (S : Finset R) (parents : R → Finset R)
    (h : ∀ r ∈ S, (parents r).card ≤ (Q.inputs r \ Q.food).card + 1) :
    (∑ r ∈ S, (parents r).card) ≤ (∑ r ∈ S, (Q.inputs r \ Q.food).card) + S.card := by
  calc
    (∑ r ∈ S, (parents r).card) ≤ ∑ r ∈ S, ((Q.inputs r \ Q.food).card + 1) :=
      Finset.sum_le_sum h
    _ = _ := by simp [Finset.sum_add_distrib]

end RAFQueryCompilation
