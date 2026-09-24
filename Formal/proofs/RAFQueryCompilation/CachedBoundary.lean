import proofs.RAFQueryCompilation.BoundaryFood

namespace RAFQueryCompilation
open RAF
variable {M R : Type*} [DecidableEq M] [Fintype M] [DecidableEq R]

def producerCount (Q : CRS M R) (S : Finset R) (x : M) : ℕ :=
  (S.filter (fun r => x ∈ Q.outputs r)).card

omit [Fintype M] in
theorem producer_count_partition (Q : CRS M R) (S E : Finset R) (x : M) :
    producerCount Q (S \ E) x + producerCount Q (S ∩ E) x = producerCount Q S x := by
  have hd : (S \ E).filter (fun r => x ∈ Q.outputs r) =
      S.filter (fun r => x ∈ Q.outputs r) \ E := by ext r; simp; tauto
  have hi : (S ∩ E).filter (fun r => x ∈ Q.outputs r) =
      S.filter (fun r => x ∈ Q.outputs r) ∩ E := by ext r; simp; tauto
  simp only [producerCount, hd, hi]
  exact Finset.card_sdiff_add_card_inter _ _

omit [Fintype M] in
theorem outside_product_iff_count (Q : CRS M R) (S E : Finset R) (x : M) :
    x ∈ (S \ E).biUnion Q.outputs ↔
      producerCount Q (S ∩ E) x < producerCount Q S x := by
  have hp := producer_count_partition Q S E x
  have hz : x ∈ (S \ E).biUnion Q.outputs ↔ 0 < producerCount Q (S \ E) x := by
    simp [producerCount, Finset.card_pos, Finset.Nonempty]
  rw [hz]
  omega

def neededSet (Q : CRS M R) (C : Catalysis M R) [∀ x r, Decidable (C x r)]
    (E : Finset R) : Finset M :=
  E.biUnion (fun r => Q.inputs r ∪ Finset.univ.filter (fun x => C x r))

omit [DecidableEq R] in
theorem mem_neededSet (Q : CRS M R) (C : Catalysis M R)
    [∀ x r, Decidable (C x r)] (E : Finset R) (x : M) :
    x ∈ neededSet Q C E ↔ Needed Q C E x := by
  simp [neededSet, Needed]

def cachedFood (Q : CRS M R) (C : Catalysis M R) [∀ x r, Decidable (C x r)]
    (S E : Finset R) : Finset M :=
  Q.food ∪ (neededSet Q C E).filter
    (fun x => producerCount Q (S ∩ E) x < producerCount Q S x)

/-- Only molecules used locally need the cached outside-production test. -/
theorem cached_food_exact (Q : CRS M R) (C : Catalysis M R)
    [∀ x r, Decidable (C x r)] (S E I : Finset R) (hi : I ⊆ E) :
    evaluate (withFood Q (cachedFood Q C S E)) C I =
      evaluate (residualSource Q (S \ E)) C I := by
  apply evaluate_food_agree Q C (cachedFood Q C S E)
    (Q.food ∪ (S \ E).biUnion Q.outputs) I
  intro x hx
  obtain ⟨r, hr, hn⟩ := hx
  have he : x ∈ neededSet Q C E := (mem_neededSet Q C E x).mpr ⟨r, hi hr, hn⟩
  simp only [cachedFood, Finset.mem_union, Finset.mem_filter, he, true_and,
    outside_product_iff_count]

theorem evaluate_cached_cone_update (Q : CRS M R) (C : Catalysis M R)
    [∀ x r, Decidable (C x r)] (A B E : Finset R)
    (hind : OutsideIndependent Q C E) (hab : A \ E = B \ E) :
    evaluate Q C B = (evaluate Q C A \ E) ∪
      evaluate (withFood Q (cachedFood Q C (evaluate Q C A) E)) C (B ∩ E) := by
  rw [cached_food_exact Q C _ _ _ Finset.inter_subset_right]
  exact evaluate_cone_update Q C A B E hind hab

end RAFQueryCompilation
