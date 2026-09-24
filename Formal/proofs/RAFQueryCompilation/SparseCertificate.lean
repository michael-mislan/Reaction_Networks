import proofs.RAFQueryCompilation.IndexedCertificate

namespace RAFQueryCompilation
open RAF
variable {M R : Type*} [DecidableEq M] [DecidableEq R]

def NeedsSound (Q : CRS M R) (C : Catalysis M R) (needs : R → Finset M) : Prop :=
  ∀ r x, (x ∈ Q.inputs r ∨ C x r) → x ∈ needs r

variable [Fintype M]
def sourceNeeds (Q : CRS M R) (C : Catalysis M R) [∀ x r, Decidable (C x r)]
    (r : R) : Finset M := Q.inputs r ∪ Finset.univ.filter (fun x => C x r)

omit [DecidableEq R] in
theorem sourceNeeds_sound (Q : CRS M R) (C : Catalysis M R)
    [∀ x r, Decidable (C x r)] : NeedsSound Q C (sourceNeeds Q C) := by
  intro r x hx
  simpa only [sourceNeeds, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
    true_and] using hx

/-- Boundary construction uses only region incidences and cached producer lookups. -/
def sparseFood (Q : CRS M R) (needs : R → Finset M) (S E : Finset R)
    (counts : M → ℕ) : Finset M :=
  Q.food ∪ (E.biUnion needs).filter
    (fun x => producerCount Q (restrictToRegion E S) x < counts x)

theorem sparse_food_exact (Q : CRS M R) (C : Catalysis M R)
    [∀ x r, Decidable (C x r)] (needs : R → Finset M) (hn : NeedsSound Q C needs)
    (S E I : Finset R) (counts : M → ℕ)
    (hc : ∀ x, counts x = producerCount Q S x) (hi : I ⊆ E) :
    evaluate (withFood Q (sparseFood Q needs S E counts)) C I =
      evaluate (residualSource Q (S \ E)) C I := by
  apply evaluate_food_agree Q C (sparseFood Q needs S E counts)
    (Q.food ∪ (S \ E).biUnion Q.outputs) I
  intro x hx
  obtain ⟨r, hr, hx⟩ := hx
  have he : x ∈ E.biUnion needs := Finset.mem_biUnion.mpr ⟨r, hi hr, hn r x hx⟩
  simp only [sparseFood, Finset.mem_union, Finset.mem_filter, he, true_and,
    restrictToRegion_eq, hc, outside_product_iff_count]

def checkSparseLocal (Q : CRS M R) (C : Catalysis M R)
    [∀ x r, Decidable (C x r)] (succ : R → Finset R) (needs : R → Finset M)
    (oldAnswer B D E : Finset R) (counts : M → ℕ) (certificate : List (List R)) :
    Option (Finset R) :=
  if checkRegion succ D E then
    checkPruning (withFood Q (sparseFood Q needs oldAnswer E counts)) C
      (restrictToRegion E B) certificate
  else none

/-- The checker avoids explicit universe enumeration; representation costs are separate. -/
theorem checkSparseLocal_sound (Q : CRS M R) (C : Catalysis M R)
    [∀ x r, Decidable (C x r)] (succ : R → Finset R) (needs : R → Finset M)
    (hi : IndexSound Q C succ) (hn : NeedsSound Q C needs)
    (A B D E : Finset R) (counts : M → ℕ) (certificate : List (List R))
    (hcounts : ∀ x, counts x = producerCount Q (evaluate Q C A) x)
    (hedits : ∀ r, (r ∈ A ↔ r ∈ B) ∨ r ∈ D) {localAnswer : Finset R}
    (h : checkSparseLocal Q C succ needs (evaluate Q C A) B D E counts certificate =
      some localAnswer) :
    evaluate Q C B = (evaluate Q C A \ E) ∪ localAnswer := by
  unfold checkSparseLocal at h
  split at h
  next hr =>
    have hregion := checkRegion_sound Q C succ hi D E hr
    rw [restrictToRegion_eq] at h
    have hl := checkPruning_sound _ C certificate _ h
    rw [sparse_food_exact Q C needs hn _ E _ counts hcounts Finset.inter_subset_right] at hl
    rw [hl]
    exact evaluate_cone_update Q C A B E hregion.2
      (outside_agree_of_edit_cover A B D E hedits hregion.1)
  next => contradiction

end RAFQueryCompilation
