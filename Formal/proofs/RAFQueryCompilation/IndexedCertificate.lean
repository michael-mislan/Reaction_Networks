import proofs.RAFQueryCompilation.UpdateCertificate

namespace RAFQueryCompilation
open RAF
variable {M R : Type*} [DecidableEq M] [DecidableEq R]

/-- A once-verified dependency index may conservatively contain extra edges. -/
def IndexSound (Q : CRS M R) (C : Catalysis M R) (succ : R → Finset R) : Prop :=
  ∀ e r x, x ∈ Q.outputs e → x ∉ Q.food →
    (x ∈ Q.inputs r ∨ C x r) → r ∈ succ e

def checkRegion (succ : R → Finset R) (D E : Finset R) : Bool :=
  decide (D ⊆ E ∧ ∀ e ∈ E, succ e ⊆ E)

theorem checkRegion_sound (Q : CRS M R) (C : Catalysis M R)
    (succ : R → Finset R) (hi : IndexSound Q C succ) (D E : Finset R)
    (h : checkRegion succ D E = true) : D ⊆ E ∧ OutsideIndependent Q C E := by
  have hc : D ⊆ E ∧ ∀ e ∈ E, succ e ⊆ E := of_decide_eq_true h
  refine ⟨hc.1, ?_⟩
  intro e he r hr x hx hn
  by_contra hf
  exact hr (hc.2 e he (hi e r x hx hf hn))

variable [Fintype R]
def sourceSuccessors (Q : CRS M R) (C : Catalysis M R)
    [∀ x r, Decidable (C x r)] (e : R) : Finset R :=
  Finset.univ.filter (fun r => ∃ x ∈ Q.outputs e,
    x ∉ Q.food ∧ (x ∈ Q.inputs r ∨ C x r))

omit [DecidableEq R] in
theorem sourceSuccessors_sound (Q : CRS M R) (C : Catalysis M R)
    [∀ x r, Decidable (C x r)] : IndexSound Q C (sourceSuccessors Q C) := by
  intro e r x hx hf hn
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, x, hx, hf, hn⟩

variable [Fintype M]

/-- Scan the proposed region, not the complete available or surviving set. -/
def restrictToRegion (E S : Finset R) : Finset R := E.filter (fun r => r ∈ S)

omit [Fintype M] [Fintype R] in
theorem restrictToRegion_eq (E S : Finset R) : restrictToRegion E S = S ∩ E := by
  ext r
  simp only [restrictToRegion, Finset.mem_filter, Finset.mem_inter]
  exact and_comm

def indexedFood (Q : CRS M R) (C : Catalysis M R) [∀ x r, Decidable (C x r)]
    (oldAnswer E : Finset R) (counts : M → ℕ) : Finset M :=
  Q.food ∪ (neededSet Q C E).filter
    (fun x => producerCount Q (restrictToRegion E oldAnswer) x < counts x)

omit [Fintype R] in
theorem indexedFood_eq (Q : CRS M R) (C : Catalysis M R)
    [∀ x r, Decidable (C x r)] (S E : Finset R) (counts : M → ℕ)
    (hc : ∀ x, counts x = producerCount Q S x) :
    indexedFood Q C S E counts = cachedFood Q C S E := by
  simp only [indexedFood, cachedFood, restrictToRegion_eq, hc]

/-- Return only the local answer. Global answer serialization is not performed. -/
def checkIndexedLocal (Q : CRS M R) (C : Catalysis M R)
    [∀ x r, Decidable (C x r)] (succ : R → Finset R)
    (oldAnswer B D E : Finset R) (counts : M → ℕ) (certificate : List (List R)) :
    Option (Finset R) :=
  if checkRegion succ D E then
    checkPruning (withFood Q (indexedFood Q C oldAnswer E counts)) C
      (restrictToRegion E B) certificate
  else none

omit [Fintype R] in
/-- Region-only checking with a source-authenticated index certifies global semantics. -/
theorem checkIndexedLocal_sound (Q : CRS M R) (C : Catalysis M R)
    [∀ x r, Decidable (C x r)] (succ : R → Finset R) (hi : IndexSound Q C succ)
    (A B D E : Finset R) (counts : M → ℕ) (certificate : List (List R))
    (hcounts : ∀ x, counts x = producerCount Q (evaluate Q C A) x)
    (hedits : ∀ r, (r ∈ A ↔ r ∈ B) ∨ r ∈ D) {localAnswer : Finset R}
    (h : checkIndexedLocal Q C succ (evaluate Q C A) B D E counts certificate =
      some localAnswer) :
    evaluate Q C B = (evaluate Q C A \ E) ∪ localAnswer := by
  unfold checkIndexedLocal at h
  split at h
  next hr =>
    have hregion := checkRegion_sound Q C succ hi D E hr
    rw [indexedFood_eq Q C _ E counts hcounts, restrictToRegion_eq] at h
    have hl := checkPruning_sound _ C certificate _ h
    rw [hl]
    exact evaluate_cached_cone_update Q C A B E hregion.2
      (outside_agree_of_edit_cover A B D E hedits hregion.1)
  next => contradiction

end RAFQueryCompilation
