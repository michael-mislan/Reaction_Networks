import proofs.DUnstableCores.Elementary.ElementaryPatterns

namespace DUnstableCores

def elementaryChildChoice (κ : ChildSelection elementarySource) (i : Fin 4) : Option (Fin 6) :=
  if h : i ∈ κ.species then some (κ.assign ⟨i,h⟩).1 else none

theorem elementaryChildChoice_reactant (κ : ChildSelection elementarySource)
    (i : Fin 4) (r : Fin 6) (h : elementaryChildChoice κ i = some r) :
    elementarySource.Reactant i r := by
  unfold elementaryChildChoice at h
  split at h
  next hi =>
    have hr := Option.some.inj h
    simpa [hr] using κ.reactant_match ⟨i,hi⟩
  next hi => simp at h

theorem elementaryChildChoice_injective (κ : ChildSelection elementarySource)
    (i j : Fin 4) (r : Fin 6) (hi : elementaryChildChoice κ i = some r)
    (hj : elementaryChildChoice κ j = some r) : i=j := by
  unfold elementaryChildChoice at hi hj
  split at hi
  next hmi =>
    split at hj
    next hmj =>
      have heq : κ.assign ⟨i,hmi⟩ = κ.assign ⟨j,hmj⟩ :=
        Subtype.ext ((Option.some.inj hi).trans (Option.some.inj hj).symm)
      exact congrArg Subtype.val (κ.assign.injective heq)
    next hmj => simp at hj
  next hmi => simp at hi

theorem elementaryChildChoice_patterns (κ : ChildSelection elementarySource) :
    ∃ (a b : Fin 2) (c d : Fin 3), elementaryChoiceValid a b c d ∧
      elementaryChoice a b c d = elementaryChildChoice κ := by
  classical
  have h0 : elementaryChildChoice κ 0 = none ∨ elementaryChildChoice κ 0 = some 0 := by
    cases h : elementaryChildChoice κ 0 with
    | none => exact Or.inl rfl
    | some r =>
      have hr := elementaryChildChoice_reactant κ 0 r h
      fin_cases r <;> simp_all [SourceNetwork.Reactant, elementarySource]
  have h1 : elementaryChildChoice κ 1 = none ∨ elementaryChildChoice κ 1 = some 1 := by
    cases h : elementaryChildChoice κ 1 with
    | none => exact Or.inl rfl
    | some r =>
      have hr := elementaryChildChoice_reactant κ 1 r h
      fin_cases r <;> simp_all [SourceNetwork.Reactant, elementarySource]
  have h2 : elementaryChildChoice κ 2 = none ∨ elementaryChildChoice κ 2 = some 1 ∨
      elementaryChildChoice κ 2 = some 2 := by
    cases h : elementaryChildChoice κ 2 with
    | none => exact Or.inl rfl
    | some r =>
      have hr := elementaryChildChoice_reactant κ 2 r h
      fin_cases r <;> simp_all [SourceNetwork.Reactant, elementarySource]
  have h3 : elementaryChildChoice κ 3 = none ∨ elementaryChildChoice κ 3 = some 0 ∨
      elementaryChildChoice κ 3 = some 3 := by
    cases h : elementaryChildChoice κ 3 with
    | none => exact Or.inl rfl
    | some r =>
      have hr := elementaryChildChoice_reactant κ 3 r h
      fin_cases r <;> simp_all [SourceNetwork.Reactant, elementarySource]
  let a : Fin 2 := if elementaryChildChoice κ 0 = none then 0 else 1
  let b : Fin 2 := if elementaryChildChoice κ 1 = none then 0 else 1
  let c : Fin 3 := if elementaryChildChoice κ 2 = none then 0 else
    if elementaryChildChoice κ 2 = some 1 then 1 else 2
  let d : Fin 3 := if elementaryChildChoice κ 3 = none then 0 else
    if elementaryChildChoice κ 3 = some 0 then 1 else 2
  have heq : elementaryChoice a b c d = elementaryChildChoice κ := by
    funext i
    fin_cases i
    · rcases h0 with h0|h0 <;> simp [elementaryChoice,a,h0]
    · rcases h1 with h1|h1 <;> simp [elementaryChoice,b,h1]
    · rcases h2 with h2|h2|h2 <;> simp [elementaryChoice,c,h2]
    · rcases h3 with h3|h3|h3 <;> simp [elementaryChoice,d,h3]
  refine ⟨a,b,c,d,?_,heq⟩
  constructor
  · rintro ⟨ha,hd⟩
    have hi : elementaryChildChoice κ 0 = some 0 := by
      rw [←heq]; simp [elementaryChoice,ha]
    have hj : elementaryChildChoice κ 3 = some 0 := by
      rw [←heq]; simp [elementaryChoice,hd]
    have := elementaryChildChoice_injective κ 0 3 0 hi hj
    norm_num [Fin.ext_iff] at this
  · rintro ⟨hb,hc⟩
    have hi : elementaryChildChoice κ 1 = some 1 := by
      rw [←heq]; simp [elementaryChoice,hb]
    have hj : elementaryChildChoice κ 2 = some 1 := by
      rw [←heq]; simp [elementaryChoice,hc]
    have := elementaryChildChoice_injective κ 1 2 1 hi hj
    norm_num [Fin.ext_iff] at this

/-- A padded pattern adds only decoupled negative diagonal coordinates.
Every unstable child eigenvector extends by zero to its padded pattern. -/
theorem elementaryChild_of_pattern (κ : ChildSelection elementarySource)
    (a b : Fin 2) (c d : Fin 3)
    (hmatch : elementaryChoice a b c d = elementaryChildChoice κ)
    (hsafe : DNonUnstable (elementaryPatternMatrix a b c d)) : DNonUnstable κ.realMatrix := by
  classical
  intro scale hscale hunstable
  obtain ⟨z,v,hz,hv⟩ := hunstable
  let scale' : Fin 4 → ℝ := fun i => if h:i∈κ.species then scale ⟨i,h⟩ else 1
  let w : Fin 4 → ℂ := fun i => if h:i∈κ.species then v ⟨i,h⟩ else 0
  have hscale' : ∀ i, 0 < scale' i := by
    intro i
    dsimp [scale']
    split
    next hi => exact hscale _
    next hi => norm_num
  apply hsafe scale' hscale'
  refine ⟨z,w,hz,?_,?_⟩
  · intro hw
    apply hv.1
    funext i
    have hi := congrFun hw i.1
    simpa [w,i.2] using hi
  · intro i
    by_cases hi : i∈κ.species
    · have hsum :
          (∑ j : Fin 4, complexify (rightScale (elementaryPatternMatrix a b c d) scale') i j * w j) =
          ∑ j : κ.species, complexify (rightScale κ.realMatrix scale) ⟨i,hi⟩ j * v j := by
        calc
          _ = ∑ j ∈ κ.species,
              complexify (rightScale (elementaryPatternMatrix a b c d) scale') i j * w j := by
            symm
            apply Finset.sum_subset (Finset.subset_univ _)
            intro j _ hj
            simp [w,hj]
          _ = ∑ j : κ.species,
              complexify (rightScale (elementaryPatternMatrix a b c d) scale') i j.1 * w j.1 :=
            (Finset.sum_coe_sort κ.species _).symm
          _ = _ := by
            apply Finset.sum_congr rfl
            intro j _
            simp [complexify, rightScale, elementaryPatternMatrix, hmatch,
              elementaryChildChoice, scale',w,hi,j.2,ChildSelection.realMatrix,
              ChildSelection.matrix_eq_stoich]
      change (∑ j : Fin 4, complexify (rightScale (elementaryPatternMatrix a b c d) scale') i j * w j) = z*w i
      rw [hsum]
      simpa [Matrix.mulVec,dotProduct,w,hi] using hv.2 ⟨i,hi⟩
    · change (∑ j : Fin 4, complexify (rightScale (elementaryPatternMatrix a b c d) scale') i j * w j) = z*w i
      have hzero : ∀ j : Fin 4,
          complexify (rightScale (elementaryPatternMatrix a b c d) scale') i j * w j = 0 := by
        intro j
        by_cases hj : j∈κ.species
        · simp [complexify,rightScale,elementaryPatternMatrix,hmatch,elementaryChildChoice,hi,hj]
        · simp [w,hj]
      simp [hzero,w,hi]

theorem elementarySource_all_children (κ : ChildSelection elementarySource) :
    DNonUnstable κ.realMatrix := by
  obtain ⟨a,b,c,d,hvalid,hmatch⟩ := elementaryChildChoice_patterns κ
  exact elementaryChild_of_pattern κ a b c d hmatch
    (elementary_all_patterns a b c d hvalid)

end DUnstableCores
