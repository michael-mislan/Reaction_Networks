import Mathlib

namespace RAF.Frankl

variable {R : Type*} [Fintype R] [DecidableEq R]

/-- A pure Horn DNF with one term for each negative head. -/
def dependencyHornDNF (body : R → Finset R) (T : Finset R) : Prop :=
  ∃ r, r ∉ T ∧ body r ⊆ T

noncomputable def dependencyHornTrueFamily (body : R → Finset R) :
    Finset (Finset R) := by
  classical
  exact Finset.univ.powerset.filter (dependencyHornDNF body)

noncomputable def dependencyHornZeroCells (body : R → Finset R) :
    Finset (Finset R × R) := by
  classical
  exact ((dependencyHornTrueFamily body).product Finset.univ).filter
    fun z => z.2 ∉ z.1

noncomputable def dependencyHornOneCells (body : R → Finset R) :
    Finset (Finset R × R) := by
  classical
  exact ((dependencyHornTrueFamily body).product Finset.univ).filter
    fun z => z.2 ∈ z.1

omit [DecidableEq R] in
@[simp] theorem mem_dependencyHornTrueFamily (body : R → Finset R)
    (T : Finset R) :
    T ∈ dependencyHornTrueFamily body ↔ dependencyHornDNF body T := by
  classical
  simp [dependencyHornTrueFamily]

@[simp] theorem mem_dependencyHornZeroCells (body : R → Finset R)
    (T : Finset R) (r : R) :
    (T, r) ∈ dependencyHornZeroCells body ↔
      dependencyHornDNF body T ∧ r ∉ T := by
  classical
  simp [dependencyHornZeroCells]

@[simp] theorem mem_dependencyHornOneCells (body : R → Finset R)
    (T : Finset R) (r : R) :
    (T, r) ∈ dependencyHornOneCells body ↔
      dependencyHornDNF body T ∧ r ∈ T := by
  classical
  simp [dependencyHornOneCells]

/-- A covering term is free in column `r` precisely when its negative head is
not `r`.  Its positive body is already contained in the row, so no positive
literal can mention the absent coordinate `r`. -/
def dependencyHornHasFreeCover (body : R → Finset R)
    (T : Finset R) (r : R) : Prop :=
  ∃ q, q ∉ T ∧ body q ⊆ T ∧ q ≠ r

/-- Lozin--Zamaraev's horizontal/vertical cell map. -/
noncomputable def dependencyHornCellMap
    (body : R → Finset R) (d : R → R) (z : Finset R × R) :
    Finset R × R := by
  classical
  exact if dependencyHornHasFreeCover body z.1 z.2
    then (insert z.2 z.1, z.2) else (z.1, d z.2)

theorem dependencyHornCellMap_mapsTo
    (body : R → Finset R) (d : R → R)
    (hdep : ∀ r, d r ∈ body r) :
    Set.MapsTo (dependencyHornCellMap body d)
      (dependencyHornZeroCells body) (dependencyHornOneCells body) := by
  classical
  rintro ⟨T, r⟩ hz
  change (T, r) ∈ dependencyHornZeroCells body at hz
  rw [mem_dependencyHornZeroCells] at hz
  by_cases hfree : dependencyHornHasFreeCover body T r
  · have hfree' := hfree
    obtain ⟨q, hqT, hbody, hqr⟩ := hfree'
    have hins : dependencyHornDNF body (insert r T) :=
      ⟨q, by simpa [hqr] using hqT,
        hbody.trans (Finset.subset_insert r T)⟩
    rw [dependencyHornCellMap, if_pos hfree]
    exact (mem_dependencyHornOneCells body (insert r T) r).2
      ⟨hins, Finset.mem_insert_self r T⟩
  · have hhead : body r ⊆ T := by
      obtain ⟨q, hqT, hbody⟩ := hz.1
      have hqr : q = r := by
        by_contra hne
        exact hfree ⟨q, hqT, hbody, hne⟩
      simpa [hqr] using hbody
    have hdT : d r ∈ T := hhead (hdep r)
    rw [dependencyHornCellMap, if_neg hfree]
    exact (mem_dependencyHornOneCells body T (d r)).2 ⟨hz.1, hdT⟩

theorem dependencyHornCellMap_injOn
    (body : R → Finset R) (d : R → R)
    (hdep : ∀ r, d r ∈ body r) :
    ((dependencyHornZeroCells body : Finset (Finset R × R)) :
      Set (Finset R × R)).InjOn (dependencyHornCellMap body d) := by
  classical
  rintro ⟨A, a⟩ hA ⟨B, b⟩ hB hEq
  change (A, a) ∈ dependencyHornZeroCells body at hA
  change (B, b) ∈ dependencyHornZeroCells body at hB
  rw [mem_dependencyHornZeroCells] at hA hB
  by_cases ha : dependencyHornHasFreeCover body A a
  · by_cases hb : dependencyHornHasFreeCover body B b
    · simp only [dependencyHornCellMap, ha, hb, if_true] at hEq
      have hab : a = b := congrArg Prod.snd hEq
      subst b
      have hsets : insert a A = insert a B := congrArg Prod.fst hEq
      have herase := congrArg (fun S : Finset R => S.erase a) hsets
      have hAB : A = B := by simpa [hA.2, hB.2] using herase
      subst B
      rfl
    · simp only [dependencyHornCellMap, ha, hb, if_true, if_false] at hEq
      have hadb : a = d b := congrArg Prod.snd hEq
      have hBA : B = insert a A := (congrArg Prod.fst hEq).symm
      obtain ⟨q, hqA, hqbody, hqa⟩ := ha
      by_cases hqb : q = b
      · subst q
        have hadA : d b ∈ A := hqbody (hdep b)
        exfalso
        exact hA.2 (hadb ▸ hadA)
      · exfalso
        apply hb
        refine ⟨q, ?_, hqbody.trans ?_, hqb⟩
        · rw [hBA]
          simp [hqa, hqA]
        · exact (Finset.subset_insert a A).trans (by
            rw [← hBA])
  · by_cases hb : dependencyHornHasFreeCover body B b
    · simp only [dependencyHornCellMap, ha, hb, if_false, if_true] at hEq
      have hbda : b = d a := congrArg Prod.snd hEq.symm
      have hAB : A = insert b B := congrArg Prod.fst hEq
      obtain ⟨q, hqB, hqbody, hqb⟩ := hb
      by_cases hqa : q = a
      · subst q
        have hbdB : d a ∈ B := hqbody (hdep a)
        exfalso
        exact hB.2 (hbda ▸ hbdB)
      · exfalso
        apply ha
        refine ⟨q, ?_, hqbody.trans ?_, hqa⟩
        · rw [hAB]
          simp [hqb, hqB]
        · exact (Finset.subset_insert b B).trans (by
            rw [← hAB])
    · simp only [dependencyHornCellMap, ha, hb, if_false] at hEq
      have hAB : A = B := congrArg Prod.fst hEq
      subst B
      have hahead : ∀ q, q ∉ A → body q ⊆ A → q = a := by
        intro q hq hqbody
        by_contra hqa
        exact ha ⟨q, hq, hqbody, hqa⟩
      have hbhead : ∀ q, q ∉ A → body q ⊆ A → q = b := by
        intro q hq hqbody
        by_contra hqb
        exact hb ⟨q, hq, hqbody, hqb⟩
      obtain ⟨q, hqA, hqbody⟩ := hA.1
      have hqa : q = a := hahead q hqA hqbody
      have hqb : q = b := hbhead q hqA hqbody
      subst a
      subst b
      rfl

theorem dependencyHorn_zeroCells_card_le_oneCells_card
    (body : R → Finset R) (d : R → R)
    (hdep : ∀ r, d r ∈ body r) :
    (dependencyHornZeroCells body).card ≤
      (dependencyHornOneCells body).card := by
  classical
  exact Finset.card_le_card_of_injOn (dependencyHornCellMap body d)
    (dependencyHornCellMap_mapsTo body d hdep)
    (dependencyHornCellMap_injOn body d hdep)

noncomputable def dependencyHornFalseFamily (body : R → Finset R) :
    Finset (Finset R) := by
  classical
  exact Finset.univ.powerset.filter fun T => ¬ dependencyHornDNF body T

noncomputable def dependencyHornAllZeroCells (R : Type*) [Fintype R] :
    Finset (Finset R × R) := by
  classical
  exact (Finset.univ.powerset.product Finset.univ).filter fun z => z.2 ∉ z.1

noncomputable def dependencyHornAllOneCells (R : Type*) [Fintype R] :
    Finset (Finset R × R) := by
  classical
  exact (Finset.univ.powerset.product Finset.univ).filter fun z => z.2 ∈ z.1

noncomputable def dependencyHornFalseZeroCells (body : R → Finset R) :
    Finset (Finset R × R) := by
  classical
  exact ((dependencyHornFalseFamily body).product Finset.univ).filter
    fun z => z.2 ∉ z.1

noncomputable def dependencyHornFalseOneCells (body : R → Finset R) :
    Finset (Finset R × R) := by
  classical
  exact ((dependencyHornFalseFamily body).product Finset.univ).filter
    fun z => z.2 ∈ z.1

omit [DecidableEq R] in
@[simp] theorem mem_dependencyHornFalseFamily (body : R → Finset R)
    (T : Finset R) :
    T ∈ dependencyHornFalseFamily body ↔ ¬ dependencyHornDNF body T := by
  classical
  simp [dependencyHornFalseFamily]

omit [DecidableEq R] in
@[simp] theorem mem_dependencyHornAllZeroCells (T : Finset R) (r : R) :
    (T, r) ∈ dependencyHornAllZeroCells R ↔ r ∉ T := by
  classical
  simp [dependencyHornAllZeroCells]

omit [DecidableEq R] in
@[simp] theorem mem_dependencyHornAllOneCells (T : Finset R) (r : R) :
    (T, r) ∈ dependencyHornAllOneCells R ↔ r ∈ T := by
  classical
  simp [dependencyHornAllOneCells]

@[simp] theorem mem_dependencyHornFalseZeroCells (body : R → Finset R)
    (T : Finset R) (r : R) :
    (T, r) ∈ dependencyHornFalseZeroCells body ↔
      ¬ dependencyHornDNF body T ∧ r ∉ T := by
  classical
  simp [dependencyHornFalseZeroCells]

@[simp] theorem mem_dependencyHornFalseOneCells (body : R → Finset R)
    (T : Finset R) (r : R) :
    (T, r) ∈ dependencyHornFalseOneCells body ↔
      ¬ dependencyHornDNF body T ∧ r ∈ T := by
  classical
  simp [dependencyHornFalseOneCells]

theorem dependencyHorn_allZero_card_eq_allOne_card :
    (dependencyHornAllZeroCells R).card =
      (dependencyHornAllOneCells R).card := by
  classical
  apply Nat.le_antisymm
  · apply Finset.card_le_card_of_injOn
      (fun z : Finset R × R => (insert z.2 z.1, z.2))
    · rintro ⟨T, r⟩ hz
      change (T, r) ∈ dependencyHornAllZeroCells R at hz
      simp
    · rintro ⟨A, a⟩ hA ⟨B, b⟩ hB hEq
      change (A, a) ∈ dependencyHornAllZeroCells R at hA
      change (B, b) ∈ dependencyHornAllZeroCells R at hB
      rw [mem_dependencyHornAllZeroCells] at hA hB
      have hab : a = b := congrArg Prod.snd hEq
      subst b
      have hsets : insert a A = insert a B := congrArg Prod.fst hEq
      have herase := congrArg (fun S : Finset R => S.erase a) hsets
      have hAB : A = B := by simpa [hA, hB] using herase
      subst B
      rfl
  · apply Finset.card_le_card_of_injOn
      (fun z : Finset R × R => (z.1.erase z.2, z.2))
    · rintro ⟨T, r⟩ hz
      change (T, r) ∈ dependencyHornAllOneCells R at hz
      simp
    · rintro ⟨A, a⟩ hA ⟨B, b⟩ hB hEq
      change (A, a) ∈ dependencyHornAllOneCells R at hA
      change (B, b) ∈ dependencyHornAllOneCells R at hB
      rw [mem_dependencyHornAllOneCells] at hA hB
      have hab : a = b := congrArg Prod.snd hEq
      subst b
      have hsets : A.erase a = B.erase a := congrArg Prod.fst hEq
      have hins := congrArg (insert a) hsets
      have hAB : A = B := by simpa [hA, hB] using hins
      subst B
      rfl

theorem dependencyHorn_allZero_partition (body : R → Finset R) :
    (dependencyHornAllZeroCells R).card =
      (dependencyHornZeroCells body).card +
        (dependencyHornFalseZeroCells body).card := by
  classical
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := dependencyHornAllZeroCells R)
    (p := fun z => dependencyHornDNF body z.1)
  have htrue :
      (dependencyHornAllZeroCells R).filter
          (fun z => dependencyHornDNF body z.1) =
        dependencyHornZeroCells body := by
    ext z
    rcases z with ⟨T, r⟩
    simp [and_comm]
  have hfalse :
      (dependencyHornAllZeroCells R).filter
          (fun z => ¬ dependencyHornDNF body z.1) =
        dependencyHornFalseZeroCells body := by
    ext z
    rcases z with ⟨T, r⟩
    simp [and_comm]
  rw [htrue, hfalse] at hsplit
  omega

theorem dependencyHorn_allOne_partition (body : R → Finset R) :
    (dependencyHornAllOneCells R).card =
      (dependencyHornOneCells body).card +
        (dependencyHornFalseOneCells body).card := by
  classical
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := dependencyHornAllOneCells R)
    (p := fun z => dependencyHornDNF body z.1)
  have htrue :
      (dependencyHornAllOneCells R).filter
          (fun z => dependencyHornDNF body z.1) =
        dependencyHornOneCells body := by
    ext z
    rcases z with ⟨T, r⟩
    simp [and_comm]
  have hfalse :
      (dependencyHornAllOneCells R).filter
          (fun z => ¬ dependencyHornDNF body z.1) =
        dependencyHornFalseOneCells body := by
    ext z
    rcases z with ⟨T, r⟩
    simp [and_comm]
  rw [htrue, hfalse] at hsplit
  omega

/-- The matrix injection on true points reverses on their complement: false
points have no more one-cells than zero-cells. -/
theorem dependencyHorn_falseOne_card_le_falseZero_card
    (body : R → Finset R) (d : R → R)
    (hdep : ∀ r, d r ∈ body r) :
    (dependencyHornFalseOneCells body).card ≤
      (dependencyHornFalseZeroCells body).card := by
  have hcube := dependencyHorn_allZero_card_eq_allOne_card (R := R)
  have hz := dependencyHorn_allZero_partition body
  have ho := dependencyHorn_allOne_partition body
  have htrue := dependencyHorn_zeroCells_card_le_oneCells_card body d hdep
  omega

theorem dependencyHorn_falseOne_fiber_card (body : R → Finset R) (r : R) :
    ((dependencyHornFalseOneCells body).filter fun z => z.2 = r).card =
      ((dependencyHornFalseFamily body).filter fun T => r ∈ T).card := by
  classical
  have heq :
      (dependencyHornFalseOneCells body).filter (fun z => z.2 = r) =
        ((dependencyHornFalseFamily body).filter fun T => r ∈ T).product {r} := by
    ext z
    rcases z with ⟨T, q⟩
    simp [dependencyHornFalseOneCells, eq_comm, and_comm]
    aesop
  rw [heq]
  simp

theorem dependencyHorn_falseZero_fiber_card (body : R → Finset R) (r : R) :
    ((dependencyHornFalseZeroCells body).filter fun z => z.2 = r).card =
      ((dependencyHornFalseFamily body).filter fun T => r ∉ T).card := by
  classical
  have heq :
      (dependencyHornFalseZeroCells body).filter (fun z => z.2 = r) =
        ((dependencyHornFalseFamily body).filter fun T => r ∉ T).product {r} := by
    ext z
    rcases z with ⟨T, q⟩
    simp [dependencyHornFalseZeroCells, eq_comm, and_comm]
    aesop
  rw [heq]
  simp

theorem dependencyHorn_falseOne_card_eq_sum (body : R → Finset R) :
    (dependencyHornFalseOneCells body).card =
      ∑ r : R, ((dependencyHornFalseFamily body).filter fun T => r ∈ T).card := by
  classical
  have h := Finset.sum_card_fiberwise_eq_card_filter
    (dependencyHornFalseOneCells body) (Finset.univ : Finset R) Prod.snd
  simp only [Finset.mem_univ, Finset.filter_true] at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro r _
  exact dependencyHorn_falseOne_fiber_card body r

theorem dependencyHorn_falseZero_card_eq_sum (body : R → Finset R) :
    (dependencyHornFalseZeroCells body).card =
      ∑ r : R, ((dependencyHornFalseFamily body).filter fun T => r ∉ T).card := by
  classical
  have h := Finset.sum_card_fiberwise_eq_card_filter
    (dependencyHornFalseZeroCells body) (Finset.univ : Finset R) Prod.snd
  simp only [Finset.mem_univ, Finset.filter_true] at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro r _
  exact dependencyHorn_falseZero_fiber_card body r

/-- Coordinate form of the dependency-Horn theorem: some variable occurs in
at most half of the false points. -/
theorem dependencyHorn_exists_false_frequency_le_omission [Nonempty R]
    (body : R → Finset R) (d : R → R)
    (hdep : ∀ r, d r ∈ body r) :
    ∃ r : R,
      ((dependencyHornFalseFamily body).filter fun T => r ∈ T).card ≤
        ((dependencyHornFalseFamily body).filter fun T => r ∉ T).card := by
  classical
  by_contra h
  push Not at h
  have hsum :
      (∑ r : R,
        ((dependencyHornFalseFamily body).filter fun T => r ∉ T).card) <
      ∑ r : R,
        ((dependencyHornFalseFamily body).filter fun T => r ∈ T).card := by
    apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
    intro r _
    exact h r
  rw [← dependencyHorn_falseZero_card_eq_sum,
    ← dependencyHorn_falseOne_card_eq_sum] at hsum
  exact (Nat.not_lt_of_ge
    (dependencyHorn_falseOne_card_le_falseZero_card body d hdep)) hsum

noncomputable def dependencyHornComplementFamily (body : R → Finset R) :
    Finset (Finset R) := by
  classical
  exact (dependencyHornFalseFamily body).image fun T => Finset.univ \ T

theorem univ_sdiff_inj (A B : Finset R)
    (h : Finset.univ \ A = Finset.univ \ B) : A = B := by
  classical
  ext r
  have hr := congrArg (fun T : Finset R => r ∈ T) h
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hr
  tauto

theorem dependencyHornComplementFamily_card (body : R → Finset R) :
    (dependencyHornComplementFamily body).card =
      (dependencyHornFalseFamily body).card := by
  classical
  unfold dependencyHornComplementFamily
  exact Finset.card_image_iff.mpr fun A _ B _ h => univ_sdiff_inj A B h

theorem dependencyHornComplementFamily_frequency (body : R → Finset R)
    (r : R) :
    ((dependencyHornComplementFamily body).filter fun S => r ∈ S).card =
      ((dependencyHornFalseFamily body).filter fun T => r ∉ T).card := by
  classical
  have heq :
      (dependencyHornComplementFamily body).filter (fun S => r ∈ S) =
        ((dependencyHornFalseFamily body).filter fun T => r ∉ T).image
          (fun T => Finset.univ \ T) := by
    ext S
    simp only [Finset.mem_filter, dependencyHornComplementFamily,
      Finset.mem_image, mem_dependencyHornFalseFamily]
    constructor
    · rintro ⟨⟨T, hfalse, rfl⟩, hr⟩
      exact ⟨T, ⟨hfalse, by simpa using hr⟩, rfl⟩
    · rintro ⟨T, ⟨hfalse, hr⟩, rfl⟩
      exact ⟨⟨T, hfalse, rfl⟩, by simpa using hr⟩
  rw [heq]
  exact Finset.card_image_iff.mpr fun A _ B _ h => univ_sdiff_inj A B h

/-- Frankl's inequality for the complements of the false points of a
dependency Horn DNF. -/
theorem dependencyHornComplementFamily_exists_abundant [Nonempty R]
    (body : R → Finset R) (d : R → R)
    (hdep : ∀ r, d r ∈ body r) :
    ∃ r : R, (dependencyHornComplementFamily body).card ≤
      2 * ((dependencyHornComplementFamily body).filter fun S => r ∈ S).card := by
  classical
  obtain ⟨r, hr⟩ :=
    dependencyHorn_exists_false_frequency_le_omission body d hdep
  refine ⟨r, ?_⟩
  rw [dependencyHornComplementFamily_card,
    dependencyHornComplementFamily_frequency]
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := dependencyHornFalseFamily body) (p := fun T => r ∈ T)
  omega

end RAF.Frankl
