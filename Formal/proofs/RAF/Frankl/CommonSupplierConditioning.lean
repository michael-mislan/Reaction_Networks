import proofs.RAF.Frankl.ElementaryConditioning

namespace RAF.Frankl.CommonSupplier
variable {R : Type*} [Fintype R] [DecidableEq R]

/-- Monotone failure predicates generalize multiple requirement bodies per head.
Every failure must contain the same deletion coordinate d(r). -/
def conditionedHorn (body : R → Finset R → Prop) (P : Finset R → Prop)
    (T : Finset R) : Prop := P T ∨ (∃ r, r ∉ T ∧ body r T)

def conditionedFree (body : R → Finset R → Prop) (P : Finset R → Prop)
    (T : Finset R) (r : R) : Prop := P T ∨ (∃ q, q ∉ T ∧ body q T ∧ q ≠ r)

noncomputable def conditionedCellMap (body : R → Finset R → Prop)
    (P : Finset R → Prop) (d : R → R) (z : Finset R × R) : Finset R × R := by
  classical
  exact if conditionedFree body P z.1 z.2 then (insert z.2 z.1, z.2)
    else (z.1, d z.2)

omit [Fintype R] in
theorem conditioned_noFree_head (body : R → Finset R → Prop) (P : Finset R → Prop)
    {T : Finset R} {r : R} (h : conditionedHorn body P T)
    (hn : ¬ conditionedFree body P T r) : r ∉ T ∧ body r T := by
  rcases h with hp | ⟨q,hq,hbody⟩
  · exact (hn (Or.inl hp)).elim
  have heq : q = r := by
    by_contra hne
    exact hn (Or.inr ⟨q,hq,hbody,hne⟩)
  simpa [heq] using And.intro hq hbody

omit [Fintype R] in
theorem conditioned_free_insert (body : R → Finset R → Prop) (P : Finset R → Prop)
    (hbodymono : ∀ r {A B}, A ⊆ B → body r A → body r B)
    (hmono : ∀ {A B}, A ⊆ B → P A → P B)
    {T : Finset R} {r : R} (h : conditionedFree body P T r) :
    conditionedHorn body P (insert r T) := by
  rcases h with hp | ⟨q,hq,hbody,hqr⟩
  · exact Or.inl (hmono (Finset.subset_insert r T) hp)
  · exact Or.inr ⟨q, by simpa [hqr] using hq,
      hbodymono q (Finset.subset_insert r T) hbody⟩

omit [Fintype R] in
/-- The mixed-collision exclusion, including the positive-predicate case. -/
theorem conditioned_free_dependency_insert
    (body : R → Finset R → Prop) (P : Finset R → Prop) (d : R → R)
    (hdep : ∀ r T, body r T → d r ∈ T)
    (hbodymono : ∀ r {A B}, A ⊆ B → body r A → body r B)
    (hmono : ∀ {A B}, A ⊆ B → P A → P B)
    {T : Finset R} {a b : R} (ha : a ∉ T) (hab : a = d b)
    (hf : conditionedFree body P T a) :
    conditionedFree body P (insert a T) b := by
  rcases hf with hp | ⟨q,hq,hbody,hqa⟩
  · exact Or.inl (hmono (Finset.subset_insert a T) hp)
  · have hqb : q ≠ b := by
      intro heq
      subst q
      exact ha (hab ▸ hdep b T hbody)
    exact Or.inr ⟨q, by simpa [hqa] using hq,
      hbodymono q (Finset.subset_insert a T) hbody, hqb⟩

theorem conditionedCellMap_mapsTo
    (body : R → Finset R → Prop) (P : Finset R → Prop) (d : R → R)
    (hdep : ∀ r T, body r T → d r ∈ T)
    (hbodymono : ∀ r {A B}, A ⊆ B → body r A → body r B)
    (hmono : ∀ {A B}, A ⊆ B → P A → P B) :
    Set.MapsTo (conditionedCellMap body P d)
      (matrixCells (conditionedHorn body P) false)
      (matrixCells (conditionedHorn body P) true) := by
  classical
  rintro ⟨T,r⟩ hz
  change (T,r) ∈ matrixCells (conditionedHorn body P) false at hz
  simp only [mem_matrixCells, Bool.false_eq_true, ↓reduceIte] at hz
  by_cases hf : conditionedFree body P T r
  · rw [conditionedCellMap, if_pos hf]
    exact (mem_matrixCells _ true _ _).2
      ⟨conditioned_free_insert body P hbodymono hmono hf, Finset.mem_insert_self r T⟩
  · rw [conditionedCellMap, if_neg hf]
    exact (mem_matrixCells _ true _ _).2
      ⟨hz.1, hdep r T (conditioned_noFree_head body P hz.1 hf).2⟩

theorem conditionedCellMap_injOn
    (body : R → Finset R → Prop) (P : Finset R → Prop) (d : R → R)
    (hdep : ∀ r T, body r T → d r ∈ T)
    (hbodymono : ∀ r {A B}, A ⊆ B → body r A → body r B)
    (hmono : ∀ {A B}, A ⊆ B → P A → P B) :
    ((matrixCells (conditionedHorn body P) false : Finset (Finset R × R)) :
      Set (Finset R × R)).InjOn (conditionedCellMap body P d) := by
  classical
  rintro ⟨A,a⟩ hA ⟨B,b⟩ hB heq
  change (A,a) ∈ matrixCells (conditionedHorn body P) false at hA
  change (B,b) ∈ matrixCells (conditionedHorn body P) false at hB
  simp only [mem_matrixCells, Bool.false_eq_true, ↓reduceIte] at hA hB
  by_cases ha : conditionedFree body P A a
  · by_cases hb : conditionedFree body P B b
    · simp only [conditionedCellMap, ha, hb, if_true] at heq
      have hab : a = b := congrArg Prod.snd heq
      subst b
      have hsets : insert a A = insert a B := congrArg Prod.fst heq
      have herase := congrArg (fun S : Finset R => S.erase a) hsets
      have hAB : A = B := by simpa [hA.2, hB.2] using herase
      subst B
      rfl
    · simp only [conditionedCellMap, ha, hb, if_true, if_false] at heq
      have hab : a = d b := congrArg Prod.snd heq
      have hBA : B = insert a A := (congrArg Prod.fst heq).symm
      exact (hb (hBA ▸ conditioned_free_dependency_insert body P d hdep hbodymono hmono
        hA.2 hab ha)).elim
  · by_cases hb : conditionedFree body P B b
    · simp only [conditionedCellMap, ha, hb, if_true, if_false] at heq
      have hba : b = d a := congrArg Prod.snd heq.symm
      have hAB : A = insert b B := congrArg Prod.fst heq
      exact (ha (hAB ▸ conditioned_free_dependency_insert body P d hdep hbodymono hmono
        hB.2 hba hb)).elim
    · simp only [conditionedCellMap, ha, hb, if_false] at heq
      have hAB : A = B := congrArg Prod.fst heq
      subst B
      have hh := conditioned_noFree_head body P hA.1 ha
      have hab : a = b := by
        by_contra hn
        exact hb (Or.inr ⟨a, hh.1, hh.2, hn⟩)
      subst b
      rfl

theorem conditionedHorn_zero_le_one
    (body : R → Finset R → Prop) (P : Finset R → Prop) (d : R → R)
    (hdep : ∀ r T, body r T → d r ∈ T)
    (hbodymono : ∀ r {A B}, A ⊆ B → body r A → body r B)
    (hmono : ∀ {A B}, A ⊆ B → P A → P B) :
    (matrixCells (conditionedHorn body P) false).card ≤
      (matrixCells (conditionedHorn body P) true).card := by
  classical
  exact Finset.card_le_card_of_injOn (conditionedCellMap body P d)
    (conditionedCellMap_mapsTo body P d hdep hbodymono hmono)
    (conditionedCellMap_injOn body P d hdep hbodymono hmono)

theorem conditionedHorn_false_one_le_zero
    (body : R → Finset R → Prop) (P : Finset R → Prop) (d : R → R)
    (hdep : ∀ r T, body r T → d r ∈ T)
    (hbodymono : ∀ r {A B}, A ⊆ B → body r A → body r B)
    (hmono : ∀ {A B}, A ⊆ B → P A → P B) :
    (matrixCells (fun T => ¬ conditionedHorn body P T) true).card ≤
      (matrixCells (fun T => ¬ conditionedHorn body P T) false).card := by
  have hz := matrixCells_partition (R := R) (conditionedHorn body P) false
  have ho := matrixCells_partition (R := R) (conditionedHorn body P) true
  have h := conditionedHorn_zero_le_one body P d hdep hbodymono hmono
  have hc : (matrixCells (fun _ : Finset R => True) false).card =
      (matrixCells (fun _ : Finset R => True) true).card := by
    have h0 : matrixCells (fun _ : Finset R => True) false =
        dependencyHornAllZeroCells R := by ext ⟨T,r⟩; simp
    have h1 : matrixCells (fun _ : Finset R => True) true =
        dependencyHornAllOneCells R := by ext ⟨T,r⟩; simp
    rw [h0,h1]
    exact dependencyHorn_allZero_card_eq_allOne_card
  omega


/-- The selected-coordinate average after arbitrary upward exterior conditioning. -/
theorem supported_upward_average
    (L : R → Finset R → Prop) (d : R → R)
    (hL : ∀ r {A B}, A ⊆ B → L r A → L r B)
    (hd : ∀ r S, d r ∈ S → L r S)
    (K : Finset R → Prop) (hK : ∀ {A B}, A ⊆ B → K A → K B) :
    by classical exact
    let H := fun S => K S ∧ ∀ r ∈ S, L r S
    (Finset.univ.powerset.filter H).card * Fintype.card R ≤
      2 * ∑ S ∈ Finset.univ.powerset.filter H, S.card := by
  classical
  dsimp only
  let H := fun S => K S ∧ ∀ r ∈ S, L r S
  let P := fun T => ¬ K (Finset.univ \ T)
  let body := fun r T => ¬ L r (Finset.univ \ T)
  have cm : ∀ {A B : Finset R}, A ⊆ B → Finset.univ \ B ⊆ Finset.univ \ A := by
    intro A B hab r hr
    simp only [Finset.mem_sdiff] at hr ⊢
    exact ⟨hr.1,fun ha => hr.2 (hab ha)⟩
  have hm : ∀ {A B}, A ⊆ B → P A → P B :=
    fun hab ha hb => ha (hK (cm hab) hb)
  have hb : ∀ r {A B}, A ⊆ B → body r A → body r B :=
    fun r {_ _} hab ha hb => ha (hL r (cm hab) hb)
  have hdep : ∀ r T, body r T → d r ∈ T := by
    intro r T ht
    by_contra hn
    exact ht (hd r _ (by simp [hn]))
  have heq : (fun T => ¬ conditionedHorn body P T) =
      (fun T => H (Finset.univ \ T)) := by
    funext T
    simp [conditionedHorn,P,body,H,not_or]
  have hh := conditionedHorn_false_one_le_zero body P d hdep hb hm
  rw [heq,matrixCells_complement_card,matrixCells_complement_card] at hh
  simp only [Bool.not_true,Bool.not_false] at hh
  have ht := matrixCells_total_card H
  rw [matrixCells_one_card] at hh ht
  change (Finset.univ.powerset.filter H).card * Fintype.card R ≤
    2 * ∑ S ∈ Finset.univ.powerset.filter H, S.card
  omega

end RAF.Frankl.CommonSupplier
