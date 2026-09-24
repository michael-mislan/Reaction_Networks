import proofs.RAF.Frankl.DependencyHorn

/-! The dependency counting injection with an additional monotone positive
predicate. This is the aggregate kernel needed for relative-upset conditioning.
The underlying horizontal/vertical counting method is due to Lozin--Zamaraev. -/

namespace RAF.Frankl

variable {R : Type*} [Fintype R] [DecidableEq R]

def conditionedHorn (body : R → Finset R) (P : Finset R → Prop)
    (T : Finset R) : Prop := P T ∨ dependencyHornDNF body T

def conditionedFree (body : R → Finset R) (P : Finset R → Prop)
    (T : Finset R) (r : R) : Prop := P T ∨ dependencyHornHasFreeCover body T r

noncomputable def matrixCells (H : Finset R → Prop) (bit : Bool) :
    Finset (Finset R × R) := by
  classical
  exact (Finset.univ.powerset.product Finset.univ).filter
    fun z => H z.1 ∧ (if bit then z.2 ∈ z.1 else z.2 ∉ z.1)

@[simp] theorem mem_matrixCells (H : Finset R → Prop) (bit : Bool)
    (T : Finset R) (r : R) :
    (T,r) ∈ matrixCells H bit ↔ H T ∧ (if bit then r ∈ T else r ∉ T) := by
  classical
  simp [matrixCells]

noncomputable def conditionedCellMap (body : R → Finset R)
    (P : Finset R → Prop) (d : R → R) (z : Finset R × R) : Finset R × R := by
  classical
  exact if conditionedFree body P z.1 z.2 then (insert z.2 z.1, z.2)
    else (z.1, d z.2)

omit [Fintype R] in
theorem conditioned_noFree_head (body : R → Finset R) (P : Finset R → Prop)
    {T : Finset R} {r : R} (h : conditionedHorn body P T)
    (hn : ¬ conditionedFree body P T r) : r ∉ T ∧ body r ⊆ T := by
  rcases h with hp | ⟨q,hq,hbody⟩
  · exact (hn (Or.inl hp)).elim
  have heq : q = r := by
    by_contra hne
    exact hn (Or.inr ⟨q,hq,hbody,hne⟩)
  simpa [heq] using And.intro hq hbody

omit [Fintype R] in
theorem conditioned_free_insert (body : R → Finset R) (P : Finset R → Prop)
    (hmono : ∀ {A B}, A ⊆ B → P A → P B)
    {T : Finset R} {r : R} (h : conditionedFree body P T r) :
    conditionedHorn body P (insert r T) := by
  rcases h with hp | ⟨q,hq,hbody,hqr⟩
  · exact Or.inl (hmono (Finset.subset_insert r T) hp)
  · exact Or.inr ⟨q, by simpa [hqr] using hq,
      hbody.trans (Finset.subset_insert r T)⟩

omit [Fintype R] in
/-- The mixed-collision exclusion, including the positive-predicate case. -/
theorem conditioned_free_dependency_insert
    (body : R → Finset R) (P : Finset R → Prop) (d : R → R)
    (hdep : ∀ r, d r ∈ body r)
    (hmono : ∀ {A B}, A ⊆ B → P A → P B)
    {T : Finset R} {a b : R} (ha : a ∉ T) (hab : a = d b)
    (hf : conditionedFree body P T a) :
    conditionedFree body P (insert a T) b := by
  rcases hf with hp | ⟨q,hq,hbody,hqa⟩
  · exact Or.inl (hmono (Finset.subset_insert a T) hp)
  · have hqb : q ≠ b := by
      intro heq
      subst q
      exact ha (hab ▸ hbody (hdep b))
    exact Or.inr ⟨q, by simpa [hqa] using hq,
      hbody.trans (Finset.subset_insert a T), hqb⟩

theorem conditionedCellMap_mapsTo
    (body : R → Finset R) (P : Finset R → Prop) (d : R → R)
    (hdep : ∀ r, d r ∈ body r)
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
      ⟨conditioned_free_insert body P hmono hf, Finset.mem_insert_self r T⟩
  · rw [conditionedCellMap, if_neg hf]
    exact (mem_matrixCells _ true _ _).2
      ⟨hz.1, (conditioned_noFree_head body P hz.1 hf).2 (hdep r)⟩

theorem conditionedCellMap_injOn
    (body : R → Finset R) (P : Finset R → Prop) (d : R → R)
    (hdep : ∀ r, d r ∈ body r)
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
      exact (hb (hBA ▸ conditioned_free_dependency_insert body P d hdep hmono
        hA.2 hab ha)).elim
  · by_cases hb : conditionedFree body P B b
    · simp only [conditionedCellMap, ha, hb, if_true, if_false] at heq
      have hba : b = d a := congrArg Prod.snd heq.symm
      have hAB : A = insert b B := congrArg Prod.fst heq
      exact (ha (hAB ▸ conditioned_free_dependency_insert body P d hdep hmono
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
    (body : R → Finset R) (P : Finset R → Prop) (d : R → R)
    (hdep : ∀ r, d r ∈ body r)
    (hmono : ∀ {A B}, A ⊆ B → P A → P B) :
    (matrixCells (conditionedHorn body P) false).card ≤
      (matrixCells (conditionedHorn body P) true).card := by
  classical
  exact Finset.card_le_card_of_injOn (conditionedCellMap body P d)
    (conditionedCellMap_mapsTo body P d hdep hmono)
    (conditionedCellMap_injOn body P d hdep hmono)

theorem matrixCells_partition (H : Finset R → Prop) (bit : Bool) :
    (matrixCells H bit).card + (matrixCells (fun T => ¬ H T) bit).card =
      (matrixCells (fun _ : Finset R => True) bit).card := by
  classical
  have h := Finset.card_filter_add_card_filter_not
    (s := matrixCells (fun _ : Finset R => True) bit) (p := fun z => H z.1)
  have h1 : (matrixCells (fun _ : Finset R => True) bit).filter (fun z => H z.1) =
      matrixCells H bit := by ext ⟨T,r⟩; simp [and_comm]
  have h2 : (matrixCells (fun _ : Finset R => True) bit).filter (fun z => ¬ H z.1) =
      matrixCells (fun T => ¬ H T) bit := by ext ⟨T,r⟩; simp [and_comm]
  rwa [h1,h2] at h

theorem conditionedHorn_false_one_le_zero
    (body : R → Finset R) (P : Finset R → Prop) (d : R → R)
    (hdep : ∀ r, d r ∈ body r)
    (hmono : ∀ {A B}, A ⊆ B → P A → P B) :
    (matrixCells (fun T => ¬ conditionedHorn body P T) true).card ≤
      (matrixCells (fun T => ¬ conditionedHorn body P T) false).card := by
  have hz := matrixCells_partition (R := R) (conditionedHorn body P) false
  have ho := matrixCells_partition (R := R) (conditionedHorn body P) true
  have h := conditionedHorn_zero_le_one body P d hdep hmono
  have hc : (matrixCells (fun _ : Finset R => True) false).card =
      (matrixCells (fun _ : Finset R => True) true).card := by
    have h0 : matrixCells (fun _ : Finset R => True) false =
        dependencyHornAllZeroCells R := by ext ⟨T,r⟩; simp
    have h1 : matrixCells (fun _ : Finset R => True) true =
        dependencyHornAllOneCells R := by ext ⟨T,r⟩; simp
    rw [h0,h1]
    exact dependencyHorn_allZero_card_eq_allOne_card
  omega

theorem matrixCells_one_card (H : Finset R → Prop) [DecidablePred H] :
    (matrixCells H true).card =
      ∑ T ∈ Finset.univ.powerset.filter H, T.card := by
  classical
  simp only [matrixCells, Finset.product_eq_sprod, Finset.card_eq_sum_ones, Finset.sum_filter,
    Finset.sum_product, ↓reduceIte]
  apply Finset.sum_congr rfl
  intro T _
  by_cases hT : H T
  · simp [hT]
  · simp [hT]

theorem matrixCells_total_card (H : Finset R → Prop) [DecidablePred H] :
    (matrixCells H false).card + (matrixCells H true).card =
      (Finset.univ.powerset.filter H).card * Fintype.card R := by
  classical
  have h := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ.powerset.filter H).product (Finset.univ : Finset R))
    (p := fun z => z.2 ∈ z.1)
  have h1 : ((Finset.univ.powerset.filter H).product (Finset.univ : Finset R)).filter
      (fun z => z.2 ∈ z.1) = matrixCells H true := by
    ext ⟨T,r⟩; simp
  have h0 : ((Finset.univ.powerset.filter H).product (Finset.univ : Finset R)).filter
      (fun z => ¬ z.2 ∈ z.1) = matrixCells H false := by
    ext ⟨T,r⟩; simp
  rw [h1,h0,Finset.product_eq_sprod,Finset.card_product,Finset.card_univ] at h
  omega

theorem matrixCells_complement_card (H : Finset R → Prop) (bit : Bool) :
    (matrixCells (fun T => H (Finset.univ \ T)) bit).card =
      (matrixCells H (!bit)).card := by
  classical
  let f : Finset R × R → Finset R × R := fun z => (Finset.univ \ z.1,z.2)
  have hi : Function.Injective f := by
    rintro ⟨A,a⟩ ⟨B,b⟩ heq
    have hAB : A = B := univ_sdiff_inj A B (congrArg Prod.fst heq)
    have hab : a = b := congrArg Prod.snd heq
    subst B; subst b; rfl
  have hm : (matrixCells (fun T => H (Finset.univ \ T)) bit).image f =
      matrixCells H (!bit) := by
    ext ⟨T,r⟩
    simp only [Finset.mem_image, mem_matrixCells]
    constructor
    · rintro ⟨⟨S,s⟩,hs,heq⟩
      have hT : T = Finset.univ \ S := (congrArg Prod.fst heq).symm
      have hr : r = s := (congrArg Prod.snd heq).symm
      subst T; subst r
      cases bit <;> simpa only [mem_matrixCells, Finset.mem_sdiff,
        Finset.mem_univ, true_and, Bool.not_true, Bool.not_false,
        ↓reduceIte, not_not] using hs
    · intro ht
      refine ⟨(Finset.univ \ T,r), ?_, ?_⟩
      · cases bit <;> simpa using ht
      · simp [f]
  rw [← hm, Finset.card_image_of_injective _ hi]

/-- Support constraints with nonempty predecessor bodies retain at least half
the coordinates even after any ambient upward conditioning. -/
theorem supported_upward_average
    (body : R → Finset R) (d : R → R) (hdep : ∀ r, d r ∈ body r)
    (K : Finset R → Prop) (hK : ∀ {A B}, A ⊆ B → K A → K B) :
    by classical exact
    let H := fun S => K S ∧ ¬ dependencyHornDNF body (Finset.univ \ S)
    (Finset.univ.powerset.filter H).card * Fintype.card R ≤
      2 * ∑ S ∈ Finset.univ.powerset.filter H, S.card := by
  classical
  dsimp only
  let H := fun S => K S ∧ ¬ dependencyHornDNF body (Finset.univ \ S)
  let P := fun T => ¬ K (Finset.univ \ T)
  have hm : ∀ {A B}, A ⊆ B → P A → P B := by
    intro A B hab ha hb
    apply ha
    exact hK (by intro r hr; simp only [Finset.mem_sdiff] at hr ⊢;
                 exact ⟨hr.1, fun hra => hr.2 (hab hra)⟩) hb
  have heq : (fun T => ¬ conditionedHorn body P T) =
      (fun T => H (Finset.univ \ T)) := by
    funext T
    simp [conditionedHorn,P,H,not_or]
  have hh := conditionedHorn_false_one_le_zero body P d hdep hm
  rw [heq, matrixCells_complement_card, matrixCells_complement_card] at hh
  simp only [Bool.not_true, Bool.not_false] at hh
  have ht := matrixCells_total_card H
  rw [matrixCells_one_card] at hh ht
  change (Finset.univ.powerset.filter H).card * Fintype.card R ≤
    2 * ∑ S ∈ Finset.univ.powerset.filter H, S.card
  omega

theorem not_dependencyHorn_compl_iff (body : R → Finset R) (S : Finset R) :
    ¬ dependencyHornDNF body (Finset.univ \ S) ↔
      ∀ r ∈ S, ∃ p ∈ S, p ∈ body r := by
  classical
  constructor
  · intro h r hr
    by_contra hn
    apply h
    refine ⟨r, by simpa using hr, ?_⟩
    intro p hp
    simp only [Finset.mem_sdiff,Finset.mem_univ,true_and]
    intro hps
    exact hn ⟨p,hps,hp⟩
  · rintro h ⟨r,hr,hbody⟩
    have hrs : r ∈ S := by simpa using hr
    obtain ⟨p,hps,hpb⟩ := h r hrs
    exact (Finset.mem_sdiff.mp (hbody hpb)).2 hps

end RAF.Frankl
