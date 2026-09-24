import proofs.RAF.Frankl.Antimatroid
import proofs.RAF.Frankl.DependencyHorn
import proofs.RAF.Frankl.Toggle

namespace RAF.Frankl

open RAF

variable {M R : Type*} [DecidableEq M]

/-- Every reaction is enabled directly from food. -/
def Elementary (Q : CRS M R) : Prop := ∀ r, SeedReaction Q r

theorem elementary_foodGenerated (Q : CRS M R) [DecidableEq R]
    (hE : Elementary Q) (S : Finset R) : FoodGenerated Q S := by
  intro r _
  exact ⟨0, hE r⟩

/-- Product predecessors of a reaction in the catalysis digraph. -/
noncomputable def productPredecessors (Q : CRS M R) (C : Catalysis M R)
    [Fintype R] (r : R) : Finset R := by
  classical
  exact Finset.univ.filter fun u => ∃ x ∈ Q.outputs u, C x r

@[simp] theorem mem_productPredecessors (Q : CRS M R) (C : Catalysis M R)
    [Fintype R] (u r : R) :
    u ∈ productPredecessors Q C r ↔ ∃ x ∈ Q.outputs u, C x r := by
  classical
  simp [productPredecessors]

/-- Food-catalyzed heads receive the impossible body `{r}`; all other heads
receive their product predecessors.  Thus every actual term describes exactly
one way in which a retained reaction can lack a catalyst. -/
noncomputable def elementaryHornBody (Q : CRS M R) (C : Catalysis M R)
    [Fintype R] (r : R) : Finset R := by
  classical
  exact if ∃ x ∈ Q.food, C x r then {r} else productPredecessors Q C r

theorem elementaryHornBody_nonempty (Q : CRS M R) (C : Catalysis M R)
    [Fintype R] [DecidableEq R]
    (hne : (rafFamily Q C).Nonempty)
    (hactive : maxRAF Q C = Finset.univ) (r : R) :
    (elementaryHornBody Q C r).Nonempty := by
  classical
  by_cases hfood : ∃ x ∈ Q.food, C x r
  · simp [elementaryHornBody, hfood]
  · have hmax : IsRAF Q C (maxRAF Q C) := isRAF_maxRAF Q C hne
    have hgraph : ProductGraphCatalyzed Q C (maxRAF Q C) :=
      (isRAF_iff_foodGenerated_and_productGraph Q C (maxRAF Q C)).mp hmax |>.2.2
    have hr : r ∈ maxRAF Q C := by rw [hactive]; simp
    rcases hgraph r hr with hfood' | ⟨u, hu, x, hx, hcat⟩
    · exact (hfood hfood').elim
    · refine ⟨u, ?_⟩
      rw [elementaryHornBody, if_neg hfood,
        mem_productPredecessors]
      exact ⟨x, hx, hcat⟩

theorem elementary_false_iff_empty_or_isRAF
    (Q : CRS M R) (C : Catalysis M R) [Fintype R] [DecidableEq R]
    (hE : Elementary Q) (T : Finset R) :
    ¬ dependencyHornDNF (elementaryHornBody Q C) T ↔
      Finset.univ \ T = ∅ ∨ IsRAF Q C (Finset.univ \ T) := by
  classical
  let S : Finset R := Finset.univ \ T
  constructor
  · intro hfalse
    by_cases hS : S = ∅
    · exact Or.inl hS
    · apply Or.inr
      rw [isRAF_iff_foodGenerated_and_productGraph]
      refine ⟨Finset.nonempty_iff_ne_empty.mpr hS,
        elementary_foodGenerated Q hE S, ?_⟩
      intro r hrS
      by_cases hfood : ∃ x ∈ Q.food, C x r
      · exact Or.inl hfood
      · apply Or.inr
        by_contra hnopred
        push Not at hnopred
        apply hfalse
        refine ⟨r, ?_, ?_⟩
        · simpa [S] using hrS
        · intro u hu
          have hpred : ∃ x ∈ Q.outputs u, C x r := by
            simpa [elementaryHornBody, hfood] using hu
          by_contra huT
          have huS : u ∈ S := by simp [S, huT]
          obtain ⟨x, hx, hcat⟩ := hpred
          exact hnopred u huS x hx hcat
  · rintro (hS | hraf) hdnf
    · obtain ⟨r, hrT, _⟩ := hdnf
      have hrS : r ∈ S := by simp [S, hrT]
      have hrS' : r ∈ Finset.univ \ T := hrS
      rw [hS] at hrS'
      simp at hrS'
    · obtain ⟨r, hrT, hbody⟩ := hdnf
      have hrS : r ∈ S := by simp [S, hrT]
      have hgraph : ProductGraphCatalyzed Q C S :=
        (isRAF_iff_foodGenerated_and_productGraph Q C S).mp hraf |>.2.2
      rcases hgraph r hrS with hfood | ⟨u, huS, x, hx, hcat⟩
      · have hrr : r ∈ elementaryHornBody Q C r := by
          simp [elementaryHornBody, hfood]
        exact hrT (hbody hrr)
      · have hnofood : ¬ ∃ y ∈ Q.food, C y r := by
          intro hy
          have hrr : r ∈ elementaryHornBody Q C r := by
            simp [elementaryHornBody, hy]
          exact hrT (hbody hrr)
        have huBody : u ∈ elementaryHornBody Q C r := by
          rw [elementaryHornBody, if_neg hnofood,
            mem_productPredecessors]
          exact ⟨x, hx, hcat⟩
        have huT : u ∈ T := hbody huBody
        have huNotT : u ∉ T := by simpa [S] using huS
        exact huNotT huT

theorem elementaryHornComplementFamily_eq_fixedFamily
    (Q : CRS M R) (C : Catalysis M R) [Fintype R] [DecidableEq R]
    (hE : Elementary Q) :
    dependencyHornComplementFamily (elementaryHornBody Q C) =
      fixedFamily Q C := by
  classical
  ext S
  simp only [dependencyHornComplementFamily, Finset.mem_image,
    mem_dependencyHornFalseFamily, mem_fixedFamily]
  constructor
  · rintro ⟨T, hfalse, rfl⟩
    exact (elementary_false_iff_empty_or_isRAF Q C hE T).mp hfalse
  · intro hfixed
    refine ⟨Finset.univ \ S, ?_, ?_⟩
    · rw [elementary_false_iff_empty_or_isRAF Q C hE]
      simpa using hfixed
    · ext r
      simp

/-- The normalized elementary case of Steel's stronger fixed-family target. -/
theorem elementary_normalized_rafFixedFrankl
    (Q : CRS M R) (C : Catalysis M R) [Fintype R] [DecidableEq R]
    (hE : Elementary Q) (hactive : maxRAF Q C = Finset.univ) :
    RAFFixedFrankl Q C := by
  classical
  intro hne
  let d : R → R := fun r =>
    Classical.choose (elementaryHornBody_nonempty Q C hne hactive r)
  have hdep : ∀ r, d r ∈ elementaryHornBody Q C r := fun r =>
    Classical.choose_spec (elementaryHornBody_nonempty Q C hne hactive r)
  have hR : Nonempty R := by
    obtain ⟨S, hS⟩ := hne
    obtain ⟨r, _⟩ := ((mem_rafFamily Q C S).mp hS).1
    exact ⟨r⟩
  letI : Nonempty R := hR
  obtain ⟨r, hr⟩ :=
    dependencyHornComplementFamily_exists_abundant
      (elementaryHornBody Q C) d hdep
  refine ⟨r, ?_⟩
  rw [elementaryHornComplementFamily_eq_fixedFamily Q C hE] at hr
  have hcard : (fixedFamily Q C).card = (rafFamily Q C).card + 1 := by
    have hempty : (∅ : Finset R) ∉ rafFamily Q C := by
      rw [mem_rafFamily]
      intro h
      simpa using h.1
    simp [fixedFamily, hempty]
  have hfreq :
      ((fixedFamily Q C).filter fun S => r ∈ S).card = frequency Q C r := by
    rw [frequency]
    congr 1
    ext S
    simp [fixedFamily]
    aesop
  rwa [hcard, hfreq] at hr

/-- Restrict a CRS to a finite set of reactions. -/
def restrictCRS (Q : CRS M R) (A : Finset R) : CRS M {r // r ∈ A} where
  inputs r := Q.inputs r.1
  outputs r := Q.outputs r.1
  food := Q.food

def restrictCatalysis (C : Catalysis M R) (A : Finset R) :
    Catalysis M {r // r ∈ A} := fun x r => C x r.1

noncomputable def toRestricted (A S : Finset R) : Finset {r // r ∈ A} := by
  classical
  exact Finset.univ.filter fun r => r.1 ∈ S

noncomputable def fromRestricted {A : Finset R}
    (U : Finset {r // r ∈ A}) : Finset R := by
  classical
  exact U.map ⟨Subtype.val, Subtype.val_injective⟩

@[simp] theorem mem_toRestricted [Fintype R] [DecidableEq R]
    (A S : Finset R) (r : {r // r ∈ A}) :
    r ∈ toRestricted A S ↔ r.1 ∈ S := by
  classical
  simp [toRestricted]

@[simp] theorem mem_fromRestricted [DecidableEq R] {A : Finset R}
    (U : Finset {r // r ∈ A}) (r : R) :
    r ∈ fromRestricted U ↔ ∃ h : r ∈ A, (⟨r, h⟩ : {r // r ∈ A}) ∈ U := by
  classical
  simp [fromRestricted]

theorem from_toRestricted [Fintype R] [DecidableEq R]
    {A S : Finset R} (hSA : S ⊆ A) :
    fromRestricted (toRestricted A S) = S := by
  classical
  ext r
  constructor
  · simp only [mem_fromRestricted, mem_toRestricted]
    rintro ⟨_, hr⟩
    exact hr
  · intro hr
    exact (mem_fromRestricted (toRestricted A S) r).2 ⟨hSA hr, by simpa⟩

theorem to_fromRestricted [Fintype R] [DecidableEq R]
    {A : Finset R} (U : Finset {r // r ∈ A}) :
    toRestricted A (fromRestricted U) = U := by
  classical
  ext r
  simp

theorem elementary_restrict (Q : CRS M R) [DecidableEq R]
    (A : Finset R) (hE : Elementary Q) : Elementary (restrictCRS Q A) := by
  intro r
  exact hE r.1

theorem productGraph_restrict_iff (Q : CRS M R) (C : Catalysis M R)
    [Fintype R] [DecidableEq R] (A : Finset R)
    (U : Finset {r // r ∈ A}) :
    ProductGraphCatalyzed (restrictCRS Q A) (restrictCatalysis C A) U ↔
      ProductGraphCatalyzed Q C (fromRestricted U) := by
  classical
  constructor
  · intro h r hr
    obtain ⟨hrA, hrU⟩ := (mem_fromRestricted U r).mp hr
    rcases h ⟨r, hrA⟩ hrU with hfood | ⟨u, hu, x, hx, hcat⟩
    · exact Or.inl hfood
    · exact Or.inr ⟨u.1, (mem_fromRestricted U u.1).2 ⟨u.2, hu⟩,
        x, hx, hcat⟩
  · intro h r hr
    rcases h r.1 ((mem_fromRestricted U r.1).2 ⟨r.2, hr⟩) with
        hfood | ⟨u, hu, x, hx, hcat⟩
    · exact Or.inl hfood
    · obtain ⟨huA, huU⟩ := (mem_fromRestricted U u).mp hu
      exact Or.inr ⟨⟨u, huA⟩, huU, x, hx, hcat⟩

theorem elementary_isRAF_restrict_iff
    (Q : CRS M R) (C : Catalysis M R) [Fintype R] [DecidableEq R]
    (A : Finset R) (hE : Elementary Q) (U : Finset {r // r ∈ A}) :
    IsRAF (restrictCRS Q A) (restrictCatalysis C A) U ↔
      IsRAF Q C (fromRestricted U) := by
  classical
  rw [isRAF_iff_foodGenerated_and_productGraph,
    isRAF_iff_foodGenerated_and_productGraph]
  have hnonempty : U.Nonempty ↔ (fromRestricted U).Nonempty := by
    simp [Finset.nonempty_iff_ne_empty, fromRestricted]
  constructor
  · rintro ⟨hne, _, hgraph⟩
    exact ⟨hnonempty.mp hne, elementary_foodGenerated Q hE _,
      (productGraph_restrict_iff Q C A U).mp hgraph⟩
  · rintro ⟨hne, _, hgraph⟩
    exact ⟨hnonempty.mpr hne,
      elementary_foodGenerated (restrictCRS Q A)
        (elementary_restrict Q A hE) U,
      (productGraph_restrict_iff Q C A U).mpr hgraph⟩

theorem elementary_isRAF_toRestricted_iff
    (Q : CRS M R) (C : Catalysis M R) [Fintype R] [DecidableEq R]
    (A : Finset R) (hE : Elementary Q) {S : Finset R} (hSA : S ⊆ A) :
    IsRAF (restrictCRS Q A) (restrictCatalysis C A) (toRestricted A S) ↔
      IsRAF Q C S := by
  rw [elementary_isRAF_restrict_iff Q C A hE,
    from_toRestricted hSA]

theorem elementary_rafFamily_restrict_eq_image
    (Q : CRS M R) (C : Catalysis M R) [Fintype R] [DecidableEq R]
    (A : Finset R) (hE : Elementary Q)
    (hAll : ∀ {S : Finset R}, IsRAF Q C S → S ⊆ A) :
    rafFamily (restrictCRS Q A) (restrictCatalysis C A) =
      (rafFamily Q C).image (toRestricted A) := by
  classical
  ext U
  simp only [mem_rafFamily, Finset.mem_image]
  constructor
  · intro hU
    refine ⟨fromRestricted U,
      (elementary_isRAF_restrict_iff Q C A hE U).mp hU, ?_⟩
    exact to_fromRestricted U
  · rintro ⟨S, hS, rfl⟩
    exact (elementary_isRAF_toRestricted_iff Q C A hE (hAll hS)).mpr hS

theorem elementary_rafFamily_restrict_card
    (Q : CRS M R) (C : Catalysis M R) [Fintype R] [DecidableEq R]
    (A : Finset R) (hE : Elementary Q)
    (hAll : ∀ {S : Finset R}, IsRAF Q C S → S ⊆ A) :
    (rafFamily (restrictCRS Q A) (restrictCatalysis C A)).card =
      (rafFamily Q C).card := by
  classical
  rw [elementary_rafFamily_restrict_eq_image Q C A hE hAll]
  apply Finset.card_image_iff.mpr
  intro S hS T hT hEq
  have hEq' := congrArg fromRestricted hEq
  rw [from_toRestricted (hAll ((mem_rafFamily Q C S).mp hS)),
    from_toRestricted (hAll ((mem_rafFamily Q C T).mp hT))] at hEq'
  exact hEq'

theorem elementary_frequency_restrict
    (Q : CRS M R) (C : Catalysis M R) [Fintype R] [DecidableEq R]
    (A : Finset R) (hE : Elementary Q)
    (hAll : ∀ {S : Finset R}, IsRAF Q C S → S ⊆ A)
    (r : {r // r ∈ A}) :
    frequency (restrictCRS Q A) (restrictCatalysis C A) r =
      frequency Q C r.1 := by
  classical
  rw [frequency_eq_filter_card, frequency_eq_filter_card]
  have heq :
      (rafFamily (restrictCRS Q A) (restrictCatalysis C A)).filter
          (fun U => r ∈ U) =
        ((rafFamily Q C).filter fun S => r.1 ∈ S).image (toRestricted A) := by
    ext U
    simp only [Finset.mem_filter, mem_rafFamily, Finset.mem_image]
    constructor
    · rintro ⟨hU, hrU⟩
      refine ⟨fromRestricted U,
        ⟨(elementary_isRAF_restrict_iff Q C A hE U).mp hU, ?_⟩, ?_⟩
      · exact (mem_fromRestricted U r.1).2 ⟨r.2, hrU⟩
      · exact to_fromRestricted U
    · rintro ⟨S, ⟨hS, hrS⟩, rfl⟩
      exact ⟨(elementary_isRAF_toRestricted_iff Q C A hE (hAll hS)).mpr hS,
        by simpa⟩
  have hcardImage :
      (((rafFamily Q C).filter fun S => r.1 ∈ S).image
          (toRestricted A)).card =
        ((rafFamily Q C).filter fun S => r.1 ∈ S).card := by
    apply Finset.card_image_iff.mpr
    intro S hS T hT hEq
    have hpairS : IsRAF Q C S ∧ r.1 ∈ S := by simpa using hS
    have hpairT : IsRAF Q C T ∧ r.1 ∈ T := by simpa using hT
    have hrafS : IsRAF Q C S := hpairS.1
    have hrafT : IsRAF Q C T := hpairT.1
    have hEq' := congrArg fromRestricted hEq
    rw [from_toRestricted (hAll hrafS),
      from_toRestricted (hAll hrafT)] at hEq'
    exact hEq'
  have hcardEq := congrArg Finset.card heq
  have hfirst :
      ((rafFamily (restrictCRS Q A) (restrictCatalysis C A)).filter
          fun U => r ∈ U).card =
        (((rafFamily Q C).filter fun S => r.1 ∈ S).image
          (toRestricted A)).card := by
    exact hcardEq
  exact hfirst.trans hcardImage

theorem elementary_restricted_maxRAF_eq_univ
    (Q : CRS M R) (C : Catalysis M R) [Fintype R] [DecidableEq R]
    (hE : Elementary Q) :
    maxRAF (restrictCRS Q (maxRAF Q C))
        (restrictCatalysis C (maxRAF Q C)) = Finset.univ := by
  classical
  apply Finset.eq_univ_of_forall
  intro r
  have hr := r.2
  simp only [maxRAF, Finset.mem_biUnion] at hr
  obtain ⟨S, hSF, hrS⟩ := hr
  have hS : IsRAF Q C S := (mem_rafFamily Q C S).mp hSF
  have hsub : S ⊆ maxRAF Q C := subset_maxRAF_of_isRAF Q C hS
  have hrestricted :
      IsRAF (restrictCRS Q (maxRAF Q C))
        (restrictCatalysis C (maxRAF Q C))
        (toRestricted (maxRAF Q C) S) :=
    (elementary_isRAF_toRestricted_iff Q C (maxRAF Q C) hE hsub).mpr hS
  exact subset_maxRAF_of_isRAF _ _ hrestricted (by simpa using hrS)

/-- Every finite elementary CRS satisfies the stronger fixed-family form of
Steel's conjecture, without assuming that ambient reactions are active. -/
theorem elementary_rafFixedFrankl
    (Q : CRS M R) (C : Catalysis M R) [Fintype R] [DecidableEq R]
    (hE : Elementary Q) : RAFFixedFrankl Q C := by
  classical
  intro hne
  let A := maxRAF Q C
  let Q' := restrictCRS Q A
  let C' := restrictCatalysis C A
  have hAll : ∀ {S : Finset R}, IsRAF Q C S → S ⊆ A := by
    intro S hS
    exact subset_maxRAF_of_isRAF Q C hS
  have hne' : (rafFamily Q' C').Nonempty := by
    obtain ⟨S, hSF⟩ := hne
    refine ⟨toRestricted A S, ?_⟩
    rw [mem_rafFamily]
    exact (elementary_isRAF_toRestricted_iff Q C A hE
      (hAll ((mem_rafFamily Q C S).mp hSF))).mpr
        ((mem_rafFamily Q C S).mp hSF)
  have hactive : maxRAF Q' C' = Finset.univ := by
    exact elementary_restricted_maxRAF_eq_univ Q C hE
  obtain ⟨r, hr⟩ :=
    elementary_normalized_rafFixedFrankl Q' C'
      (elementary_restrict Q A hE) hactive hne'
  refine ⟨r.1, ?_⟩
  rw [elementary_rafFamily_restrict_card Q C A hE hAll,
    elementary_frequency_restrict Q C A hE hAll r] at hr
  exact hr

end RAF.Frankl
