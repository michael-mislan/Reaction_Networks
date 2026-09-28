import proofs.RAFInteriorRealizability.CPlusThreeSeedBound

/-!
The last graph configuration in the five-element obstruction: two feasible
seed-nonseed pairs sharing a nonseed cannot coexist with support of the
corresponding triple.
-/

namespace RAFInteriorRealizability

universe u

variable {E : Type u} [DecidableEq E]

private theorem forced_incoming_from_three_cycle
    (a b c d e f x0 x1 x2 : Prop)
    (hab : a → ¬ b) (hcd : c → ¬ d) (hef : e → ¬ f)
    (h0 : a ∨ c) (h1 : b ∨ e) (h2 : d ∨ f)
    (hx0a : c ∨ x0) (hx0b : a ∨ x0)
    (hx1a : b ∨ x1) (hx1b : e ∨ x1)
    (hx2a : f ∨ x2) (hx2b : d ∨ x2) :
    x0 ∧ x1 ∧ x2 := by
  have hCycle : (a ∧ e ∧ d) ∨ (c ∧ b ∧ f) := by tauto
  rcases hCycle with hA | hB
  · have hnB := hab hA.1
    have hnC : ¬ c := by intro hc; exact (hcd hc) hA.2.2
    have hnF := hef hA.2.1
    exact ⟨hx0a.resolve_left hnC, hx1a.resolve_left hnB,
      hx2a.resolve_left hnF⟩
  · have hnA : ¬ a := by intro ha; exact (hab ha) hB.2.1
    have hnD := hcd hB.1
    have hnE : ¬ e := by intro he; exact (hef he) hB.2.2
    exact ⟨hx0b.resolve_left hnA, hx1b.resolve_left hnE,
      hx2b.resolve_left hnD⟩

private theorem three_seeds_force_incoming
    (P : Fin 5 → Finset (Fin 5)) (x : Fin 5)
    (h0 : ¬ PredSupported P {0})
    (h1 : ¬ PredSupported P {1})
    (h2 : ¬ PredSupported P {2})
    (h01 : ¬ PredSupported P {0, 1})
    (h02 : ¬ PredSupported P {0, 2})
    (h12 : ¬ PredSupported P {1, 2})
    (h012 : PredSupported P {0, 1, 2})
    (h01x : PredSupported P {0, 1, x})
    (h02x : PredSupported P {0, 2, x})
    (h12x : PredSupported P {1, 2, x}) :
    x ∈ P 0 ∧ x ∈ P 1 ∧ x ∈ P 2 := by
  simp [PredSupported] at h0 h1 h2 h01 h02 h12 h012
  simp [PredSupported] at h01x h02x h12x
  simp [h0, h1, h2] at h01 h02 h12 h012 h01x h02x h12x
  exact forced_incoming_from_three_cycle
    ((1 : Fin 5) ∈ P 0) ((0 : Fin 5) ∈ P 1)
    ((2 : Fin 5) ∈ P 0) ((0 : Fin 5) ∈ P 2)
    ((2 : Fin 5) ∈ P 1) ((1 : Fin 5) ∈ P 2)
    (x ∈ P 0) (x ∈ P 1) (x ∈ P 2)
    h01 h02 h12 h012.1 h012.2.1 h012.2.2
    h02x.1 h01x.1 h01x.2.1 h12x.1 h12x.2.1 h02x.2.1

theorem shared_nonseed_pair_obstruction
    (P : E → Finset E) (a b x : E)
    (hab : a ≠ b) (hax : a ≠ x) (hbx : b ≠ x)
    (hxa : x ∈ P a) (hxb : x ∈ P b)
    (ha : ¬ PredSupported P {a, x})
    (hb : ¬ PredSupported P {b, x})
    (htriple : PredSupported P {a, b, x}) : False := by
  have hNoAx : a ∉ P x := by
    intro haxPred
    apply ha
    intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl
    · exact ⟨x, by simp, hxa⟩
    · exact ⟨a, by simp, haxPred⟩
  have hNoBx : b ∉ P x := by
    intro hbxPred
    apply hb
    intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl
    · exact ⟨x, by simp, hxb⟩
    · exact ⟨b, by simp, hbxPred⟩
  have hNoXx : x ∉ P x := by
    intro hxx
    apply ha
    intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl
    · exact ⟨x, by simp, hxa⟩
    · exact ⟨e, by simp, hxx⟩
  obtain ⟨u, hu, hux⟩ := htriple x (by simp)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu
  rcases hu with rfl | rfl | rfl
  · exact hNoAx hux
  · exact hNoBx hux
  · exact hNoXx hux

/-- If both nonseeds point to all three seeds, one of the two nonseeds must be
chosen as an unsupported partner by two seeds; their supported triple is then
impossible. -/
theorem five_partner_pigeonhole_obstruction
    (P : Fin 5 → Finset (Fin 5))
    (h3 : ∀ a ∈ ({0, 1, 2} : Finset (Fin 5)), (3 : Fin 5) ∈ P a)
    (h4 : ∀ a ∈ ({0, 1, 2} : Finset (Fin 5)), (4 : Fin 5) ∈ P a)
    (htriple : ∀ S : Finset (Fin 5), S.card = 3 → PredSupported P S)
    (h0 : ¬ PredSupported P {0, 3} ∨ ¬ PredSupported P {0, 4})
    (h1 : ¬ PredSupported P {1, 3} ∨ ¬ PredSupported P {1, 4})
    (h2 : ¬ PredSupported P {2, 3} ∨ ¬ PredSupported P {2, 4}) :
    False := by
  rcases h0 with h03 | h04
  · rcases h1 with h13 | h14
    · exact shared_nonseed_pair_obstruction P 0 1 3
        (by decide) (by decide) (by decide)
        (h3 0 (by decide)) (h3 1 (by decide)) h03 h13
        (htriple {0, 1, 3} (by decide))
    · rcases h2 with h23 | h24
      · exact shared_nonseed_pair_obstruction P 0 2 3
          (by decide) (by decide) (by decide)
          (h3 0 (by decide)) (h3 2 (by decide)) h03 h23
          (htriple {0, 2, 3} (by decide))
      · exact shared_nonseed_pair_obstruction P 1 2 4
          (by decide) (by decide) (by decide)
          (h4 1 (by decide)) (h4 2 (by decide)) h14 h24
          (htriple {1, 2, 4} (by decide))
  · rcases h1 with h13 | h14
    · rcases h2 with h23 | h24
      · exact shared_nonseed_pair_obstruction P 1 2 3
          (by decide) (by decide) (by decide)
          (h3 1 (by decide)) (h3 2 (by decide)) h13 h23
          (htriple {1, 2, 3} (by decide))
      · exact shared_nonseed_pair_obstruction P 0 2 4
          (by decide) (by decide) (by decide)
          (h4 0 (by decide)) (h4 2 (by decide)) h04 h24
          (htriple {0, 2, 4} (by decide))
    · exact shared_nonseed_pair_obstruction P 0 1 4
        (by decide) (by decide) (by decide)
        (h4 0 (by decide)) (h4 1 (by decide)) h04 h14
        (htriple {0, 1, 4} (by decide))

/-- The graph portion of the five-element obstruction, after accessibility
has selected one feasible seed-nonseed pair for each seed. -/
theorem five_seed_graph_obstruction
    (P : Fin 5 → Finset (Fin 5))
    (hsmall : ∀ S : Finset (Fin 5),
      S ⊆ ({0, 1, 2} : Finset (Fin 5)) →
      S.Nonempty → S.card < 3 → ¬ PredSupported P S)
    (htriple : ∀ S : Finset (Fin 5), S.card = 3 → PredSupported P S)
    (h0 : ¬ PredSupported P {0, 3} ∨ ¬ PredSupported P {0, 4})
    (h1 : ¬ PredSupported P {1, 3} ∨ ¬ PredSupported P {1, 4})
    (h2 : ¬ PredSupported P {2, 3} ∨ ¬ PredSupported P {2, 4}) :
    False := by
  have hSeed0 := hsmall {0} (by decide) (by decide) (by decide)
  have hSeed1 := hsmall {1} (by decide) (by decide) (by decide)
  have hSeed2 := hsmall {2} (by decide) (by decide) (by decide)
  have hSeed01 := hsmall {0, 1} (by decide) (by decide) (by decide)
  have hSeed02 := hsmall {0, 2} (by decide) (by decide) (by decide)
  have hSeed12 := hsmall {1, 2} (by decide) (by decide) (by decide)
  have incoming (x : Fin 5)
      (h01x : ({0, 1, x} : Finset (Fin 5)).card = 3)
      (h02x : ({0, 2, x} : Finset (Fin 5)).card = 3)
      (h12x : ({1, 2, x} : Finset (Fin 5)).card = 3) :=
    three_seeds_force_incoming P x
      hSeed0 hSeed1 hSeed2 hSeed01 hSeed02 hSeed12
      (htriple {0, 1, 2} (by decide))
      (htriple {0, 1, x} h01x)
      (htriple {0, 2, x} h02x)
      (htriple {1, 2, x} h12x)
  have h3 := incoming 3 (by decide) (by decide) (by decide)
  have h4 := incoming 4 (by decide) (by decide) (by decide)
  have h3Seeds : ∀ a ∈ ({0, 1, 2} : Finset (Fin 5)), (3 : Fin 5) ∈ P a := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl
    · exact h3.1
    · exact h3.2.1
    · exact h3.2.2
  have h4Seeds : ∀ a ∈ ({0, 1, 2} : Finset (Fin 5)), (4 : Fin 5) ∈ P a := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl
    · exact h4.1
    · exact h4.2.1
    · exact h4.2.2
  exact five_partner_pigeonhole_obstruction P h3Seeds h4Seeds htriple h0 h1 h2

/-- Accessibility of a feasible seed-nonseed-nonseed triple supplies one
feasible pair containing the seed. The other pair has no seed. -/
theorem antimatroid_partner_choice
    (A : AntimatroidData E) (P : E → Finset E)
    (a x y : E) (hax : a ≠ x) (hay : a ≠ y) (hxy : x ≠ y)
    (hx : ({x} : Finset E) ∉ A.family)
    (hy : ({y} : Finset E) ∉ A.family)
    (hA : ({a, x, y} : Finset E) ∈ A.family)
    (hSmall : ∀ S : Finset E, S.Nonempty → S.card < 3 →
      S ∈ A.family → ¬ PredSupported P S) :
    ¬ PredSupported P {a, x} ∨ ¬ PredSupported P {a, y} := by
  obtain ⟨e, he, hErase⟩ := A.accessible hA (by simp)
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl
  · have hXY : ({x, y} : Finset E) ∈ A.family := by
      simpa [hax, hay] using hErase
    obtain ⟨s, hs, hSeed⟩ := A.exists_seed_in {x, y} hXY (by simp)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl
    · exact False.elim (hx hSeed)
    · exact False.elim (hy hSeed)
  · right
    have hAY : ({a, y} : Finset E) ∈ A.family := by
      simpa [Finset.erase_insert_of_ne hax, hxy] using hErase
    exact hSmall {a, y} (by simp) (by simp [hay]) hAY
  · left
    have hAX : ({a, x} : Finset E) ∈ A.family := by
      simpa [Finset.erase_insert_of_ne hay,
        Finset.erase_insert_of_ne hxy] using hErase
    exact hSmall {a, x} (by simp) (by simp [hax]) hAX

/-- No five-element certificate can have the first three vertices as exactly
its singleton seeds. -/
theorem cplusThree_fin5_obstruction_fixed_seeds
    (A : AntimatroidData (Fin 5)) (P : Fin 5 → Finset (Fin 5))
    (hSeeds : A.seeds = {0, 1, 2})
    (hcert : ∀ S : Finset (Fin 5),
      (S = ∅ ∨ 3 ≤ S.card) ↔ S ∈ A.family ∧ PredSupported P S) :
    False := by
  have hSmall : ∀ S : Finset (Fin 5), S.Nonempty → S.card < 3 →
      S ∈ A.family → ¬ PredSupported P S := by
    intro S hNe hCard hA hSupp
    have hTarget := (hcert S).mpr ⟨hA, hSupp⟩
    rcases hTarget with hEmpty | hLarge
    · exact hNe.ne_empty hEmpty
    · omega
  have hNo3 : ({3} : Finset (Fin 5)) ∉ A.family := by
    intro h
    have hNot : (3 : Fin 5) ∉ A.seeds := by simp [hSeeds]
    exact hNot ((A.mem_seeds_iff 3).mpr h)
  have hNo4 : ({4} : Finset (Fin 5)) ∉ A.family := by
    intro h
    have hNot : (4 : Fin 5) ∉ A.seeds := by simp [hSeeds]
    exact hNot ((A.mem_seeds_iff 4).mpr h)
  have hTriple : ∀ S : Finset (Fin 5), S.card = 3 → PredSupported P S := by
    intro S hCard
    exact ((hcert S).mp (Or.inr (by omega))).2
  have hChoice0 : ¬ PredSupported P {0, 3} ∨ ¬ PredSupported P {0, 4} := by
    apply antimatroid_partner_choice A P 0 3 4
      (by decide) (by decide) (by decide) hNo3 hNo4
    · exact ((hcert {0, 3, 4}).mp (Or.inr (by decide))).1
    · exact hSmall
  have hChoice1 : ¬ PredSupported P {1, 3} ∨ ¬ PredSupported P {1, 4} := by
    apply antimatroid_partner_choice A P 1 3 4
      (by decide) (by decide) (by decide) hNo3 hNo4
    · exact ((hcert {1, 3, 4}).mp (Or.inr (by decide))).1
    · exact hSmall
  have hChoice2 : ¬ PredSupported P {2, 3} ∨ ¬ PredSupported P {2, 4} := by
    apply antimatroid_partner_choice A P 2 3 4
      (by decide) (by decide) (by decide) hNo3 hNo4
    · exact ((hcert {2, 3, 4}).mp (Or.inr (by decide))).1
    · exact hSmall
  apply five_seed_graph_obstruction P ?_ hTriple hChoice0 hChoice1 hChoice2
  intro S hSubset hNe hCard
  have hFeasible : S ∈ A.family := by
    apply A.mem_of_singletons_mem S
    intro e he
    apply (A.mem_seeds_iff e).mp
    rw [hSeeds]
    exact hSubset he
  exact hSmall S hNe hCard hFeasible

/-- No food-support certificate realizes the empty-or-at-least-three family
on a five-element ground set. -/
theorem cplusThree_fin5_certificate_impossible
    (A : AntimatroidData (Fin 5)) (P : Fin 5 → Finset (Fin 5))
    (hcert : ∀ S : Finset (Fin 5),
      (S = ∅ ∨ 3 ≤ S.card) ↔ S ∈ A.family ∧ PredSupported P S) :
    False := by
  have hSeedCard : A.seeds.card = 3 :=
    cplusThree_five_seed_card_eq_three A P (by decide) hcert
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_map_finset_eq A.seeds
    ({0, 1, 2} : Finset (Fin 5)) (by simpa using hSeedCard)
  have hPullSeeds : (A.pullback σ.symm).seeds = {0, 1, 2} := by
    ext i
    rw [AntimatroidData.mem_seeds_iff,
      AntimatroidData.mem_pullback_iff]
    simp only [Finset.image_singleton]
    rw [← A.mem_seeds_iff]
    rw [← Finset.mem_map_equiv (f := σ)]
    rw [hσ]
  exact cplusThree_fin5_obstruction_fixed_seeds
    (A.pullback σ.symm) (pullbackPredecessors P σ.symm)
    hPullSeeds
    (cplusThree_certificate_pullback A P σ.symm hcert)

/-- The five-element obstruction is independent of vertex labels. -/
theorem cplusThree_card_five_certificate_impossible
    [Fintype E] (hcard : Fintype.card E = 5)
    (A : AntimatroidData E) (P : E → Finset E)
    (hcert : ∀ S : Finset E,
      (S = ∅ ∨ 3 ≤ S.card) ↔ S ∈ A.family ∧ PredSupported P S) :
    False := by
  let e : Fin 5 ≃ E := (Fintype.equivFinOfCardEq hcard).symm
  exact cplusThree_fin5_certificate_impossible
    (A.pullback e) (pullbackPredecessors P e)
    (cplusThree_certificate_pullback A P e hcert)

/-- The upper bound for same-ground realizability: any larger ground set
restricts to a forbidden five-element certificate. -/
theorem cplusThree_realizable_card_le_four
    [Fintype E]
    (hReal : SameGroundRAFRealizable (cplusThreeOperator E)) :
    Fintype.card E ≤ 4 := by
  by_contra hBound
  have hFive : 5 ≤ (Finset.univ : Finset E).card := by
    simp only [Finset.card_univ]
    omega
  obtain ⟨Y, _, hYCard⟩ := Finset.exists_subset_card_eq hFive
  obtain ⟨A, P, hCertificate⟩ :=
    (rafInteriorOperator_realizable_iff (cplusThreeOperator E)).mp hReal
  have hCert : ∀ S : Finset E,
      (S = ∅ ∨ 3 ≤ S.card) ↔ S ∈ A.family ∧ PredSupported P S := by
    intro S
    exact (mem_cplusThreeOperator S).symm.trans (hCertificate S)
  have hSubtype : Fintype.card {e // e ∈ Y} = 5 := by simpa using hYCard
  exact cplusThree_card_five_certificate_impossible hSubtype
    (A.restrict Y) (restrictPredecessors P Y)
    (cplusThree_certificate_restrict A P Y hCert)

/-- Sharp threshold for the empty-or-at-least-three fixed family. -/
theorem cplusThree_realizable_iff_card_le_four
    [Fintype E] :
    SameGroundRAFRealizable (cplusThreeOperator E) ↔
      Fintype.card E ≤ 4 :=
  ⟨cplusThree_realizable_card_le_four,
    cplusThree_card_le_four_realizable⟩

end RAFInteriorRealizability
