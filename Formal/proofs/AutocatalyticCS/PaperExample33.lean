import proofs.AutocatalyticCS.SourceCoreSemantics

/-! The two-species extra-CS-core example following Definition 3.4. -/

namespace AutocatalyticCS.PaperExample33

open AutocatalyticCS

abbrev X := Fin 2
abbrev R := Fin 2

/-- `r0 : x0 + x1 → 2 x1`, `r1 : a + x1 → 2 x0`; the food species
`a` is external to the selected species type. -/
def network : ReactionNetwork X R where
  reactant x r :=
    if r = 0 then 1 else if x = 1 then 1 else 0
  product x r :=
    if r = 0 then (if x = 1 then 2 else 0)
    else if x = 0 then 2 else 0

/-- The two-species CS `x0 ↦ r0`, `x1 ↦ r1`. -/
def extra : IndexedMatching network where
  card := 2
  left := id
  right := id
  left_injective := Function.injective_id
  right_injective := Function.injective_id
  reactant_edge := by intro i; fin_cases i <;> decide

/-- The smaller ordinary core uses the different assignment `x1 ↦ r0`. -/
def ordinary : IndexedMatching network where
  card := 1
  left := fun _ => 1
  right := fun _ => 0
  left_injective := by intro i j _; exact Subsingleton.elim i j
  right_injective := by intro i j _; exact Subsingleton.elim i j
  reactant_edge := by intro i; fin_cases i; decide

theorem extra_edgeFinset :
    extra.edgeFinset = {(0, 0), (1, 1)} := by native_decide

theorem ordinary_edgeFinset :
    ordinary.edgeFinset = {(1, 0)} := by native_decide

theorem ordinary_underlying :
    ordinary.underlying = ({1}, {0}) := by native_decide

theorem extra_underlying :
    extra.underlying = ({0, 1}, {0, 1}) := by native_decide

theorem ordinary_underlying_lt_extra : ordinary.underlying < extra.underlying := by
  rw [ordinary_underlying, extra_underlying]
  apply lt_of_le_of_ne
  · exact ⟨by simp, by simp⟩
  · decide

theorem ordinary_edges_not_subset_extra :
    ¬ ordinary.edgeFinset ⊆ extra.edgeFinset := by
  rw [ordinary_edgeFinset, extra_edgeFinset]
  native_decide

theorem ordinary_vertexContained_extra : ordinary.VertexContained extra :=
  IndexedMatching.vertexContained_of_underlying_le
    ordinary_underlying_lt_extra.le

theorem extra_autocatalytic : extra.toChildSelection.Autocatalytic := by
  rw [IndexedMatching.toChildSelection_autocatalytic_iff]
  let v : extra.species → ℚ := fun x => if x.1 = 0 then 3 else 2
  refine ⟨v, ?_, ?_, ?_⟩
  · intro i
    dsimp [v]
    split <;> norm_num
  · intro hv
    have hzero := congrFun hv ⟨0, by native_decide⟩
    simp [v] at hzero
  · intro i
    have hiLt : i.1.val < 2 := i.1.isLt
    have hvalNat : i.1.val = 0 ∨ i.1.val = 1 := by omega
    have hval : i.1 = 0 ∨ i.1 = 1 :=
      hvalNat.imp Fin.ext Fin.ext
    rcases hval with hval | hval
    · have h : i = ⟨0, by native_decide⟩ := Subtype.ext hval
      subst i
      native_decide
    · have h : i = ⟨1, by native_decide⟩ := Subtype.ext hval
      subst i
      native_decide

theorem not_autocatalytic_of_card_one_subset_extra
    (E : IndexedMatching network) (hcard : E.card = 1)
    (hsubset : E.edgeFinset ⊆ extra.edgeFinset) :
    ¬ E.toChildSelection.Autocatalytic := by
  rw [IndexedMatching.toChildSelection_autocatalytic_iff]
  rintro ⟨v, hvnonneg, hvne, hvpos⟩
  have hspeciesCard : E.species.card = 1 := E.species_card.trans hcard
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hspeciesCard
  let x0 : E.species := ⟨x, by rw [hx]; simp⟩
  have hunique : ∀ y : E.species, y = x0 := by
    intro y
    apply Subtype.ext
    have hy : y.1 ∈ ({x} : Finset X) := by simpa [hx] using y.2
    simpa [x0] using hy
  have hedge := hsubset (E.assign_mem_edgeFinset x0)
  rw [extra_edgeFinset] at hedge
  have hedgeCases :
      (x0.1 = 0 ∧ (E.assign x0).1 = 0) ∨
      (x0.1 = 1 ∧ (E.assign x0).1 = 1) := by
    simpa [Prod.ext_iff] using hedge
  have hvx_ne : v x0 ≠ 0 := by
    intro hvx
    apply hvne
    funext y
    rw [hunique y, hvx]
    rfl
  have hvx_pos : 0 < v x0 := lt_of_le_of_ne (hvnonneg x0) (Ne.symm hvx_ne)
  have huniv : (Finset.univ : Finset E.species) = {x0} := by
    ext y
    simp [hunique y]
  have hrow := hvpos x0
  rw [Matrix.mulVec, dotProduct, huniv] at hrow
  simp only [Finset.sum_singleton] at hrow
  rcases hedgeCases with hedgeCases | hedgeCases
  · have hrow' : 0 < -v x0 := by
      rw [hedgeCases.1, hedgeCases.2] at hrow
      norm_num [network, ReactionNetwork.net] at hrow ⊢
      exact hrow
    exact (not_lt_of_ge (neg_nonpos.mpr (hvnonneg x0))) hrow'
  · have hrow' : 0 < -v x0 := by
      rw [hedgeCases.1, hedgeCases.2] at hrow
      norm_num [network, ReactionNetwork.net] at hrow ⊢
      exact hrow
    exact (not_lt_of_ge (neg_nonpos.mpr (hvnonneg x0))) hrow'

theorem extra_is_csCore : extra.IsCSCore := by
  refine ⟨extra_autocatalytic, ?_⟩
  intro edges hlt hauto
  rcases hauto with ⟨E, hEedges, hEauto⟩
  have hsubset : E.edgeFinset ⊆ extra.edgeFinset := by
    rw [hEedges]
    exact hlt.le
  have hpos := E.card_pos_of_autocatalytic hEauto
  have hle : E.card ≤ 2 := by
    calc
      E.card = E.edgeFinset.card := E.edgeFinset_card.symm
      _ ≤ extra.edgeFinset.card := Finset.card_le_card hsubset
      _ = 2 := by native_decide
  have hcard : E.card = 1 ∨ E.card = 2 := by omega
  rcases hcard with hcard | hcard
  · exact not_autocatalytic_of_card_one_subset_extra E hcard hsubset hEauto
  · have heq : E.edgeFinset = extra.edgeFinset := by
      apply Finset.eq_of_subset_of_card_le hsubset
      rw [E.edgeFinset_card, extra.edgeFinset_card, hcard]
      native_decide
    exact hlt.ne (hEedges.symm.trans heq)

theorem ordinary_autocatalytic : ordinary.toChildSelection.Autocatalytic := by
  rw [IndexedMatching.toChildSelection_autocatalytic_iff]
  let v : ordinary.species → ℚ := fun _ => 1
  refine ⟨v, ?_, ?_, ?_⟩
  · intro i
    norm_num [v]
  · intro hv
    have hzero := congrFun hv ⟨1, by native_decide⟩
    simp [v] at hzero
  · intro i
    have hiLt : i.1.val < 2 := i.1.isLt
    have hvalNat : i.1.val = 0 ∨ i.1.val = 1 := by omega
    have hval : i.1 = 0 ∨ i.1 = 1 :=
      hvalNat.imp Fin.ext Fin.ext
    rcases hval with hval | hval
    · exfalso
      have := i.2
      simp [ordinary, IndexedMatching.species, hval] at this
    · have h : i = ⟨1, by native_decide⟩ := Subtype.ext hval
      subst i
      native_decide

theorem ordinary_is_ordinaryCore : OrdinaryCore network ordinary.underlying := by
  refine ⟨ordinary.underlying_autocatalytic ordinary_autocatalytic, ?_⟩
  intro N hNlt hNauto
  rcases hNauto with ⟨E, hEN, hEauto⟩
  have hpos := E.card_pos_of_autocatalytic hEauto
  have hsupportLe : E.underlying ≤ ordinary.underlying := by
    rw [hEN]
    exact hNlt.le
  have hsle : E.species ⊆ ordinary.species := by
    exact hsupportLe.1
  have hrle : E.reactions ⊆ ordinary.reactions := by
    exact hsupportLe.2
  have hcardle : E.card ≤ 1 := by
    rw [← E.species_card]
    calc
      E.species.card ≤ ordinary.species.card := Finset.card_le_card hsle
      _ = 1 := by native_decide
  have hcard : E.card = 1 := by omega
  have hordcard : ordinary.card = 1 := rfl
  have hsEq : E.species = ordinary.species := by
    apply Finset.eq_of_subset_of_card_le hsle
    rw [ordinary.species_card, E.species_card, hordcard, hcard]
  have hrEq : E.reactions = ordinary.reactions := by
    apply Finset.eq_of_subset_of_card_le hrle
    rw [ordinary.reactions_card, E.reactions_card, hordcard, hcard]
  apply hNlt.ne
  rw [← hEN]
  exact Prod.ext hsEq hrEq

theorem ordinary_unique :
    SimpleGraph.Subgraph.IsUniqueMatching ordinary.subgraph := by
  refine ⟨ordinary.subgraph_isMatching, ?_⟩
  intro N hN hverts
  apply SimpleGraph.Subgraph.ext hverts
  funext u v
  apply propext
  constructor
  · intro huv
    have hu := N.edge_vert huv
    have hv := N.edge_vert (N.adj_symm huv)
    rw [hverts] at hu hv
    cases u with
    | inl x =>
        cases v with
        | inl y => exact (N.adj_sub huv).elim
        | inr r =>
            change x ∈ ordinary.species at hu
            change r ∈ ordinary.reactions at hv
            have hx : x = 1 := by
              simpa [ordinary, IndexedMatching.species] using hu
            have hr : r = 0 := by
              simpa [ordinary, IndexedMatching.reactions] using hv
            subst x
            subst r
            exact ⟨⟨0, by native_decide⟩, rfl, rfl⟩
    | inr r =>
        cases v with
        | inl x =>
            change r ∈ ordinary.reactions at hu
            change x ∈ ordinary.species at hv
            have hr : r = 0 := by
              simpa [ordinary, IndexedMatching.reactions] using hu
            have hx : x = 1 := by
              simpa [ordinary, IndexedMatching.species] using hv
            subst r
            subst x
            exact ⟨⟨0, by native_decide⟩, rfl, rfl⟩
        | inr s => exact (N.adj_sub huv).elim
  · intro huv
    have hu : u ∈ N.verts := by
      rw [hverts]
      exact ordinary.subgraph.edge_vert huv
    obtain ⟨w, huw, -⟩ := hN hu
    have hw := N.edge_vert (N.adj_symm huw)
    rw [hverts] at hw
    have huwQ := N.adj_sub huw
    cases u with
    | inl x =>
        cases v with
        | inl y => exact huv.elim
        | inr r =>
            rcases huv with ⟨i, hix, hir⟩
            subst x
            subst r
            cases w with
            | inl y => exact huwQ.elim
            | inr s =>
                change s ∈ ordinary.reactions at hw
                have hs : s = 0 := by
                  simpa [ordinary, IndexedMatching.reactions] using hw
                subst s
                exact huw
    | inr r =>
        cases v with
        | inl x =>
            rcases huv with ⟨i, hir, hix⟩
            subst r
            subst x
            cases w with
            | inl y =>
                change y ∈ ordinary.species at hw
                have hy : y = 1 := by
                  simpa [ordinary, IndexedMatching.species] using hw
                subst y
                exact huw
            | inr s => exact huwQ.elim
        | inr s => exact huv.elim

theorem extra_emitted_from_different_ordinary_anchor :
    extra.edgeFinset ∈ sourceCandidateEdgeFinsets network ordinary
      [0, 1] [0, 1] := by
  apply target_edgeFinset_mem_sourceCandidateEdgeFinsets
  · exact ordinary_unique
  · exact ordinary_vertexContained_extra
  · intro x
    fin_cases x <;> simp
  · intro r
    fin_cases r <;> simp

end AutocatalyticCS.PaperExample33
