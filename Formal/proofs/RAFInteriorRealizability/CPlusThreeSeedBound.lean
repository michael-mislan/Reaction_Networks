import proofs.RAFInteriorRealizability.CPlusThreeFourSubset

/-!
An empty-or-at-least-three certificate has at most three feasible singleton
seeds. Four seeds would contradict the directed-graph obstruction.
-/

namespace RAFInteriorRealizability

universe u

variable {E : Type u} [Fintype E] [DecidableEq E]

noncomputable def AntimatroidData.seeds (A : AntimatroidData E) : Finset E := by
  classical
  exact Finset.univ.filter (fun e => ({e} : Finset E) ∈ A.family)

theorem AntimatroidData.mem_seeds_iff
    (A : AntimatroidData E) (e : E) :
    e ∈ A.seeds ↔ ({e} : Finset E) ∈ A.family := by
  classical
  simp [AntimatroidData.seeds]

/-- At most three elements have feasible singletons in any certificate for
the empty-or-at-least-three family. -/
theorem cplusThree_seed_card_le_three
    (A : AntimatroidData E) (P : E → Finset E)
    (hcert : ∀ S : Finset E,
      (S = ∅ ∨ 3 ≤ S.card) ↔ S ∈ A.family ∧ PredSupported P S) :
    A.seeds.card ≤ 3 := by
  by_contra hBound
  have hFour : 4 ≤ A.seeds.card := by omega
  obtain ⟨Y, hYSubset, hYCard⟩ := Finset.exists_subset_card_eq hFour
  apply four_seed_graph_obstruction_on_subset P Y hYCard
  · intro S hSY hNe hSmall
    have hSeeds : ∀ e ∈ S, ({e} : Finset E) ∈ A.family := by
      intro e he
      exact (A.mem_seeds_iff e).mp (hYSubset (hSY he))
    have hA := A.mem_of_singletons_mem S hSeeds
    have hNotTarget : ¬ (S = ∅ ∨ 3 ≤ S.card) := by
      intro h
      rcases h with hEmpty | hLarge
      · exact hNe.ne_empty hEmpty
      · omega
    intro hSupported
    exact hNotTarget ((hcert S).mpr ⟨hA, hSupported⟩)
  · intro S _ hThree
    exact ((hcert S).mp (Or.inr (by omega))).2

/-- On a five-element ground set, every certificate must have exactly three
feasible singleton seeds. -/
theorem cplusThree_five_seed_card_eq_three
    (A : AntimatroidData E) (P : E → Finset E)
    (hcard : Fintype.card E = 5)
    (hcert : ∀ S : Finset E,
      (S = ∅ ∨ 3 ≤ S.card) ↔ S ∈ A.family ∧ PredSupported P S) :
    A.seeds.card = 3 := by
  have hAtMost := cplusThree_seed_card_le_three A P hcert
  by_contra hNotThree
  have hAtMostTwo : A.seeds.card ≤ 2 := by omega
  have hSum := Finset.card_sdiff_add_card_eq_card
    (Finset.subset_univ A.seeds)
  simp only [Finset.card_univ] at hSum
  have hComplement : 3 ≤ (Finset.univ \ A.seeds).card := by omega
  obtain ⟨T, hTSub, hTCard⟩ :=
    Finset.exists_subset_card_eq hComplement
  have hA : T ∈ A.family := ((hcert T).mp (Or.inr (by omega))).1
  have hNe : T.Nonempty := by
    apply Finset.card_pos.mp
    omega
  obtain ⟨e, heT, heSeed⟩ := A.exists_seed_in T hA hNe
  have heNotSeed : e ∉ A.seeds := (Finset.mem_sdiff.mp (hTSub heT)).2
  exact heNotSeed ((A.mem_seeds_iff e).mpr heSeed)

end RAFInteriorRealizability
