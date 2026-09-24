import proofs.RAF.Frankl.PairStructural

namespace RAF.Frankl.UnionClosedData
open scoped Classical

variable {U : Type*} [Fintype U] [DecidableEq U]

/-- Inclusion minimality, allowing the empty blocker for inactive coordinates. -/
def IsMinimalBlocker (D : UnionClosedData U) (i : U) (B : Finset U) : Prop :=
  D.IsBlocker i B ∧ ∀ A ⊆ B, D.IsBlocker i A → A = B

noncomputable def blockers (D : UnionClosedData U) (i : U) : Finset (Finset U) :=
  Finset.univ.powerset.filter (D.IsBlocker i)

noncomputable def minimalBlockers (D : UnionClosedData U) (i : U) : Finset (Finset U) :=
  (D.blockers i).filter (D.IsMinimalBlocker i)

theorem exists_minimal_blocker_subset (D : UnionClosedData U) (i : U)
    (B : Finset U) (hB : D.IsBlocker i B) :
    ∃ A ⊆ B, D.IsMinimalBlocker i A := by
  let G := B.powerset.filter (D.IsBlocker i)
  have hn : G.Nonempty := ⟨B,by simp [G,hB]⟩
  obtain ⟨A,hA,hm⟩ := Finset.exists_min_image G Finset.card hn
  have ha : A ⊆ B ∧ D.IsBlocker i A := by simpa [G] using hA
  refine ⟨A,ha.1,ha.2,?_⟩
  intro C hCA hC
  have hCG : C ∈ G := by simp [G,hCA.trans ha.1,hC]
  exact Finset.eq_of_subset_of_card_le hCA (hm C hCG)

theorem hits_blockers_iff_hits_minimal (D : UnionClosedData U) (i : U) (S : Finset U) :
    (∀ B, D.IsBlocker i B → ¬ Disjoint S B) ↔
      (∀ B, D.IsMinimalBlocker i B → ¬ Disjoint S B) := by
  constructor
  · intro h B hb
    exact h B hb.1
  · intro h B hb hd
    obtain ⟨A,hAB,ha⟩ := D.exists_minimal_blocker_subset i B hb
    exact h A ha (hd.mono_right hAB)

/-- Exact compressed membership test for the same interior operator. -/
theorem mem_interior_iff_hits_minimal_blockers (D : UnionClosedData U)
    {i : U} {S : Finset U} (hi : i ∈ S) :
    i ∈ D.interior S ↔ ∀ B, D.IsMinimalBlocker i B → ¬ Disjoint S B := by
  rw [D.mem_interior_iff_hits_blockers hi,D.hits_blockers_iff_hits_minimal]

theorem minimal_blockers_incomparable (D : UnionClosedData U) (i : U)
    {A B : Finset U} (ha : D.IsMinimalBlocker i A) (hb : D.IsMinimalBlocker i B)
    (hAB : A ⊆ B) : A = B := hb.2 A hAB ha.1

theorem blocker_subset_erase (D : UnionClosedData U) (i : U)
    {B : Finset U} (hB : D.IsBlocker i B) : B ⊆ Finset.univ.erase i := by
  intro x hx
  exact Finset.mem_erase.mpr ⟨fun he => hB.1 (he ▸ hx),Finset.mem_univ x⟩

theorem blocker_card_bound (D : UnionClosedData U) (i : U) :
    (D.blockers i).card ≤ 2 ^ (Fintype.card U - 1) := by
  have hs : D.blockers i ⊆ (Finset.univ.erase i).powerset := by
    intro B hb
    exact Finset.mem_powerset.mpr (D.blocker_subset_erase i (Finset.mem_filter.mp hb).2)
  have hc := Finset.card_le_card hs
  simpa using hc

theorem minimal_blocker_card_le (D : UnionClosedData U) (i : U) :
    (D.minimalBlockers i).card ≤ (D.blockers i).card :=
  Finset.card_le_card (Finset.filter_subset _ _)

/-- Each retained marker has one gate-input incidence and |B| producer-output
incidences. This bounds the latter without claiming a polynomial encoding. -/
theorem marker_output_incidence_bound (D : UnionClosedData U) :
    (∑ i : U, ∑ B ∈ D.blockers i, B.card) ≤
      (Fintype.card U - 1) * ∑ i : U, (D.blockers i).card := by
  have h : ∀ i : U, (∑ B ∈ D.blockers i, B.card) ≤
      (D.blockers i).card * (Fintype.card U - 1) := by
    intro i
    have hb : ∀ B ∈ D.blockers i, B.card ≤ Fintype.card U - 1 := by
      intro B hB
      have hc := Finset.card_le_card (D.blocker_subset_erase i (Finset.mem_filter.mp hB).2)
      simpa using hc
    simpa using Finset.sum_le_sum hb
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => h i)
  rw [← Finset.sum_mul] at hs
  simpa only [Nat.mul_comm] using hs

end RAF.Frankl.UnionClosedData

namespace RAF.Frankl.PairGadget
open PairMolecule
variable {U : Type*} [Fintype U] [DecidableEq U]

omit [DecidableEq U] in
/-- The declared molecule type contains unused marker labels as well as used
ones; its exact size is exponential despite the linear reaction count. -/
theorem declared_molecule_count : Fintype.card (PairMolecule U) =
    1 + 2 * Fintype.card U + Fintype.card U * 2 ^ Fintype.card U := by
  let e : PairMolecule U ≃ Unit ⊕ (U ⊕ (U ⊕ (U × Finset U))) :=
    { toFun := fun x => match x with
        | food => Sum.inl ()
        | alpha i => Sum.inr (Sum.inl i)
        | beta i => Sum.inr (Sum.inr (Sum.inl i))
        | marker i B => Sum.inr (Sum.inr (Sum.inr (i,B)))
      invFun := fun x => match x with
        | Sum.inl _ => food
        | Sum.inr (Sum.inl i) => alpha i
        | Sum.inr (Sum.inr (Sum.inl i)) => beta i
        | Sum.inr (Sum.inr (Sum.inr (i,B))) => marker i B
      left_inv := by intro x; cases x <;> rfl
      right_inv := by
        intro x
        rcases x with u | i | i | ⟨i,B⟩
        · cases u; rfl
        · rfl
        · rfl
        · rfl }
  have h := Fintype.card_congr e
  simpa [Fintype.card_sum,Fintype.card_prod,Fintype.card_finset,two_mul,Nat.add_assoc] using h

end RAF.Frankl.PairGadget
