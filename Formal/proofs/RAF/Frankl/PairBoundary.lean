import proofs.RAF.Frankl.PairAvailability

namespace RAF.Frankl.PairGadget
open RAF RAFQueryCompilation PairReaction PairMolecule
open scoped Classical

variable {U : Type*} [Fintype U] [DecidableEq U]

theorem one_food (D : UnionClosedData U) : (crs D).food.card = 1 := by simp [crs]

omit [DecidableEq U] in
theorem two_reactions_per_coordinate : Fintype.card (PairReaction U) = 2 * Fintype.card U := by
  let e : PairReaction U ≃ U ⊕ U :=
    { toFun := fun r => match r with | producer i => Sum.inl i | gate i => Sum.inr i
      invFun := fun x => match x with | Sum.inl i => producer i | Sum.inr i => gate i
      left_inv := by intro r; cases r <;> rfl
      right_inv := by intro x; cases x <;> rfl }
  simpa [two_mul] using Fintype.card_congr e

omit [Fintype U] [DecidableEq U] in
theorem unique_catalyst (r : PairReaction U) : ∃! x : PairMolecule U, catalysis x r := by
  cases r with
  | producer i =>
    refine ⟨beta i,by simp [catalysis],?_⟩
    intro x hx
    cases x <;> simp_all [catalysis]
  | gate i =>
    refine ⟨alpha i,by simp [catalysis],?_⟩
    intro x hx
    cases x <;> simp_all [catalysis]

/-- Literal producer-to-target catalytic edges are precisely the two directions
of each private producer/gate pair. -/
theorem catalytic_edges (D : UnionClosedData U) (r s : PairReaction U) :
    (∃ x ∈ (crs D).outputs r, catalysis x s) ↔
      (∃ i, r = producer i ∧ s = gate i) ∨
      (∃ i, r = gate i ∧ s = producer i) := by
  constructor
  · rintro ⟨x,hx,hc⟩
    cases r <;> cases s <;> cases x <;> simp_all [crs,catalysis]
  · rintro (⟨i,rfl,rfl⟩ | ⟨i,rfl,rfl⟩)
    · exact ⟨alpha i,by simp [crs],by simp [catalysis]⟩
    · exact ⟨beta i,by simp [crs],by simp [catalysis]⟩

theorem no_self_catalysis (D : UnionClosedData U) (r : PairReaction U) :
    ¬ ∃ x ∈ (crs D).outputs r, catalysis x r := by
  rw [catalytic_edges]
  rintro (⟨i,hr,hs⟩ | ⟨i,hr,hs⟩) <;> simp_all

theorem producer_outputs_round_one (D : UnionClosedData U)
    (T : Finset (PairReaction U)) (j : U) (hj : producer j ∈ T) :
    (crs D).outputs (producer j) ⊆ closureAt (crs D) T 1 := by
  intro x hx
  change x ∈ closureStep (crs D) T (crs D).food
  simp only [closureStep,Finset.mem_union,Finset.mem_biUnion]
  exact Or.inr ⟨producer j,hj,by simpa [Enabled,crs] using hx⟩

/-- Any reactant requirement which can ever become available is already
available in round one. Gate outputs are not reactant markers. -/
theorem inputs_available_round_one (D : UnionClosedData U)
    (T : Finset (PairReaction U)) (r : PairReaction U) (k : Nat)
    (h : (crs D).inputs r ⊆ closureAt (crs D) T k) :
    (crs D).inputs r ⊆ closureAt (crs D) T 1 := by
  intro x hx
  cases r with
  | producer j =>
    have he : x = food := by simpa [crs] using hx
    subst x
    simp [closureAt,closureStep,crs]
  | gate j =>
    cases x with
    | food => simp [closureAt,closureStep,crs]
    | alpha i => simp [crs] at hx
    | beta i => simp [crs] at hx
    | marker i B =>
      obtain ⟨hb,p,hp,hpt⟩ := marker_origin D T (h hx)
      apply producer_outputs_round_one D T p hpt
      simp [crs,hb,hp]

theorem round_two_fixed (D : UnionClosedData U) (T : Finset (PairReaction U)) :
    closureStep (crs D) T (closureAt (crs D) T 2) = closureAt (crs D) T 2 := by
  apply Finset.Subset.antisymm
  · intro x hx
    simp only [closureStep,Finset.mem_union,Finset.mem_biUnion] at hx
    rcases hx with hx | ⟨r,hr,hx⟩
    · exact hx
    · by_cases he : Enabled (crs D) (closureAt (crs D) T 2) r
      · have he1 : Enabled (crs D) (closureAt (crs D) T 1) r :=
          inputs_available_round_one D T r 2 he
        rw [if_pos he] at hx
        change x ∈ closureStep (crs D) T (closureAt (crs D) T 1)
        simp only [closureStep,Finset.mem_union,Finset.mem_biUnion]
        exact Or.inr ⟨r,hr,by simpa only [if_pos he1] using hx⟩
      · simp [he] at hx
  · exact Finset.subset_union_left

/-- Uniform two-round stabilization for every availability set, not only RAFs
or encoded fixed rows. -/
theorem closure_stabilizes_after_two (D : UnionClosedData U)
    (T : Finset (PairReaction U)) (k : Nat) :
    closureAt (crs D) T (k + 2) = closureAt (crs D) T 2 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change closureStep (crs D) T (closureAt (crs D) T (k + 2)) = _
    rw [ih,round_two_fixed]

end RAF.Frankl.PairGadget
