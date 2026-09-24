import proofs.IrrRAFEnumeration.HybridCharge

namespace IrrRAFEnumeration

/-- The abstract code space of a root, a first cover choice, or an ordered
pair of cover choices.  The alternating binary construction realizes this
shape in the numerical pre-flight. -/
inductive TwoStageCode (α : Type*) where
  | root
  | first (a : α)
  | second (a b : α)

deriving DecidableEq, Fintype

theorem twoStageCode_card (α : Type*) [Fintype α] :
    Fintype.card (TwoStageCode α) =
      1 + Fintype.card α + Fintype.card α * Fintype.card α := by
  classical
  let equivalence : TwoStageCode α ≃ Unit ⊕ α ⊕ (α × α) :=
    { toFun := fun code =>
        match code with
        | .root => Sum.inl ()
        | .first a => Sum.inr (Sum.inl a)
        | .second a b => Sum.inr (Sum.inr (a, b))
      invFun := fun code =>
        match code with
        | .inl _ => .root
        | .inr (.inl a) => .first a
        | .inr (.inr (a, b)) => .second a b
      left_inv := by intro code; cases code <;> rfl
      right_inv := by
        intro code
        rcases code with _ | code
        · rfl
        · rcases code with _ | _ <;> rfl }
  rw [Fintype.card_congr equivalence]
  simp [Nat.add_assoc]

/-- Exact arithmetic obstruction to the attempted linear root-charge proof.
The certified alternating family has 7,168 choices at each of two stages,
whereas its proposed `1 + n|F||G|` budget is 50,331,649. -/
theorem selectorAlternating_twoStage_exceeds_linearCharge :
    50331649 < Fintype.card (TwoStageCode (Fin 7168)) := by
  rw [twoStageCode_card]
  norm_num

theorem selectorAlternating_twoStage_card :
    Fintype.card (TwoStageCode (Fin 7168)) = 51387393 := by
  rw [twoStageCode_card]
  norm_num

/-- Abstract state codes for a recursion that makes at most `r` independent
choices from a `c`-element cover. -/
abbrev MultiStageCode (r c : Nat) :=
  Fin (∑ i ∈ Finset.range (r + 1), c ^ i)

theorem multiStageCode_card (r c : Nat) :
    Fintype.card (MultiStageCode r c) =
      ∑ i ∈ Finset.range (r + 1), c ^ i := by
  simp [MultiStageCode]

theorem coverChoicePow_le_multiStageCode_card (r c : Nat) :
    c ^ r ≤ Fintype.card (MultiStageCode r c) := by
  rw [multiStageCode_card]
  exact Finset.single_le_sum
    (fun i _hi => Nat.zero_le (c ^ i))
    (Finset.mem_range.mpr (Nat.lt_succ_self r))

/-- Exact arithmetic target certified by the three-copy descriptor census. -/
theorem selectorThreeCopy_multiStage_card :
    Fintype.card (MultiStageCode 3 224) = 11289825 := by
  rw [multiStageCode_card]
  norm_num

end IrrRAFEnumeration
