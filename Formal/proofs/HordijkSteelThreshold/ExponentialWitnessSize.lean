import proofs.HordijkSteelThreshold.SeededBulkCritical

namespace HordijkSteelThreshold

open RAF RAF.Polymer RAF.Concrete

/-- Molecules incident with a finite reversible reaction set. -/
def revReactionSupport {M R : Type*} [DecidableEq M] [DecidableEq R]
    (Q : ReversibleCRS M R) (S : Finset R) : Finset M :=
  S.biUnion fun r => Q.lhs r ∪ Q.rhs r

/-- Reversible closure cannot create a molecule outside food or the literal
reaction support. -/
theorem revClosureAt_subset_food_union_support
    {M R : Type*} [DecidableEq M] [DecidableEq R]
    (Q : ReversibleCRS M R) (S : Finset R) :
    ∀ k, revClosureAt Q S k ⊆ Q.food ∪ revReactionSupport Q S := by
  intro k
  induction k with
  | zero => exact Finset.subset_union_left
  | succ k ih =>
      intro x hx
      simp only [revClosureAt, revClosureStep, Finset.mem_union,
        Finset.mem_biUnion] at hx
      rcases hx with hx | ⟨r, hr, hx⟩
      · exact ih hx
      · apply Finset.mem_union_right
        simp only [revReactionSupport, Finset.mem_biUnion]
        refine ⟨r, hr, ?_⟩
        by_cases hl : RevEnabledLhs Q (revClosureAt Q S k) r
        · by_cases hh : RevEnabledRhs Q (revClosureAt Q S k) r
          · simp [hl, hh] at hx
            rcases hx with hxr | hxl
            · exact Finset.mem_union_right _ hxr
            · exact Finset.mem_union_left _ hxl
          · simp [hl, hh] at hx
            exact Finset.mem_union_right _ hx
        · by_cases hh : RevEnabledRhs Q (revClosureAt Q S k) r
          · simp [hl, hh] at hx
            exact Finset.mem_union_left _ hx
          · simp [hl, hh] at hx

theorem seededClosureMolecules_subset_support {n : Nat}
    (bulk : Set (NonseedCoord n))
    (J : Finset (PolymerSeedReaction n 2)) :
    seededClosureMolecules bulk J ⊆
      binaryFood n 2 ∪ revReactionSupport (binaryPolymerCRS n 2)
        (gatewaySeededMaxRAF bulk J) := by
  intro x hx
  obtain ⟨k, hk⟩ := (mem_seededClosureMolecules bulk J x).mp hx
  exact revClosureAt_subset_food_union_support _ _ k hk

/-- A split-position reaction is incident with at most three molecules. -/
theorem card_binaryReaction_support_le_three {n : Nat} (r : Reaction n) :
    ((binaryPolymerCRS n 2).lhs r ∪
      (binaryPolymerCRS n 2).rhs r).card ≤ 3 := by
  have hpair : ({reactionLeft r, reactionRight r} :
      Finset (Molecule n)).card ≤ 2 := by
    have h := Finset.card_insert_le (reactionLeft r)
      ({reactionRight r} : Finset (Molecule n))
    simpa only [Finset.card_singleton, Nat.add_comm] using h
  calc
    ((binaryPolymerCRS n 2).lhs r ∪
      (binaryPolymerCRS n 2).rhs r).card
        ≤ ((binaryPolymerCRS n 2).lhs r).card +
          ((binaryPolymerCRS n 2).rhs r).card :=
            Finset.card_union_le _ _
    _ ≤ 2 + 1 := by
      simpa only [binaryPolymerCRS, Finset.card_singleton] using
        Nat.add_le_add_right hpair 1
    _ = 3 := by norm_num

theorem card_revReactionSupport_binary_le {n : Nat} (S : Finset (Reaction n)) :
    (revReactionSupport (binaryPolymerCRS n 2) S).card ≤ 3 * S.card := by
  calc
    (revReactionSupport (binaryPolymerCRS n 2) S).card
        ≤ ∑ r ∈ S, (((binaryPolymerCRS n 2).lhs r ∪
          (binaryPolymerCRS n 2).rhs r).card) := Finset.card_biUnion_le
    _ ≤ ∑ _r ∈ S, 3 := by
      exact Finset.sum_le_sum fun r _ => card_binaryReaction_support_le_three r
    _ = 3 * S.card := by simp [Nat.mul_comm]

theorem card_seededClosureMolecules_le {n : Nat}
    (bulk : Set (NonseedCoord n))
    (J : Finset (PolymerSeedReaction n 2)) :
    (seededClosureMolecules bulk J).card ≤
      (binaryFood n 2).card + 3 * (gatewaySeededMaxRAF bulk J).card := by
  calc
    (seededClosureMolecules bulk J).card
        ≤ (binaryFood n 2 ∪ revReactionSupport (binaryPolymerCRS n 2)
          (gatewaySeededMaxRAF bulk J)).card :=
            Finset.card_le_card (seededClosureMolecules_subset_support bulk J)
    _ ≤ (binaryFood n 2).card +
          (revReactionSupport (binaryPolymerCRS n 2)
            (gatewaySeededMaxRAF bulk J)).card := Finset.card_union_le _ _
    _ ≤ (binaryFood n 2).card + 3 *
          (gatewaySeededMaxRAF bulk J).card :=
            Nat.add_le_add_left
              (card_revReactionSupport_binary_le (gatewaySeededMaxRAF bulk J)) _

/-- Half-density ignition forces a reaction witness on the exponential
molecule scale; this is the bridge missing from small-RAF counting bounds. -/
theorem macroEvent_implies_exponential_witness {n : Nat}
    (J : Finset (PolymerSeedReaction n 2))
    {bulk : Set (NonseedCoord n)} (hmacro : bulk ∈ SeededBulkMacroEvent n J) :
    Fintype.card (Molecule n) ≤
      2 * ((binaryFood n 2).card +
        3 * (gatewaySeededMaxRAF bulk J).card) := by
  exact hmacro.trans (Nat.mul_le_mul_left 2
    (card_seededClosureMolecules_le bulk J))

end HordijkSteelThreshold
