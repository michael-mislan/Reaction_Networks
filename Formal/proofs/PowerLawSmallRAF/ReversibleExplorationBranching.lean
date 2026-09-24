import proofs.PowerLawSmallRAF.ReversibleExplorationEnvelope
import proofs.PowerLawSmallRAF.ReversibleExplorationStructure

namespace PowerLawSmallRAF

open RAF.Polymer RAF.Concrete

/-- The exact local source bound behind the reversible exploration code:
through step `n`, an available set grown from six foods by at most two
molecules per productive reaction has at most `C_n` enabled channels. -/
theorem card_reversiblyEnabledReaction_le_sourceBranch
    {n i : Nat} (available : Finset (Molecule n))
    (hcard : available.card ≤ 6 + 2 * i) (hi : i ≤ n) :
    Fintype.card (ReversiblyEnabledReaction available) ≤
      sourceReversibleBranchCount n := by
  calc
    Fintype.card (ReversiblyEnabledReaction available) ≤
        available.card ^ 2 + available.card * n :=
      card_reversiblyEnabledReaction_le available
    _ = available.card * (available.card + n) := by ring
    _ ≤ (6 + 2 * n) * (6 + 3 * n) := by
      apply Nat.mul_le_mul
      · omega
      · omega
    _ = sourceReversibleBranchCount n := by
      rfl

/-- Molecules exposed by using one reversible split-position channel. -/
def reversibleReactionStep {n : Nat} (available : Finset (Molecule n))
    (r : Reaction n) : Finset (Molecule n) :=
  available ∪ {reactionLeft r, reactionRight r, reactionProduct r}

/-- One enabled reversible channel adds at most two previously unavailable
molecules (a ligation adds its product; a cleavage adds its two factors). -/
theorem card_reversibleReactionStep_le_add_two {n : Nat}
    (available : Finset (Molecule n))
    (r : ReversiblyEnabledReaction available) :
    (reversibleReactionStep available r).card ≤ available.card + 2 := by
  let rv : Reaction n := r.val
  change (reversibleReactionStep available rv).card ≤ available.card + 2
  have henabled :
      (reactionLeft rv ∈ available ∧ reactionRight rv ∈ available) ∨
        reactionProduct rv ∈ available := r.property
  rcases henabled with hligation | hcleavage
  · have hsubset : reversibleReactionStep available rv ⊆
        insert (reactionProduct rv) available := by
      intro x hx
      simp only [reversibleReactionStep, Finset.mem_union,
        Finset.mem_insert, Finset.mem_singleton] at hx ⊢
      rcases hx with hx | hx
      · exact Or.inr hx
      · rcases hx with hx | hx | hx
        · subst x
          exact Or.inr hligation.1
        · subst x
          exact Or.inr hligation.2
        · exact Or.inl hx
    calc
      (reversibleReactionStep available rv).card ≤
          (insert (reactionProduct rv) available).card :=
        Finset.card_le_card hsubset
      _ ≤ available.card + 1 := Finset.card_insert_le _ _
      _ ≤ available.card + 2 := by omega
  · have hsubset : reversibleReactionStep available rv ⊆
        insert (reactionLeft rv) (insert (reactionRight rv) available) := by
      intro x hx
      simp only [reversibleReactionStep, Finset.mem_union,
        Finset.mem_insert, Finset.mem_singleton] at hx ⊢
      rcases hx with hx | hx
      · exact Or.inr (Or.inr hx)
      · rcases hx with hx | hx | hx
        · exact Or.inl hx
        · exact Or.inr (Or.inl hx)
        · subst x
          exact Or.inr (Or.inr hcleavage)
    calc
      (reversibleReactionStep available rv).card ≤
          (insert (reactionLeft rv) (insert (reactionRight rv) available)).card :=
        Finset.card_le_card hsubset
      _ ≤ (insert (reactionRight rv) available).card + 1 :=
        Finset.card_insert_le _ _
      _ ≤ (available.card + 1) + 1 := by
        exact Nat.add_le_add_right
          (Finset.card_insert_le (reactionRight rv) available) 1
      _ = available.card + 2 := by omega

end PowerLawSmallRAF
