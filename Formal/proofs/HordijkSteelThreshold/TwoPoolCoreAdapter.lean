import proofs.HordijkSteelThreshold.MarkedCoreAdapter

namespace HordijkSteelThreshold

open RAF RAF.Polymer RAF.Concrete

/-- Two finite molecule pools cross-support one another when every nonfood
molecule in either pool has a split reaction whose factors lie in their union,
and whose catalyst lies in the opposite pool. -/
def IsCrossSupportedMoleculePools {n : Nat} (foodLength : Nat)
    (Cat : Catalysis (Molecule n) (Reaction n))
    (A B : Finset (Molecule n)) : Prop :=
  binaryFood n foodLength ⊆ A ∪ B ∧
  (∀ x ∈ A, foodLength < molLength x →
    ∃ r : Reaction n,
      reactionProduct r = x ∧ reactionLeft r ∈ A ∪ B ∧
        reactionRight r ∈ A ∪ B ∧ ∃ y ∈ B, Cat y r) ∧
  (∀ x ∈ B, foodLength < molLength x →
    ∃ r : Reaction n,
      reactionProduct r = x ∧ reactionLeft r ∈ A ∪ B ∧
        reactionRight r ∈ A ∪ B ∧ ∃ y ∈ A, Cat y r)

/-- Cross-support is source-faithful: after taking the union, the two-pool
witness is an ordinary internally supported marked molecule core. -/
theorem crossSupportedPools_union_isMarkedMoleculeCore {n foodLength : Nat}
    {Cat : Catalysis (Molecule n) (Reaction n)}
    {A B : Finset (Molecule n)}
    (hAB : IsCrossSupportedMoleculePools foodLength Cat A B) :
    IsMarkedMoleculeCore foodLength Cat (A ∪ B) := by
  refine ⟨hAB.1, ?_⟩
  intro x hx hlen
  rcases Finset.mem_union.mp hx with hxA | hxB
  · obtain ⟨r, hprod, hleft, hright, y, hy, hcat⟩ :=
      hAB.2.1 x hxA hlen
    exact ⟨r, hprod, hleft, hright, y, Finset.mem_union_right A hy, hcat⟩
  · obtain ⟨r, hprod, hleft, hright, y, hy, hcat⟩ :=
      hAB.2.2 x hxB hlen
    exact ⟨r, hprod, hleft, hright, y, Finset.mem_union_left B hy, hcat⟩

/-- Any nontrivial pair of cross-supporting pools gives a literal reversible
RAF in the finite binary polymer source. -/
theorem crossSupportedPools_isRevRAF {n foodLength : Nat}
    {Cat : Catalysis (Molecule n) (Reaction n)}
    {A B : Finset (Molecule n)}
    (hAB : IsCrossSupportedMoleculePools foodLength Cat A B)
    (hnontrivial : ∃ x ∈ A ∪ B, foodLength < molLength x) :
    IsRevRAF (binaryPolymerCRS n foodLength) Cat
      (markedCoreReactions Cat (A ∪ B)) := by
  exact markedCoreReactions_isRevRAF
    (crossSupportedPools_union_isMarkedMoleculeCore hAB) hnontrivial

/-- A high-layer cross-supported core may be proved using an enlarged temporary
food cutoff `L`.  If the finitely many original nonfood molecules below `L`
also receive internal support, the same union is a marked core for the literal
food cutoff two.  This separates the high-layer and nucleus target-coordinate
blocks. -/
theorem crossSupportedPools_descend_to_food_two {n L : Nat}
    {Cat : Catalysis (Molecule n) (Reaction n)}
    {A B : Finset (Molecule n)} (h2L : 2 ≤ L)
    (hAB : IsCrossSupportedMoleculePools L Cat A B)
    (hnucleus : ∀ x ∈ binaryFood n L, 2 < molLength x →
      ∃ r : Reaction n,
        reactionProduct r = x ∧ reactionLeft r ∈ A ∪ B ∧
          reactionRight r ∈ A ∪ B ∧ ∃ y ∈ A ∪ B, Cat y r) :
    IsMarkedMoleculeCore 2 Cat (A ∪ B) := by
  refine ⟨?_, ?_⟩
  · intro x hx
    apply hAB.1
    have hxlen : molLength x ≤ 2 := by
      simpa [binaryFood] using hx
    simpa [binaryFood] using hxlen.trans h2L
  · intro x hx hlen
    by_cases hlong : L < molLength x
    · rcases Finset.mem_union.mp hx with hxA | hxB
      · obtain ⟨r, hprod, hleft, hright, y, hy, hcat⟩ :=
          hAB.2.1 x hxA hlong
        exact ⟨r, hprod, hleft, hright, y,
          Finset.mem_union_right A hy, hcat⟩
      · obtain ⟨r, hprod, hleft, hright, y, hy, hcat⟩ :=
          hAB.2.2 x hxB hlong
        exact ⟨r, hprod, hleft, hright, y,
          Finset.mem_union_left B hy, hcat⟩
    · have hxfood : x ∈ binaryFood n L := by
        simp [binaryFood, Nat.le_of_not_gt hlong]
      exact hnucleus x hxfood hlen

/-- The descended two-pool witness yields a literal reversible RAF. -/
theorem crossSupportedPools_descend_isRevRAF {n L : Nat}
    {Cat : Catalysis (Molecule n) (Reaction n)}
    {A B : Finset (Molecule n)} (h2L : 2 ≤ L)
    (hAB : IsCrossSupportedMoleculePools L Cat A B)
    (hnucleus : ∀ x ∈ binaryFood n L, 2 < molLength x →
      ∃ r : Reaction n,
        reactionProduct r = x ∧ reactionLeft r ∈ A ∪ B ∧
          reactionRight r ∈ A ∪ B ∧ ∃ y ∈ A ∪ B, Cat y r)
    (hnontrivial : ∃ x ∈ A ∪ B, 2 < molLength x) :
    IsRevRAF (binaryPolymerCRS n 2) Cat
      (markedCoreReactions Cat (A ∪ B)) := by
  exact markedCoreReactions_isRevRAF
    (crossSupportedPools_descend_to_food_two h2L hAB hnucleus) hnontrivial

end HordijkSteelThreshold
