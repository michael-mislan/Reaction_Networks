import proofs.IrrRAFEnumeration.HybridCharge

namespace IrrRAFEnumeration

/-- A binary refinement of a component-factorization tree.  A factorization
with more than two children is refined by inserting binary split nodes; this
can only increase the node count, so the bound below also pays for the
unrefined factor tree. -/
inductive FactorTree (α : Type*) where
  | leaf (support : Finset α) : FactorTree α
  | split (support : Finset α)
      (left right : FactorTree α) : FactorTree α

namespace FactorTree

/-- Number of states in a binary factor tree, including its terminal states. -/
def nodeCount : FactorTree α → ℕ
  | .leaf _ => 1
  | .split _ left right => 1 + left.nodeCount + right.nodeCount

/-- Number of terminal component states in a binary factor tree. -/
def leafCount : FactorTree α → ℕ
  | .leaf _ => 1
  | .split _ left right => left.leafCount + right.leafCount

/-- Every nonterminal factor state has two component children, hence a factor
tree has strictly fewer than twice as many states as terminal components. -/
theorem nodeCount_lt_two_mul_leafCount (tree : FactorTree α) :
    tree.nodeCount < 2 * tree.leafCount := by
  induction tree with
  | leaf support => simp [nodeCount, leafCount]
  | split support left right hleft hright =>
      simp only [nodeCount, leafCount]
      omega

end FactorTree

/-- Total number of factor states in a forest spawned by root/hybrid seeds. -/
def factorForestNodeCount (forest : List (FactorTree α)) : ℕ :=
  (forest.map FactorTree.nodeCount).sum

/-- Total number of terminal component states in that forest. -/
def factorForestLeafCount (forest : List (FactorTree α)) : ℕ :=
  (forest.map FactorTree.leafCount).sum

/-- The binary factor-tree inequality sums over an arbitrary forest. -/
theorem factorForestNodeCount_le_two_mul_leafCount
    (forest : List (FactorTree α)) :
    factorForestNodeCount forest ≤ 2 * factorForestLeafCount forest := by
  induction forest with
  | nil => simp [factorForestNodeCount, factorForestLeafCount]
  | cons tree forest ih =>
      have htree : tree.nodeCount ≤ 2 * tree.leafCount :=
        Nat.le_of_lt tree.nodeCount_lt_two_mul_leafCount
      simp [factorForestNodeCount, factorForestLeafCount] at ih ⊢
      omega

/-- If the terminal components inject into the ground vertices (as they do
for pairwise-disjoint nonempty component supports), fewer than two ground-set
units pay for every state in the component-factor forest. -/
theorem factorForestNodeCount_le_two_mul_ground
    (U : Finset α) (forest : List (FactorTree α))
    (hLeaves : factorForestLeafCount forest ≤ U.card) :
    factorForestNodeCount forest ≤ 2 * U.card := by
  calc
    factorForestNodeCount forest ≤ 2 * factorForestLeafCount forest :=
      factorForestNodeCount_le_two_mul_leafCount forest
    _ ≤ 2 * U.card := Nat.mul_le_mul_left 2 hLeaves

/-- Pairwise-disjoint nonempty terminal components inject into their ambient
ground set.  This is the exact set-theoretic fact used to discharge the leaf
premise of `factorForestNodeCount_le_two_mul_ground`. -/
theorem disjointNonemptyComponents_card_le_ground
    [DecidableEq α] (U : Finset α) (components : Finset (Finset α))
    (hNonempty : ∀ component ∈ components, component.Nonempty)
    (hDisjoint : (components : Set (Finset α)).PairwiseDisjoint id)
    (hSub : components.biUnion id ⊆ U) :
    components.card ≤ U.card := by
  have hOne : ∑ component ∈ components, 1 ≤
      ∑ component ∈ components, component.card := by
    apply Finset.sum_le_sum
    intro component hcomponent
    exact (Finset.one_le_card.mpr (hNonempty component hcomponent))
  have hUnion : (components.biUnion id).card ≤ U.card :=
    Finset.card_le_card hSub
  rw [Finset.card_biUnion hDisjoint] at hUnion
  simpa using hOne.trans hUnion

/-- Fully structural factor-forest bound: once its terminal-state count is the
number of pairwise-disjoint nonempty component supports, at most `2|U|`
factor states occur. -/
theorem factorForestNodeCount_le_of_disjointComponents
    [DecidableEq α] (U : Finset α) (forest : List (FactorTree α))
    (components : Finset (Finset α))
    (hLeafCount : factorForestLeafCount forest = components.card)
    (hNonempty : ∀ component ∈ components, component.Nonempty)
    (hDisjoint : (components : Set (Finset α)).PairwiseDisjoint id)
    (hSub : components.biUnion id ⊆ U) :
    factorForestNodeCount forest ≤ 2 * U.card := by
  apply factorForestNodeCount_le_two_mul_ground U forest
  rw [hLeafCount]
  exact disjointNonemptyComponents_card_le_ground
    U components hNonempty hDisjoint hSub

end IrrRAFEnumeration
