import proofs.RAF.Frankl.PairBoundary
import proofs.RAF.Frankl.ElementaryHorn

namespace RAF.Frankl.PairGadget
open RAF RAFQueryCompilation PairReaction
open scoped Classical

variable {U : Type*} [Fintype U] [DecidableEq U]

/-- The concrete universality construction has one food molecule, two reactions
per coordinate, one catalyst per reaction, precisely disjoint catalytic
two-cycles, and at most two closure rounds for every availability. Its exact
family, frequencies and availability interior are all preserved. -/
theorem sparse_two_round_realization (D : UnionClosedData U) :
    (crs D).food.card = 1 ∧
    Fintype.card (PairReaction U) = 2 * Fintype.card U ∧
    (∀ r : PairReaction U, ∃! x : PairMolecule U, catalysis x r) ∧
    (∀ r s : PairReaction U,
      (∃ x ∈ (crs D).outputs r, catalysis x s) ↔
        (∃ i, r = producer i ∧ s = gate i) ∨
        (∃ i, r = gate i ∧ s = producer i)) ∧
    (∀ T : Finset (PairReaction U), ∀ k : Nat,
      closureAt (crs D) T (k + 2) = closureAt (crs D) T 2) ∧
    (∀ T : Finset (PairReaction U),
      evaluate (crs D) catalysis T = encode (D.interior (completePairs T))) ∧
    rafFamily (crs D) catalysis = (D.family.erase ∅).image encode ∧
    (∀ i : U, frequency (crs D) catalysis (producer i) =
      (D.family.filter (fun A => i ∈ A)).card ∧
      frequency (crs D) catalysis (gate i) =
        (D.family.filter (fun A => i ∈ A)).card) := by
  exact ⟨one_food D,two_reactions_per_coordinate,unique_catalyst,
    catalytic_edges D,closure_stabilizes_after_two D,evaluate_eq_encode_interior D,
    rafFamily_eq_image D,fun i => ⟨producer_frequency D i,gate_frequency D i⟩⟩

end RAF.Frankl.PairGadget
