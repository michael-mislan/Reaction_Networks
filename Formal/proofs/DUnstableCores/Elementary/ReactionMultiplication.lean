import proofs.DUnstableCores.ClassicalMassAction.Rate
import proofs.DUnstableCores.DScaling

namespace DUnstableCores

variable {Species Reaction : Type*}

def multiplyReactions (Q : SourceNetwork Species Reaction) (c : Reaction → ℕ) :
    SourceNetwork Species Reaction where
  reactant := fun s r => Q.reactant s r * c r
  product := fun s r => Q.product s r * c r
  catalyst := fun s r => Q.catalyst s r * c r
  catalyst_le_reactant := fun s r => Nat.mul_le_mul_right _ (Q.catalyst_le_reactant s r)
  catalyst_le_product := fun s r => Nat.mul_le_mul_right _ (Q.catalyst_le_product s r)

theorem multiplyReactions_stoich (Q : SourceNetwork Species Reaction)
    (c : Reaction → ℕ) (s : Species) (r : Reaction) :
    (multiplyReactions Q c).stoich s r = Q.stoich s r * (c r : ℤ) := by
  simp [multiplyReactions, SourceNetwork.stoich, sub_mul]

theorem multiplyReactions_reactant_iff (Q : SourceNetwork Species Reaction)
    (c : Reaction → ℕ) (hc : ∀ r, 0 < c r) (s : Species) (r : Reaction) :
    (multiplyReactions Q c).Reactant s r ↔ Q.Reactant s r := by
  change 0 < Q.reactant s r * c r ↔ 0 < Q.reactant s r
  constructor
  · intro h
    by_contra hn
    have hz : Q.reactant s r = 0 := by omega
    simp [hz] at h
  · intro h
    exact Nat.mul_pos h (hc r)

theorem multiplyReactions_catalystFree (Q : SourceNetwork Species Reaction)
    (c : Reaction → ℕ) (h : ∀ s r, Q.reactant s r * Q.product s r = 0) :
    ∀ s r, (multiplyReactions Q c).reactant s r *
      (multiplyReactions Q c).product s r = 0 := by
  intro s r
  change (Q.reactant s r * c r) * (Q.product s r * c r) = 0
  calc
    _ = (Q.reactant s r * Q.product s r) * (c r * c r) := by ring
    _ = 0 := by rw [h]; simp

def multipliedChildToBase (Q : SourceNetwork Species Reaction)
    (c : Reaction → ℕ) (hc : ∀ r, 0 < c r)
    (κ : ChildSelection (multiplyReactions Q c)) : ChildSelection Q where
  species := κ.species
  reactions := κ.reactions
  assign := κ.assign
  reactant_match := fun x =>
    (multiplyReactions_reactant_iff Q c hc x.1 (κ.assign x).1).mp (κ.reactant_match x)

theorem multipliedChild_realMatrix [DecidableEq Species] [DecidableEq Reaction]
    (Q : SourceNetwork Species Reaction) (c : Reaction → ℕ) (hc : ∀ r, 0 < c r)
    (κ : ChildSelection (multiplyReactions Q c)) :
    κ.realMatrix = rightScale (multipliedChildToBase Q c hc κ).realMatrix
      (fun j => (c (κ.assign j).1 : ℝ)) := by
  ext i j
  change (((multiplyReactions Q c).stoich i.1 (κ.assign j).1 : ℤ) : ℝ) =
    (Q.stoich i.1 (κ.assign j).1 : ℝ) * (c (κ.assign j).1 : ℝ)
  rw [multiplyReactions_stoich]
  push_cast
  rfl

theorem dNonUnstable_rightScale {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (c : ι → ℝ) (hc : ∀ i, 0 < c i)
    (hA : DNonUnstable A) : DNonUnstable (rightScale A c) := by
  intro d hd
  have heq : rightScale (rightScale A c) d = rightScale A (fun i => c i * d i) := by
    ext i j
    simp [rightScale, mul_assoc]
  rw [heq]
  exact hA _ (fun i => mul_pos (hc i) (hd i))

theorem multiplyReactions_all_children [DecidableEq Species] [DecidableEq Reaction]
    (Q : SourceNetwork Species Reaction) (c : Reaction → ℕ) (hc : ∀ r, 0 < c r)
    (hQ : ∀ κ : ChildSelection Q, DNonUnstable κ.realMatrix)
    (κ : ChildSelection (multiplyReactions Q c)) : DNonUnstable κ.realMatrix := by
  rw [multipliedChild_realMatrix Q c hc κ]
  exact dNonUnstable_rightScale _ _ (fun i => Nat.cast_pos.mpr (hc _)) (hQ _)

end DUnstableCores
