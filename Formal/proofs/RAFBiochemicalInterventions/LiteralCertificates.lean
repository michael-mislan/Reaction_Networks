import Std
import Lean

namespace RAFBiochemicalLiteral

inductive Formula where
  | atom : Nat → Formula
  | both : Formula → Formula → Formula
  | either : Formula → Formula → Formula
  | yes : Formula
  deriving DecidableEq

structure Row where
  direction : Nat
  action : Nat
  inputs : List Nat
  outputs : List Nat
  catalyst : Formula
  deriving DecidableEq

/-- Literal food generation: catalysts are deliberately absent from this
inductive relation and are checked only in the final generated set. -/
inductive Generated (rows : List Row) (food : List Nat) : Nat → Prop where
  | food {x} : x ∈ food → Generated rows food x
  | reaction (r : Row) : r ∈ rows →
      (∀ x ∈ r.inputs, Generated rows food x) →
      ∀ y ∈ r.outputs, Generated rows food y

def remaining (rows : List Row) (cut : List Nat) : List Row :=
  rows.filter (fun r => !cut.contains r.action)

def Barrier (rows : List Row) (food blocked : List Nat) : Prop :=
  (∀ x ∈ food, x ∉ blocked) ∧
    ∀ r ∈ rows, ∀ x ∈ r.outputs, x ∈ blocked → ∃ y ∈ r.inputs, y ∈ blocked

instance (rows : List Row) (food blocked : List Nat) :
    Decidable (Barrier rows food blocked) := by
  unfold Barrier
  infer_instance

def checkBarrier (rows : List Row) (food blocked cut : List Nat) : Bool :=
  decide (Barrier (remaining rows cut) food blocked)

theorem barrier_exclusion {rows : List Row} {food blocked : List Nat}
    (h : Barrier rows food blocked) {x : Nat} (hx : Generated rows food x) :
    x ∉ blocked := by
  induction hx with
  | food hx => exact h.1 _ hx
  | reaction r hr _ y hy ih =>
      intro hyb
      obtain ⟨z,hz,hzb⟩ := h.2 r hr y hy hyb
      exact ih z hz hzb

theorem checked_exclusion (rows : List Row) (food blocked cut : List Nat)
    (h : checkBarrier rows food blocked cut = true) {p : Nat} (hp : p ∈ blocked) :
    ¬ Generated (remaining rows cut) food p := by
  intro hg
  have hb : Barrier (remaining rows cut) food blocked := of_decide_eq_true h
  exact barrier_exclusion hb hg hp

end RAFBiochemicalLiteral
