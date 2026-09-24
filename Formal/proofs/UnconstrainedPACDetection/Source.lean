import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic

/-!
Literal source semantics for unconstrained PAC detection.

A reversible reaction retains one identity and its two original nonnegative
integer complexes.  Its flux is signed; in particular, this is not a pair of
independently selectable irreversible reactions.
-/

namespace UnconstrainedPACDetection

structure ReversibleSource (Entity Reaction : Type*) where
  left : Reaction → Entity → ℕ
  right : Reaction → Entity → ℕ

variable {Entity Reaction : Type*}

def ReversibleSource.net (source : ReversibleSource Entity Reaction)
    (reaction : Reaction) (entity : Entity) : ℝ :=
  (source.right reaction entity : ℝ) - (source.left reaction entity : ℝ)

def ReversibleSource.sideAdmissible [DecidableEq Entity]
    (source : ReversibleSource Entity Reaction) (entities : Finset Entity)
    (reaction : Reaction) : Prop :=
  (∃ entity ∈ entities, 0 < source.left reaction entity) ∧
    ∃ entity ∈ entities, 0 < source.right reaction entity

end UnconstrainedPACDetection
