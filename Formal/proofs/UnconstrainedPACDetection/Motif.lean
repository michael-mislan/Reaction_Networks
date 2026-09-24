import proofs.UnconstrainedPACDetection.Source
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod

namespace UnconstrainedPACDetection

variable {Entity Reaction : Type*}
  [Fintype Entity] [DecidableEq Entity]
  [Fintype Reaction] [DecidableEq Reaction]

abbrev Candidate (Entity Reaction : Type*) := Finset Entity × Finset Reaction

def ReversibleSource.Productive (source : ReversibleSource Entity Reaction)
    (entities : Finset Entity) (reactions : Finset Reaction) : Prop :=
  ∃ flow : Reaction → ℝ,
    (∀ reaction, reaction ∉ reactions → flow reaction = 0) ∧
    ∀ entity ∈ entities,
      0 < Finset.univ.sum (fun reaction =>
        source.net reaction entity * flow reaction)

def ReversibleSource.Motif (source : ReversibleSource Entity Reaction)
    (candidate : Candidate Entity Reaction) : Prop :=
  candidate.1.Nonempty ∧
    candidate.2.Nonempty ∧
    (∀ reaction ∈ candidate.2,
      source.sideAdmissible candidate.1 reaction) ∧
    source.Productive candidate.1 candidate.2

def ReversibleSource.PAC (source : ReversibleSource Entity Reaction)
    (candidate : Candidate Entity Reaction) : Prop :=
  source.Motif candidate ∧
    ∀ ⦃smaller⦄, smaller < candidate → ¬ source.Motif smaller

end UnconstrainedPACDetection
