import proofs.RAFInteriorRealizability.FoodSupportCertificate

namespace RAFInteriorRealizability

open RAF RAF.Frankl

universe u

variable {E : Type u} [Fintype E] [DecidableEq E]

/-- Typed molecule namespace for the literal one-reaction construction. -/
inductive MarkerMolecule (E : Type u)
  | food
  | catalyst (e : E)
  | marker (target : E) (blocker : Finset E)
  deriving DecidableEq, Fintype

namespace MarkerSource

open MarkerMolecule

/-- One literal reaction per ground coordinate.  Reaction `e` requires every
all-blocker marker for `e`, produces its private catalyst, and produces every
marker whose blocker it hits. -/
noncomputable def crs (A : AntimatroidData E) : CRS (MarkerMolecule E) E := by
  classical
  exact {
    inputs := fun e => insert food <| Finset.univ.filter fun m =>
      match m with
      | marker target B => target = e ∧ A.toUnionClosedData.IsBlocker e B
      | _ => False
    outputs := fun e => insert (catalyst e) <| Finset.univ.filter fun m =>
      match m with
      | marker target B => A.toUnionClosedData.IsBlocker target B ∧ e ∈ B
      | _ => False
    food := {food}
  }

/-- Private catalyst products realize exactly the supplied predecessor map. -/
def catalysis (P : E → Finset E) : Catalysis (MarkerMolecule E) E
  | catalyst u, e => u ∈ P e
  | _, _ => False

end MarkerSource

end RAFInteriorRealizability
