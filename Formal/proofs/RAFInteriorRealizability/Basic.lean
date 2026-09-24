import proofs.RAF.Frankl.PairGadget

namespace RAFInteriorRealizability

open RAF RAF.Frankl

universe u

/-- A finite interior operator is represented by its empty-containing,
union-closed fixed family.  `UnionClosedData.interior` is the unique operator
with this fixed family. -/
abbrev InteriorOperator (E : Type u) [DecidableEq E] := UnionClosedData E

namespace InteriorOperator

variable {E : Type u} [DecidableEq E]

noncomputable def apply (ψ : InteriorOperator E) (S : Finset E) : Finset E :=
  ψ.interior S

theorem apply_subset (ψ : InteriorOperator E) (S : Finset E) :
    ψ.apply S ⊆ S :=
  ψ.interior_subset S

theorem apply_mono (ψ : InteriorOperator E) {S T : Finset E} (hST : S ⊆ T) :
    ψ.apply S ⊆ ψ.apply T :=
  ψ.interior_mono hST

theorem apply_idempotent (ψ : InteriorOperator E) (S : Finset E) :
    ψ.apply (ψ.apply S) = ψ.apply S :=
  (UnionClosedData.fixed_iff_mem ψ (ψ.apply S)).2 (ψ.interior_mem S)

theorem fixed_iff_mem (ψ : InteriorOperator E) (S : Finset E) :
    ψ.apply S = S ↔ S ∈ ψ.family :=
  UnionClosedData.fixed_iff_mem ψ S

theorem apply_eq_of_family_eq {ψ χ : InteriorOperator E}
    (h : ψ.family = χ.family) : ψ.apply = χ.apply := by
  funext S
  unfold apply UnionClosedData.interior
  rw [h]

end InteriorOperator

end RAFInteriorRealizability
