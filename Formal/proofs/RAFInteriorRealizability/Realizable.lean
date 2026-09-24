import proofs.RAFInteriorRealizability.Basic

namespace RAFInteriorRealizability

open RAF RAF.Frankl

universe u

variable {E : Type u} [Fintype E] [DecidableEq E]

/-- A literal ordinary RAF system whose reaction type is exactly the abstract
ground type.  The molecule type is finite but may contain arbitrary auxiliary
molecules. -/
structure LiteralRealization (E : Type u) [Fintype E] [DecidableEq E] where
  M : Type u
  fintypeM : Fintype M
  decEqM : DecidableEq M
  Q : @CRS M E decEqM
  C : Catalysis M E

namespace LiteralRealization

noncomputable def fixedData (W : LiteralRealization E) : InteriorOperator E := by
  letI : Fintype W.M := W.fintypeM
  exact @PairGadget.fixedData W.M E _ W.decEqM inferInstance W.Q W.C

noncomputable def rafInterior (W : LiteralRealization E) (S : Finset E) : Finset E :=
  W.fixedData.apply S

theorem fixed_iff (W : LiteralRealization E) (S : Finset E) :
    W.rafInterior S = S ↔ S ∈ W.fixedData.family :=
  W.fixedData.fixed_iff_mem S

end LiteralRealization

/-- Exact same-ground-set RAF realizability: one literal reaction for each
ground coordinate and equality of the induced maxRAF interior operator. -/
def SameGroundRAFRealizable (ψ : InteriorOperator E) : Prop :=
  ∃ W : LiteralRealization E, ∀ S, W.rafInterior S = ψ.apply S

theorem sameGroundRAFRealizable_iff_fixedFamily (ψ : InteriorOperator E) :
    SameGroundRAFRealizable ψ ↔
      ∃ W : LiteralRealization E, W.fixedData.family = ψ.family := by
  constructor
  · rintro ⟨W, hW⟩
    refine ⟨W, ?_⟩
    ext S
    rw [← W.fixed_iff S, ← ψ.fixed_iff_mem S, hW S]
  · rintro ⟨W, hW⟩
    refine ⟨W, ?_⟩
    have hop : W.fixedData.apply = ψ.apply :=
      InteriorOperator.apply_eq_of_family_eq hW
    exact fun S => congrFun hop S

end RAFInteriorRealizability
