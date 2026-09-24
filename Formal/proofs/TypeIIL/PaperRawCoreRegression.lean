import proofs.TypeIIL.PaperRawCore

namespace TypeIIL

open TypeII3

namespace PaperRawRegression

open SourceCyclicNonemptyGapSystem

/-!
Semantic regression checks for the terminal source theorem.  These are kept
as named declarations so strict verification checks that the public proof
really accepts the exceptional quotient and the nonuniform separated
geometries singled out in the source-lift audit.
-/

/-- Regression 1: the fully coincident `l = 3` quotient is proved directly,
including arbitrary positive integer fork multiplicities. -/
theorem all_coincident_typeII3
    (p : AllZeroParams) (x y : AllZeroState)
    (hx : PositiveAllZeroState x) (hy : PositiveAllZeroState y)
    (hxs : IsAllZeroStationary p x)
    (hys : IsAllZeroStationary p y) : x = y :=
  all_zero_unistationarity p x y hx hy hxs hys

/-- Regressions 2--5 in one deliberately nonuniform separated instance:
neighboring stem lengths differ, a minimum return tail and a longer return
tail coexist, and at least one main-cycle multiplicity is greater than one.
The conclusion uses no equality or unit-weight hypothesis on the main
cycle; the extra clauses only pin the requested edge geometry. -/
theorem separated_nonuniform_geometry
    {n l : ℕ} {next : Fin n ≃ Fin n}
    {back : Fin n → Option (Fin n)}
    (S : SourceCyclicNonemptyGapSystem (l := l) next back)
    (hl : 3 ≤ l) (weight : Fin n → ℕ) (hw : ∀ r, 0 < weight r)
    (rates : PaperSeparatedRates S weight)
    (hminimal : PaperReturnRestrictionsMinimal rates)
    (hunequal : ∃ j, S.gapLength j ≠ S.gapLength (S.step j))
    (hminimum : ∃ j, rates.tailDepth j = 1)
    (hlonger : ∃ j, 2 ≤ rates.tailDepth j)
    (hweighted : ∃ r, 2 ≤ weight r)
    (x y : PaperSeparatedState S weight rates)
    (hx : PositivePaperSeparatedState x)
    (hy : PositivePaperSeparatedState y)
    (hxs : IsPaperSeparatedStationary rates x)
    (hys : IsPaperSeparatedStationary rates y) : x = y := by
  have hedgeAudit :
      (∃ j, S.gapLength j ≠ S.gapLength (S.step j)) ∧
      (∃ j, rates.tailDepth j = 1) ∧
      (∃ j, 2 ≤ rates.tailDepth j) ∧
      (∃ r, 2 ≤ weight r) :=
    ⟨hunequal, hminimum, hlonger, hweighted⟩
  exact hedgeAudit.elim fun _ _ =>
    S.paper_separated_typeII_l_states_equal hl weight hw rates hminimal
      x y hx hy hxs hys

end PaperRawRegression

end TypeIIL
