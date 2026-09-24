import Mathlib
import proofs.TypeII3.Network.SourceMembership

namespace TypeIIL

/-- Positive rate constants for the seven-cycle source topology below. -/
structure SourceTypeII6Rates where
  plus : Fin 7 → ℝ
  minus : Fin 7 → ℝ
  degrade : Fin 7 → ℝ
  plus_pos : ∀ i, 0 < plus i
  minus_pos : ∀ i, 0 < minus i
  degrade_pos : ∀ i, 0 < degrade i

abbrev SourceTypeII6State := Fin 7 → ℝ

/-- Back-product indices for the six forks at cycle indices 0,2,3,4,5,6.
Index 1 is the sole ordinary one-to-one reaction. -/
def sourceTypeII6Back : Fin 7 → Fin 7 := ![6, 0, 1, 2, 3, 4, 5]

def sourceTypeII6Current (r : SourceTypeII6Rates)
    (x : SourceTypeII6State) (i : Fin 7) : ℝ :=
  match i.val with
  | 0 => r.plus 0 * x 0 - r.minus 0 * x 1 * x 6
  | 1 => r.plus 1 * x 1 - r.minus 1 * x 2
  | 2 => r.plus 2 * x 2 - r.minus 2 * x 3 * x 1
  | 3 => r.plus 3 * x 3 - r.minus 3 * x 4 * x 2
  | 4 => r.plus 4 * x 4 - r.minus 4 * x 5 * x 3
  | 5 => r.plus 5 * x 5 - r.minus 5 * x 6 * x 4
  | _ => r.plus 6 * x 6 - r.minus 6 * x 0 * x 5

/-- The seven mass-action steady equations.  They are exactly the reversible
extension, with positive degradation at every species, of

  x0 → x1+x6, x1 → x2, x2 → x3+x1, x3 → x4+x2,
  x4 → x5+x3, x5 → x6+x4, x6 → x0+x5.

Thus the one-based paper indices are `i=(1,3,4,5,6,7)` and
`σ=(7,2,3,4,5,6)`, satisfying all displayed Type II_6 weak inequalities. -/
def IsSourceTypeII6Stationary (r : SourceTypeII6Rates)
    (x : SourceTypeII6State) : Prop :=
  sourceTypeII6Current r x 6 - sourceTypeII6Current r x 0 - r.degrade 0 * x 0 = 0 ∧
  sourceTypeII6Current r x 0 - sourceTypeII6Current r x 1 +
    sourceTypeII6Current r x 2 - r.degrade 1 * x 1 = 0 ∧
  sourceTypeII6Current r x 1 - sourceTypeII6Current r x 2 +
    sourceTypeII6Current r x 3 - r.degrade 2 * x 2 = 0 ∧
  sourceTypeII6Current r x 2 - sourceTypeII6Current r x 3 +
    sourceTypeII6Current r x 4 - r.degrade 3 * x 3 = 0 ∧
  sourceTypeII6Current r x 3 - sourceTypeII6Current r x 4 +
    sourceTypeII6Current r x 5 - r.degrade 4 * x 4 = 0 ∧
  sourceTypeII6Current r x 4 - sourceTypeII6Current r x 5 +
    sourceTypeII6Current r x 6 - r.degrade 5 * x 5 = 0 ∧
  sourceTypeII6Current r x 5 - sourceTypeII6Current r x 6 +
    sourceTypeII6Current r x 0 - r.degrade 6 * x 6 = 0

def PositiveSourceTypeII6State (x : SourceTypeII6State) : Prop := ∀ i, 0 < x i

noncomputable def sourceTypeII6CounterRates : SourceTypeII6Rates where
  plus := ![79873083/3546790543, 4870030864/39014695973,
    6049869075/39014695973, 562292665/7093581086,
    560635312/3546790543, 76005216/3546790543, 80869/82483501]
  minus := ![150591284/3546790543, 1809648/3546790543,
    401938000/39014695973, 1809648/3546790543,
    486297815/3546790543, 1809648/3546790543, 1809648/3546790543]
  degrade := ![72385920/3546790543, 1809648/3546790543,
    413617671/7093581086, 6785880025/78029391946,
    558389511/7093581086, 1809648/3546790543, 1809648/3546790543]
  plus_pos := by intro i; fin_cases i <;> norm_num
  minus_pos := by intro i; fin_cases i <;> norm_num
  degrade_pos := by intro i; fin_cases i <;> norm_num

noncomputable def sourceTypeII6StateOne : SourceTypeII6State := ![1, 1, 1, 1, 1, 1, 1]
noncomputable def sourceTypeII6StateTwo : SourceTypeII6State :=
  ![1, 1/16, 1/9, 1/5, 1/3, 4/3, 12]

theorem source_typeII6_index_contract :
    (1 : ℕ) = 1 ∧ 1 ≤ 2 ∧ 2 < 3 ∧ 3 ≤ 3 ∧ 3 < 4 ∧
    4 ≤ 4 ∧ 4 < 5 ∧ 5 ≤ 5 ∧ 5 < 6 ∧
    6 ≤ 6 ∧ 6 < 7 ∧ 7 ≤ 7 ∧ 7 < 8 := by norm_num

theorem source_typeII6_state_one_positive :
    PositiveSourceTypeII6State sourceTypeII6StateOne := by
  intro i
  fin_cases i <;> norm_num [sourceTypeII6StateOne]

theorem source_typeII6_state_two_positive :
    PositiveSourceTypeII6State sourceTypeII6StateTwo := by
  intro i
  fin_cases i <;> norm_num [sourceTypeII6StateTwo]

theorem source_typeII6_state_one_stationary :
    IsSourceTypeII6Stationary sourceTypeII6CounterRates sourceTypeII6StateOne := by
  simp [IsSourceTypeII6Stationary, sourceTypeII6Current,
    sourceTypeII6CounterRates, sourceTypeII6StateOne, Matrix.cons_val_zero]; norm_num

theorem source_typeII6_state_two_stationary :
    IsSourceTypeII6Stationary sourceTypeII6CounterRates sourceTypeII6StateTwo := by
  simp [IsSourceTypeII6Stationary, sourceTypeII6Current,
    sourceTypeII6CounterRates, sourceTypeII6StateTwo, Matrix.cons_val_zero]; norm_num

theorem source_typeII6_states_ne : sourceTypeII6StateOne ≠ sourceTypeII6StateTwo := by
  intro h
  have h1 := congrFun h (1 : Fin 7)
  norm_num [sourceTypeII6StateOne, sourceTypeII6StateTwo] at h1

/-- The proper species restriction `{x1,x2,x3}`, retaining the reactions
`x1 → x2`, `x2 → x3+x1`, and `x3 → x2` after chemostatting `x4`. -/
def sourceTypeII6Restriction123 : Fin 3 → Fin 3 → ℝ := ![
  ![-1, 1, 0],
  ![ 1,-1, 1],
  ![ 0, 1,-1]]

def sourceTypeII6RestrictionWitness : Fin 3 → ℝ := ![2, 3, 2]

/-- Exact `(Top)` witness for the proper restriction:
`S₁₂₃ (2,3,2)ᵀ = (1,1,1)ᵀ`. -/
theorem source_typeII6_restriction123_autocatalytic :
    TypeII3.StoichiometricallyAutocatalytic sourceTypeII6Restriction123 := by
  refine ⟨sourceTypeII6RestrictionWitness, ?_, ?_⟩
  · intro j
    fin_cases j <;> norm_num [sourceTypeII6RestrictionWitness]
  · intro i
    fin_cases i <;>
      norm_num [sourceTypeII6Restriction123, sourceTypeII6RestrictionWitness,
        Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ]

/-- Exact counterexample to the broader weak-index topology class.  It is not
a counterexample for cores: the species restriction `{x1,x2,x3}` (zero-based)
is already autocatalytic, so the seven-species network is not minimal. -/
theorem exists_nonminimal_weak_index_typeII6_multistationarity :
    ∃ (r : SourceTypeII6Rates) (x y : SourceTypeII6State),
      PositiveSourceTypeII6State x ∧ PositiveSourceTypeII6State y ∧
      IsSourceTypeII6Stationary r x ∧ IsSourceTypeII6Stationary r y ∧ x ≠ y := by
  exact ⟨sourceTypeII6CounterRates, sourceTypeII6StateOne, sourceTypeII6StateTwo,
    source_typeII6_state_one_positive, source_typeII6_state_two_positive,
    source_typeII6_state_one_stationary, source_typeII6_state_two_stationary,
    source_typeII6_states_ne⟩

/-- Strengthened regression: the weak-index two-root example comes together
with a formal `(Top)` witness for a proper three-species restriction. -/
theorem exists_weak_index_typeII6_multistationarity_with_proper_autocatalytic_restriction :
    TypeII3.StoichiometricallyAutocatalytic sourceTypeII6Restriction123 ∧
      ∃ (r : SourceTypeII6Rates) (x y : SourceTypeII6State),
        PositiveSourceTypeII6State x ∧ PositiveSourceTypeII6State y ∧
        IsSourceTypeII6Stationary r x ∧ IsSourceTypeII6Stationary r y ∧ x ≠ y := by
  exact ⟨source_typeII6_restriction123_autocatalytic,
    exists_nonminimal_weak_index_typeII6_multistationarity⟩

end TypeIIL
