import proofs.Complexitylib.SAT.Verifier

namespace IrrRAFEnumeration.SATSource

open Complexity SAT

inductive RawKind where
  | empty | valid | invalid
  deriving DecidableEq, Repr

def pushRawKind (b : Bool) : RawKind → RawKind
  | .empty => .valid
  | .valid => if b then .valid else .invalid
  | .invalid => .invalid

/-- Abstract the reversed partial literal to three finite possibilities. -/
def rawKind : List Bool → RawKind
  | [] => .empty
  | b :: bs => pushRawKind b (rawKind bs)

theorem rawKind_eq_empty (bs : List Bool) : rawKind bs = .empty ↔ bs = [] := by
  cases bs with
  | nil => simp [rawKind]
  | cons b bs => cases h : rawKind bs <;> cases b <;> simp [rawKind, h, pushRawKind]

theorem rawKind_append_sign (bs : List Bool) (sign : Bool) :
    rawKind (bs ++ [sign]) = if bs.all id then .valid else .invalid := by
  induction bs with
  | nil => simp [rawKind, pushRawKind]
  | cons b bs ih =>
    cases b <;> cases h : bs.all id <;> simp [rawKind, ih, h, pushRawKind]

theorem rawKind_valid_iff (raw : List Bool) :
    rawKind raw = .valid ↔ (Lit.decodeRaw? raw.reverse).isSome = true := by
  cases hr : raw.reverse with
  | nil =>
    have hz : raw = [] := by simpa using congrArg List.reverse hr
    simp [hz, rawKind, Lit.decodeRaw?]
  | cons sign bs =>
    have hz : raw = bs.reverse ++ [sign] := by simpa using congrArg List.reverse hr
    rw [hz, rawKind_append_sign]
    simp [Lit.decodeRaw?, List.all_eq_true]

/-- The Boolean records whether the current clause has no finished literal. -/
abbrev SyntaxState := RawKind × Bool

def syntaxStep (q : SyntaxState) : EncToken → SyntaxState
  | .bit b => (pushRawKind b q.1, q.2)
  | .litSep => if q.1 = .valid then (.empty, false) else (.invalid, false)
  | .clauseSep => if q.1 = .empty then (.empty, true) else (.invalid, false)

def syntaxTokens : SyntaxState → List EncToken → Bool
  | q, [] => decide (q.1 = .empty) && q.2
  | q, tok :: toks => syntaxTokens (syntaxStep q tok) toks

theorem syntaxTokens_invalid (toks : List EncToken) (b : Bool) :
    syntaxTokens (.invalid, b) toks = false := by
  induction toks generalizing b with
  | nil => simp [syntaxTokens]
  | cons tok toks ih => cases tok <;> simp [syntaxTokens, syntaxStep, pushRawKind, ih]

theorem syntaxTokens_parser (toks : List EncToken) (raw : List Bool)
    (clause : Clause) (cnf : CNF) :
    syntaxTokens (rawKind raw, decide (clause = [])) toks =
      (parseTokensAux toks raw clause cnf).isSome := by
  induction toks generalizing raw clause cnf with
  | nil =>
    by_cases hr : raw = [] <;> by_cases hc : clause = [] <;>
      simp [syntaxTokens, parseTokensAux, rawKind_eq_empty, hr, hc]
  | cons tok toks ih =>
    cases tok with
    | bit b => simpa [syntaxTokens, syntaxStep, rawKind, parseTokensAux] using ih (b :: raw) clause cnf
    | litSep =>
      cases hd : Lit.decodeRaw? raw.reverse with
      | none =>
        have hr : rawKind raw ≠ .valid := by simpa [hd] using rawKind_valid_iff raw
        simp [syntaxTokens, syntaxStep, hr, syntaxTokens_invalid, parseTokensAux, hd]
      | some lit =>
        have hr : rawKind raw = .valid := (rawKind_valid_iff raw).mpr (by simp [hd])
        simpa [syntaxTokens, syntaxStep, hr, parseTokensAux, hd, rawKind] using ih [] (lit :: clause) cnf
    | clauseSep =>
      by_cases hr : raw = []
      · subst raw
        simpa [syntaxTokens, syntaxStep, rawKind, parseTokensAux] using ih [] [] (clause.reverse :: cnf)
      · have hk : rawKind raw ≠ .empty := by simpa [rawKind_eq_empty] using hr
        simp [syntaxTokens, syntaxStep, hk, syntaxTokens_invalid, parseTokensAux, hr]

def syntaxAccepts (z : List Bool) : Bool :=
  match tokenize? z with
  | none => false
  | some toks => syntaxTokens (.empty, true) toks

theorem syntaxAccepts_eq_decode (z : List Bool) :
    syntaxAccepts z = (CNF.decode? z).isSome := by
  cases ht : tokenize? z with
  | none => simp [syntaxAccepts, CNF.decode?, ht]
  | some toks =>
    simpa [syntaxAccepts, CNF.decode?, ht, rawKind] using syntaxTokens_parser toks [] [] []

end IrrRAFEnumeration.SATSource
