import proofs.IrrRAFEnumeration.SATSyntax

namespace IrrRAFEnumeration.SATSource

open Complexity SAT

abbrev SyntaxBitState := SyntaxState × Option Bool

def pairToken : Bool → Bool → EncToken
  | false, false => .bit false
  | true, true => .bit true
  | false, true => .litSep
  | true, false => .clauseSep

def syntaxBitStep (q : SyntaxBitState) (b : Bool) : SyntaxBitState :=
  match q.2 with
  | none => (q.1, some b)
  | some a => (syntaxStep q.1 (pairToken a b), none)

def syntaxFinish (q : SyntaxBitState) : Bool :=
  match q.2 with
  | none => syntaxTokens q.1 []
  | some _ => false

def syntaxBits : SyntaxBitState → List Bool → Bool
  | q, [] => syntaxFinish q
  | q, b :: bs => syntaxBits (syntaxBitStep q b) bs

theorem syntaxBits_tokenize (z : List Bool) (q : SyntaxState) :
    syntaxBits (q, none) z =
      match tokenize? z with
      | none => false
      | some toks => syntaxTokens q toks := by
  cases z with
  | nil => rfl
  | cons a zs =>
    cases zs with
    | nil => rfl
    | cons b bs =>
      have ih := syntaxBits_tokenize bs (syntaxStep q (pairToken a b))
      cases a <;> cases b <;> cases ht : tokenize? bs <;>
        simpa [syntaxBits, syntaxBitStep, pairToken, tokenize?, ht, syntaxTokens] using ih
termination_by z.length

theorem syntaxBits_eq_decode (z : List Bool) :
    syntaxBits ((.empty, true), none) z = (CNF.decode? z).isSome := by
  rw [syntaxBits_tokenize]
  exact syntaxAccepts_eq_decode z

end IrrRAFEnumeration.SATSource
