import proofs.CompositionalMemory.RationalPolynomialReplay

namespace CompositionalMemory

/-- Compact storage only. Parsed values still undergo the full polynomial
identity and inequality checks; parsing is not a proof oracle. -/
def decodeRationalToken (token : String) : ℚ :=
  match token.splitOn "/" with
  | [a,b] => (a.toInt?.getD 0 : ℚ)/(b.toNat?.getD 1 : ℚ)
  | _ => 0

def decodeRationals (data : String) : List ℚ := (data.splitOn ",").map decodeRationalToken

end CompositionalMemory
