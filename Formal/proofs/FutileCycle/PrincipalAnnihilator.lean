import proofs.FutileCycle.NegativeWitness

namespace FutileCycle

def negativeMasked (m : Fin 64) : Matrix (Fin 6) (Fin 6) ℤ :=
  fun i j => if m.val.testBit i.val && m.val.testBit j.val then negativeMatrix i j else 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000 in
/-- Pilot only: a maximal proper restriction with both marginal two-cycles. -/
theorem negativeMasked_pilot :
    (negativeMasked 62)^2 * (negativeMasked 62+1)^4 * (negativeMasked 62+2)^2 = 0 := by
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
theorem negativeMasked_annihilator : ∀ m : Fin 64, m ≠ 31 → m ≠ 63 →
    (negativeMasked m)^2 * (negativeMasked m+1)^4 * (negativeMasked m+2)^2 = 0 := by
  decide

end FutileCycle
