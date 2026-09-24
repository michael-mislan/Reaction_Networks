import Mathlib

namespace DynamicSequestration

/-- Literal phosphorylation weights cancel binding and dissociation. -/
theorem phosphorylation_balance
    (v1 v2 v3 w1 w2 w3 b2 b3 u2 u3 a1 a2 a3 h1 h2 h3 : ℝ) :
    (v1 - b2 + u2 - a1 + h1 + w2)
      + 2 * (v2 - b3 + u3 - a2 + h2 + w3)
      + 3 * (v3 - a3 + h3) + (b2 - u2 - v2)
      + 2 * (b3 - u3 - v3) + (a1 - h1 - w1)
      + 2 * (a2 - h2 - w2) + 3 * (a3 - h3 - w3)
      = v1 + v2 + v3 - w1 - w2 - w3 := by
  ring

/-- Integration of an individual periodic cumulative-pool balance. -/
theorem periodic_current_equality (forward backward : ℝ)
    (integrated_balance : forward - backward = 0) : forward = backward := by
  linarith

end DynamicSequestration
