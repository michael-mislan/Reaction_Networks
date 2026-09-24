import proofs.MicrobialFunctionAssay.Certificate

namespace MicrobialFunctionAssay

theorem precision_gain_identity (e s r f loss J H eps1 eps2 : ℝ) :
    (f-loss-s*(J-r)-H-e*eps1-eps2) -
      (f-loss-s*(J-r)-H-s*eps1-eps2) = (s-e)*eps1 := by ring

/-- Actual total-record reserve-facet comparison with tight initial total,
zero first formation/loss, and equal second formation and loss. -/
theorem reserve_precision_tradeoff (e s r f loss J H eps1 eps2 : ℝ) :
    (f-loss-(s-e)*(J-r)-H-e*eps1-eps2) -
      (f-loss-H-s*eps1-eps2) = (s-e)*(eps1-(J-r)) := by ring

theorem wash_curve (a : ℝ) :
    lower (29/5) (17/10+21/10*a) 10 (1/20) (9/10) 2 (1/5) =
      max 0 (21/10*a-41/100) := by
  have h0 : 0 ≤ max 0 (21/10*a-41/100) := le_max_left _ _
  have hx : 21/10*a-41/100 ≤ max 0 (21/10*a-41/100) := le_max_right _ _
  apply le_antisymm
  · unfold lower
    repeat' apply max_le
    all_goals linarith
  · apply max_le
    · exact le_max_left _ _
    · have hf : (1/20)*(29/5)+(17/10+21/10*a)-(1/20)*10-
          ((9/10)-(1/20))*2-(1/5) ≤
          lower (29/5) (17/10+21/10*a) 10 (1/20) (9/10) 2 (1/5) := by
        unfold lower
        exact (le_max_left _ _).trans ((le_max_right _ _).trans
          ((le_max_right _ _).trans (le_max_right _ _)))
      linarith

theorem unwashed_value :
    lower (29/5) (11/2) 10 (9/10) (9/10) 2 (1/5) = 38/25 := by
  norm_num [lower]

theorem improvement_criterion (a : ℝ) :
    (38/25 < lower (29/5) (17/10+21/10*a) 10 (1/20) (9/10) 2 (1/5)) ↔
    193/210 < a := by
  rw [wash_curve a, lt_max_iff]
  norm_num
  constructor <;> intro h <;> linarith

end MicrobialFunctionAssay
