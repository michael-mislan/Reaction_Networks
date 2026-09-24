import proofs.RAF1519.Refinement.HoldingObservable
import proofs.RAF1519.Refinement.HoldingPrimitive
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace RAF1519.Refinement
noncomputable section
open Classical MeasureTheory

theorem holdingObservable_integral (h v : ℕ → ℝ) (hh : ∀ i, 0 ≤ h i)
    (K : ℕ) (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hK : b < holdingClock h K) :
    (∫ t in a..b, v (holdingIndex h t)) =
      holdingPrimitive h v K b-holdingPrimitive h v K a := by
  apply intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab
    (holdingPrimitive_continuous h v K).continuousOn _
    (holdingObservable_integrable h v hh K a b ha hab hK)
  intro t ht
  have hi := holdingIndex_before_prefix h hh K t (ha.trans ht.1.le) (ht.2.le.trans_lt hK)
  exact (holdingPrimitive_right_derivative h v hh K _ hi.1 t hi.2.1 hi.2.2).mono
    Set.Ioi_subset_Ici_self

end
end RAF1519.Refinement
