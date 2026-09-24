import proofs.FiniteReservoir.Thermochemistry

namespace FiniteReservoir
noncomputable section

/-- The exact potential identity specializes directly to the literal source used in the mission theorem. -/
theorem model_detailed_balance (u w x c1 c2 z f p : ℕ) (V r d R : ℝ)
    (hV : 0 < V) (hd : 0 < d) (hR : 0 < R) :
    rate (drivenBefore u w x c1 c2 z f p) V r d R (.inr 0) /
      rate (drivenAfter u w x c1 c2 z f p) V r d R (.inr 1)=
    Real.exp (-(totalPotential (drivenAfter u w x c1 c2 z f p) V R R-
      totalPotential (drivenBefore u w x c1 c2 z f p) V R R)) :=
  driven_detailed_balance u w x c1 c2 z f p V r d R R hV hd hR hR

end
end FiniteReservoir
