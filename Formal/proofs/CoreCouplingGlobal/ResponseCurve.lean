import proofs.CoreCouplingGlobal.EquilibriumBarrier

namespace CoreCouplingGlobal
open CoreCouplingCAC

/-- On the zero-fork-residual curve, stationary compatibility is the response gap
times a positive factor. This links equilibrium root signs to energy geometry. -/
theorem response_curve_factorization (e z : ℝ) (he : 0 ≤ e) (hu : e ≤ 1/50000)
    (hB : 2 ≤ reducedB (varyRates e) z) (hB' : reducedB (varyRates e) z ≤ 34)
    (hz : z+2 ≠ 0) :
    residual (varyRates e) z =
      (reducedA (varyRates e) z-responseA e (reducedB (varyRates e) z))*
      (1+e*(reducedA (varyRates e) z+responseA e (reducedB (varyRates e) z))) := by
  have hq := response_quadratic e (reducedB (varyRates e) z) he hu hB hB'
  have hb : (z+2)*reducedB (varyRates e) z = 60 := by
    dsimp [reducedB,varyRates,witnessRates]
    field_simp
    norm_num
  have ha : reducedA (varyRates e) z = z*reducedB (varyRates e) z+reducedK (varyRates e) z := rfl
  change 27-(1+e)*reducedB (varyRates e) z+reducedK (varyRates e) z+
    e*(reducedA (varyRates e) z)^2 = _
  nlinarith only [hq,hb,ha]

theorem response_curve_factor_positive (e z : ℝ) (he : 0 ≤ e) (hu : e ≤ 1/50000)
    (hB : 2 ≤ reducedB (varyRates e) z) (hB' : reducedB (varyRates e) z ≤ 34)
    (hA : 0 ≤ reducedA (varyRates e) z) :
    0 < 1+e*(reducedA (varyRates e) z+responseA e (reducedB (varyRates e) z)) := by
  have hbound := (response_bounds e (reducedB (varyRates e) z) he hu hB hB').1
  have hp := mul_nonneg he (show 0 ≤ reducedA (varyRates e) z+
    responseA e (reducedB (varyRates e) z)+1 by linarith)
  nlinarith

end CoreCouplingGlobal
