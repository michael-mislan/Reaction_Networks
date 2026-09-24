import proofs.FiniteReservoir.MissionExample
import proofs.FiniteReservoir.ThermochemicalModel
import proofs.FiniteReservoir.MeteredFood

namespace FiniteReservoir
noncomputable section
open Classical ProductiveRecovery FiniteCopyReactor MeasureTheory ProbabilityTheory RandomViability.Binding
open scoped ENNReal

/-- Explicit mission confidence, output demands and every-prefix finite-bath tolerance on one physical law. -/
theorem finite_reservoir_repeated_operation (m : ℕ) (hm : 0 < m) (δ rho QI QX : ℝ) (hd : 0 < δ) (hr : 0 < rho)
    (policy : ReturnedHistory (reservoirSize (designVolume m δ QI QX) m rho) → Intervention) :
    let V := designVolume m δ QI QX
    let R := reservoirSize V m rho
    let N : CountState R := (![0,0,V,0,0,0],pureFuel R)
    let params := pureParameters R (reservoir_size_positive V m rho) 20 (1/50)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    ENNReal.ofReal (1-δ) ≤
      fullHistoryKernel (returnedHistoryStep R N V params
        (by exact_mod_cast (show 0 < V by have := design_volume_scale m δ QI QX; dsimp [V]; omega)) policy) m []
        (DesignedSuccess R N V m policy rho QI QX) :=
  pure_inverse_design m hm δ rho QI QX hd hr policy

end
end FiniteReservoir
