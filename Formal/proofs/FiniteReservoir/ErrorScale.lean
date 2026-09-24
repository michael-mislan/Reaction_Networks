import proofs.FiniteReservoir.PulseCycle
import proofs.FiniteCopyReactor.LogarithmicScale

namespace FiniteReservoir
noncomputable section

/-- Equality of numerical error budgets, not identification of the two process laws. -/
theorem one_cycle_error_eq (V : ℝ) : oneCycleError V=FiniteCopyReactor.oneCycleError V := rfl

theorem one_cycle_error_small (V : ℝ) (hV : 200000000000 ≤ V) : oneCycleError V ≤ 1/10000 :=
  FiniteCopyReactor.one_cycle_error_small V hV

theorem one_cycle_single_exponential (V : ℝ) (hV : 200000000000 ≤ V) :
    oneCycleError V ≤ 101*Real.exp (-V/10000000000) :=
  FiniteCopyReactor.one_cycle_single_exponential V hV

theorem logarithmic_volume_error (m : ℕ) (hm : 0 < m) (δ : ℝ) (hδ : 0 < δ) :
    (m:ℝ)*oneCycleError (FiniteCopyReactor.logarithmicVolume m δ) ≤ δ :=
  FiniteCopyReactor.logarithmic_volume_error m hm δ hδ

end
end FiniteReservoir
