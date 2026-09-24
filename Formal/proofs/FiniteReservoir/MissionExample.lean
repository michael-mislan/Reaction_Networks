import proofs.FiniteReservoir.InverseDesign

namespace FiniteReservoir
noncomputable section
open Classical ProductiveRecovery FiniteCopyReactor MeasureTheory ProbabilityTheory RandomViability.Binding
open scoped ENNReal

def exampleV : ℕ := 200000000000
def exampleR : ℕ := 40000000000000
def exampleState : CountState exampleR := (![0,0,exampleV,0,0,0],pureFuel exampleR)
def exampleParameters : Parameters exampleR :=
  pureParameters exampleR (by norm_num [exampleR]) 20 (1/50)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem example_arithmetic :
    grossAllowance exampleV 100=(4000000000000:ℝ) ∧
    grossAllowance exampleV 100 ≤ (1/10)*(exampleR:ℝ) ∧
    (100:ℝ)*(Nat.ceil ((exampleV:ℝ)/56):ℝ)=357142857200 ∧
    (100:ℝ)*(Nat.ceil ((exampleV:ℝ)/1080):ℝ)=18518518600 := by
  norm_num [grossAllowance,exampleV,exampleR,Nat.ceil_eq_iff]

/-- Concrete same-event output, resource and every-prefix pure-bath tolerance. -/
theorem example_mission (policy : ReturnedHistory exampleR → Intervention) :
    ENNReal.ofReal (999979/1000000:ℝ) ≤
      fullHistoryKernel (returnedHistoryStep exampleR exampleState exampleV exampleParameters
        (by norm_num [exampleV]) policy) 100 []
        (DesignedSuccess exampleR exampleState exampleV 100 policy (1/10) 357142857200 18518518600) := by
  have hp := pure_hundred exampleR (by norm_num [exampleR]) policy
  apply hp.trans
  apply measure_mono
  intro h hh
  refine ⟨hh,?_,?_,?_⟩
  · rw [← example_arithmetic.2.2.1]
    exact hh.2.2.1
  · rw [← example_arithmetic.2.2.2]
    exact hh.2.2.2.1
  · intro tr b hb
    exact pure_prefix_tolerance tr (by norm_num [exampleR]) rfl 100 hh.1 (1/10)
      example_arithmetic.2.1 b hb

theorem loaded_hundred (R : ℕ) (hR : 0 < R) (policy : ReturnedHistory (2*R) → Intervention) :
    let V := 200000000000
    let N : CountState (2*R) := (![0,0,V,0,0,0],loadedFuel R)
    let params := loadedParameters R hR 20 (by norm_num) (by norm_num)
    ENNReal.ofReal (999979/1000000:ℝ) ≤
      fullHistoryKernel (returnedHistoryStep (2*R) N V params (by norm_num) policy) 100 []
        (OperationalSuccess (2*R) N V 100 policy) := by
  dsimp only
  have hb : (100:ℝ)*oneCycleError 200000000000 ≤ 21/1000000 := FiniteCopyReactor.hundred_sharp_budget
  have hN : Restart 200000000000 ![0,0,200000000000,0,0,0] := all_free_restart _
  convert finite_bath_budget (2*R) (![0,0,200000000000,0,0,0],loadedFuel R) 200000000000
    (loadedParameters R hR 20 (by norm_num) (by norm_num))
    (by norm_num) policy (by norm_num) hN 100 (21/1000000) hb using 1
  norm_num

end
end FiniteReservoir
