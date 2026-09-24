import proofs.MemoryPrediction.Measurement
import proofs.MemoryPrediction.RateBox

namespace MemoryPrediction
noncomputable section
open MeasureTheory ProbabilityTheory LowFounderPrediction

def feasibleMenu {Ω : Type*} (O : Fin 4000 → Ω → State) (ω : Ω) : Set Bool :=
  {b | inferredIndependent O ω = b}

theorem feasible_menu_error {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (O : Fin 4000 → Ω → State)
    (hO : ∀ i, Measurable (O i)) (hi : iIndepFun O μ)
    (b : Bool) (hlaw : ∀ i, μ.map (O i)=menuLaw b) :
    μ.real {ω | b ∉ feasibleMenu O ω} ≤ 1/2000 :=
  classification_error μ O hO hi b hlaw

theorem unmeasured_seven (b : Bool) : (19/20 : ℝ) ≤ sourceCDF (menuLaw b) 7 := by
  cases b
  · exact chronological_minimal_endpoints.2.2.1
  · have h : sourceCDF independentSource 6 ≤ sourceCDF independentSource 7 :=
      measureReal_mono (fun x hx => Nat.le_trans hx (by norm_num))
    exact chronological_minimal_endpoints.1.trans h

theorem six_not_uniform : sourceCDF (menuLaw false) 6 < (19/20 : ℝ) :=
  chronological_minimal_endpoints.2.2.2 6 (by norm_num)

def contrastingRates : Rates where
  bS := 1/10
  dS := 1/20
  qS := 1/250
  bR := 501/5000
  dR := 501/10000
  qR := 3/500
  bS_nonneg := by norm_num
  dS_nonneg := by norm_num
  qS_nonneg := by norm_num
  bR_nonneg := by norm_num
  dR_nonneg := by norm_num
  qR_nonneg := by norm_num

theorem safe_class_nontrivial : demographicBox contrastingRates ∧
    contrastingRates.bS ≠ contrastingRates.bR ∧ contrastingRates.dS ≠ contrastingRates.dR := by
  norm_num [demographicBox,contrastingRates]

end
end MemoryPrediction
