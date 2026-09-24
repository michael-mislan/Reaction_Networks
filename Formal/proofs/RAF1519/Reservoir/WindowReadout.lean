import proofs.RAF1519.Reservoir.FunctionalReadout

namespace RAF1519.Reservoir
noncomputable section
open MeasureTheory Set
open scoped BigOperators

theorem finite_window_readout {n : ℕ} (q : Fin n → ℝ) (hq : ∑ i, q i=1)
    (hpos : ∀ i, 0 < q i) (X : ℝ → Community n) (a b : ℝ)
    (hX : ∀ t ∈ uIcc a b, HasDerivAt X (communityField q (X t)) t) :
    (∫ t in a..b, communityUptake (X t)) = totalConsumers (X b)-totalConsumers (X a)+
      (1/2)*(∫ t in a..b, totalConsumers (X t))+
      (∫ t in a..b, (totalConsumers (X t))^2)+
      (∫ t in a..b, variance q (normalizedDeviation q (X t))) := by
  have hc := HasDerivAt.continuousOn hX
  have hS : Continuous (fun x : Community n => totalConsumers x) := by unfold totalConsumers; fun_prop
  have hJ : Continuous (@communityUptake n) := by unfold communityUptake totalConsumers; fun_prop
  have hW : Continuous (fun x : Community n => variance q (normalizedDeviation q x)) := by
    unfold variance normalizedDeviation totalConsumers
    fun_prop
  have iS : IntervalIntegrable (fun t => totalConsumers (X t)) volume a b := (hS.comp_continuousOn hc).intervalIntegrable (μ := volume)
  have iJ : IntervalIntegrable (fun t => communityUptake (X t)) volume a b := (hJ.comp_continuousOn hc).intervalIntegrable (μ := volume)
  have iW : IntervalIntegrable (fun t => variance q (normalizedDeviation q (X t))) volume a b := (hW.comp_continuousOn hc).intervalIntegrable (μ := volume)
  have iQ : IntervalIntegrable (fun t => (totalConsumers (X t))^2) volume a b := ((hS.pow 2).comp_continuousOn hc).intervalIntegrable (μ := volume)
  have hd : ∀ t ∈ uIcc a b, HasDerivAt (fun t => totalConsumers (X t))
      (communityUptake (X t)-(1/2)*totalConsumers (X t)-(totalConsumers (X t))^2-
        variance q (normalizedDeviation q (X t))) t := by
    intro t ht
    convert totalConsumers_deriv X _ t (hX t ht) using 1
    linarith [transient_uptake q (X t) hq hpos]
  have hf := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (((iJ.sub (iS.const_mul (1/2))).sub iQ).sub iW)
  rw [intervalIntegral.integral_sub ((iJ.sub (iS.const_mul (1/2))).sub iQ) iW,
    intervalIntegral.integral_sub (iJ.sub (iS.const_mul (1/2))) iQ,
    intervalIntegral.integral_sub iJ (iS.const_mul (1/2)), intervalIntegral.integral_const_mul] at hf
  linarith

theorem reservoir_window_readout {n : ℕ} (q : Fin n → ℝ) (X : ℝ → Community n) (a b : ℝ)
    (hX : ∀ t ∈ uIcc a b, HasDerivAt X (communityField q (X t)) t) :
    (∫ t in a..b, communityUptake (X t)) =
      (1/20)*(∫ t in a..b, 1-X t (.inl 4))-(X b (.inl 4)-X a (.inl 4)) := by
  have hc := HasDerivAt.continuousOn hX
  have hJ : Continuous (@communityUptake n) := by unfold communityUptake totalConsumers; fun_prop
  have iJ : IntervalIntegrable (fun t => communityUptake (X t)) volume a b := (hJ.comp_continuousOn hc).intervalIntegrable (μ := volume)
  have hR : Continuous (fun x : Community n => (1:ℝ)-x (.inl 4)) := by fun_prop
  have iR : IntervalIntegrable (fun t => 1-X t (.inl 4)) volume a b := (hR.comp_continuousOn hc).intervalIntegrable (μ := volume)
  have hd : ∀ t ∈ uIcc a b, HasDerivAt (fun t => X t (.inl 4))
      ((1/20)*(1-X t (.inl 4))-communityUptake (X t)) t := by
    intro t ht
    exact hasDerivAt_pi.1 (hX t ht) (.inl 4)
  have hf := intervalIntegral.integral_eq_sub_of_hasDerivAt hd ((iR.const_mul (1/20)).sub iJ)
  rw [intervalIntegral.integral_sub (iR.const_mul (1/20)) iJ, intervalIntegral.integral_const_mul] at hf
  linarith

end
end RAF1519.Reservoir

