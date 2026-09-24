import proofs.FiniteReservoir.MaterialGenerator
import proofs.FiniteCopyReactor.MaterialPulse

namespace FiniteReservoir
noncomputable section
open Classical ProductiveRecovery RandomViability.Binding FiniteCopy
open scoped NNReal

def materialModel (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ)) :=
  model V M p hV (fun N => resourceGood N V)

theorem material_total (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ))
    (X : BoxState V M) : (materialModel V M p hV).total X ≤ 3000*(V:ℝ) :=
  model_total V M p hV _ (fun _ h => h) X

def materialKernel (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ)) :=
  (materialModel V M p hV).uniformize (3000*(V:ℝ)) (by positivity)
    (material_total V M p hV)

theorem material_foster (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ))
    (X : BoxState V M) :
    (materialModel V M p hV).generator (fun Y => resourcePotential V (boxCounts Y.1)) X ≤
      4*resourceSource V := by
  by_cases h : resourceGood (boxCounts X.1) V
  · rw [show (materialModel V M p hV).generator _ X = _ from
      model_inside V M p hV (fun N => resourceGood N V) X h h (resourcePotential V)]
    rw [resource_potential_generator]
    have hh := stopped_resource_foster V (1/500000000) (1/10) p.release hV
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith [p.release_lower]) (by linarith [p.release_upper]) X.1
    rw [stopped_generator_inside V (1/500000000) (1/10) p.release hV
      (by norm_num) (by norm_num) (by linarith [p.release_lower]) X.1 _ h] at hh
    exact hh
  · rw [show (materialModel V M p hV).generator _ X = 0 from
      model_outside V M p hV _ X h _]
    unfold resourceSource
    positivity

theorem material_exit_probability (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ))
    (t : ℝ≥0) (X : BoxState V M) :
    (materialKernel V M p hV).poissonized ((3000:ℝ≥0)*V*t)
      (FiniteKernel.eventIndicator {Y | ¬resourceGood (boxCounts Y.1) V}) X ≤
      resourcePotential V (boxCounts X.1)+(t:ℝ)*(4*resourceSource V) := by
  have h := (materialModel V M p hV).uniformized_event_bound ((3000:ℝ≥0)*V) t
    (by change 0 < (3000:ℝ)*(V:ℝ); positivity) (material_total V M p hV)
    {Y | ¬resourceGood (boxCounts Y.1) V} (fun Y => resourcePotential V (boxCounts Y.1))
    1 (4*resourceSource V) (fun Y => resourcePotential_nonneg V (boxCounts Y.1))
    (fun Y hY => resourcePotential_exit V (boxCounts Y.1) hY)
    (material_foster V M p hV) X
  simpa only [one_mul,materialKernel,NNReal.coe_mul,NNReal.coe_natCast,NNReal.coe_ofNat] using h

theorem prepared_material_exit (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ))
    (X : BoxState V M) (h : ∀ side,(24/25)*(V:ℝ) ≤ unitObs side (boxCounts X.1) ∧
      unitObs side (boxCounts X.1) ≤ (51/50)*(V:ℝ)) :
    (materialKernel V M p hV).poissonized ((3000:ℝ≥0)*V*4)
      (FiniteKernel.eventIndicator {Y | ¬resourceGood (boxCounts Y.1) V}) X ≤
      FiniteCopyReactor.materialExitError V := by
  have hh := material_exit_probability V M p hV 4 X
  have hp := FiniteCopyReactor.prepared_resource_potential (boxCounts X.1) V h
  norm_num only [NNReal.coe_ofNat] at hh
  unfold FiniteCopyReactor.materialExitError resourceSource at *
  nlinarith

end
end FiniteReservoir
