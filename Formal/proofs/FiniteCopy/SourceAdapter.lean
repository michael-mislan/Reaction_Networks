import proofs.FiniteCopy.Source
import proofs.CoreCouplingCAC.Reduction

namespace FiniteCopy
open CoreCouplingCAC Set

noncomputable def sourceRates : Rates := ⟨6,27,16,2,1/100000,1/10000⟩
noncomputable def pointOfState (s : State) : Point := ![s.A,s.B,s.z,s.H]

theorem limiting_drift_binding (s : State) :
    drift (1/100000) 0 (pointOfState s) =
      ![fA sourceRates s.A s.B s.z,fB sourceRates s.A s.B s.z,
        fZ sourceRates s.A s.B s.z s.H,fH sourceRates s.z s.H] := by
  rw [drift_formula]
  ext i
  fin_cases i <;> norm_num [pointOfState, Matrix.cons_val_two, Matrix.cons_val_three, sourceRates, fA, fB, fZ, fH]
  ring

theorem stationary_drift_zero (s : State) (h : Stationary sourceRates s) :
    drift (1/100000) 0 (pointOfState s) = 0 := by
  rw [limiting_drift_binding]
  rcases h with ⟨hA,hB,hZ,hH⟩
  ext i
  fin_cases i <;> simp [hA,hB,hZ,hH]

lemma source_residual_continuous (lo hi : ℝ) (hl : -2 < lo) :
    ContinuousOn (CoreCouplingCAC.residual sourceRates) (Icc lo hi) := by
  intro x hx
  apply ContinuousAt.continuousWithinAt
  unfold CoreCouplingCAC.residual reducedA reducedB reducedK sourceRates
  have hz : ∀ x ∈ Icc lo hi, x+2 ≠ 0 := by
    intro x hx
    linarith [hx.1]
  fun_prop (disch := first | exact hz x hx | norm_num)

theorem low_source_root :
    ∃ z ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000),
      Stationary sourceRates (lift sourceRates z) := by
  have hl : CoreCouplingCAC.residual sourceRates (99579401232/100000000000) ≤ 0 := by
    norm_num [CoreCouplingCAC.residual, reducedA, reducedB, reducedK, sourceRates]
  have hr : 0 ≤ CoreCouplingCAC.residual sourceRates (99579401233/100000000000) := by
    norm_num [CoreCouplingCAC.residual, reducedA, reducedB, reducedK, sourceRates]
  obtain ⟨z,hz,hroot⟩ := intermediate_value_Icc (by norm_num :
      (99579401232/100000000000 : ℝ) ≤ 99579401233/100000000000)
    (source_residual_continuous _ _ (by norm_num)) ⟨hl,hr⟩
  refine ⟨z,hz,lift_stationary _ z (by linarith [hz.1]) (by norm_num [sourceRates]) ?_⟩
  exact hroot

theorem high_source_root :
    ∃ z ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000),
      Stationary sourceRates (lift sourceRates z) := by
  have hl : CoreCouplingCAC.residual sourceRates (297636724376/100000000000) ≤ 0 := by
    norm_num [CoreCouplingCAC.residual, reducedA, reducedB, reducedK, sourceRates]
  have hr : 0 ≤ CoreCouplingCAC.residual sourceRates (297636724377/100000000000) := by
    norm_num [CoreCouplingCAC.residual, reducedA, reducedB, reducedK, sourceRates]
  obtain ⟨z,hz,hroot⟩ := intermediate_value_Icc (by norm_num :
      (297636724376/100000000000 : ℝ) ≤ 297636724377/100000000000)
    (source_residual_continuous _ _ (by norm_num)) ⟨hl,hr⟩
  refine ⟨z,hz,lift_stationary _ z (by linarith [hz.1]) (by norm_num [sourceRates]) ?_⟩
  exact hroot

end FiniteCopy



