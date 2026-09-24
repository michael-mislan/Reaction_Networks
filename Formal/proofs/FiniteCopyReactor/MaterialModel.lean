import proofs.FiniteCopyReactor.Source
import proofs.RandomViability.BindingCompetitionResourceTails

namespace FiniteCopyReactor
noncomputable section
open ProductiveRecovery RandomViability.Binding FiniteCopy Classical
open scoped BigOperators NNReal

/-- The literal twenty-label process, stopped only on material exit.
The exiting count state is retained, with zero subsequent rates. -/
def materialModel (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ)) (hr : 0 ≤ r) (hd : 0 ≤ d) :
    FiniteJumpModel (BoxCounts V) CompetitionChannel where
  next N j := boxNext V N (competitionBase j)
  rate N j := if resourceGood (boxCounts N) V then
    competitionRate (boxCounts N) V (1/500000000) (1/10) r d j else 0
  nonneg N j := by
    split_ifs
    · exact competitionRate_nonneg (boxCounts N) V (1/500000000) (1/10) r d hV
        (by norm_num) (by norm_num) hr hd j
    · rfl

theorem material_model_inside (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ)) (hr : 0 ≤ r) (hd : 0 ≤ d)
    (N : BoxCounts V) (f : Counts → ℝ) (h : resourceGood (boxCounts N) V) :
    (materialModel V r d hV hr hd).generator (fun X => f (boxCounts X)) N =
      competitionGenerator (boxCounts N) V (1/500000000) (1/10) r d f := by
  simp only [FiniteJumpModel.generator,materialModel,if_pos h,competitionGenerator]
  apply Finset.sum_congr rfl
  intro j _
  rw [boxNext_exact V N (competitionBase j) h]
  rfl

theorem material_model_outside (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ)) (hr : 0 ≤ r) (hd : 0 ≤ d)
    (N : BoxCounts V) (f : BoxCounts V → ℝ) (h : ¬resourceGood (boxCounts N) V) :
    (materialModel V r d hV hr hd).generator f N = 0 := by
  simp only [FiniteJumpModel.generator,materialModel,if_neg h,zero_mul,Finset.sum_const_zero]

theorem material_total_bound (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ))
    (hr : 0 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25) (N : BoxCounts V) :
    (materialModel V r d hV hr hd).total N ≤ 3000*(V:ℝ) := by
  by_cases h : resourceGood (boxCounts N) V
  · simp only [FiniteJumpModel.total,materialModel,if_pos h]
    apply competition_total_rate_bound (boxCounts N) V (1/500000000) (1/10) r d hV
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hr (by linarith) hd (by linarith)
    intro i
    linarith [resource_count_cap (boxCounts N) V h i]
  · simp only [FiniteJumpModel.total,materialModel,if_neg h,Finset.sum_const_zero]
    positivity

def materialKernel (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ))
    (hr : 0 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25) :
    FiniteKernel (BoxCounts V) :=
  (materialModel V r d hV hr hd).uniformize (3000*(V:ℝ)) (by positivity)
    (material_total_bound V r d hV hr hr' hd hd')

theorem material_resource_foster (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ))
    (hr : 0 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (N : BoxCounts V) :
    (materialModel V r d hV hr hd).generator (fun X => resourcePotential V (boxCounts X)) N ≤
      4*resourceSource V := by
  by_cases h : resourceGood (boxCounts N) V
  · rw [material_model_inside V r d hV hr hd N _ h,competition_resource_potential_generator]
    have hh := stopped_resource_foster V (1/500000000) (1/10) r hV
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hr (by linarith) N
    rw [stopped_generator_inside V (1/500000000) (1/10) r hV
      (by norm_num) (by norm_num) hr N _ h] at hh
    exact hh
  · rw [material_model_outside V r d hV hr hd N _ h]
    unfold resourceSource
    positivity

theorem material_exit_probability (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ))
    (hr : 0 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25)
    (t : ℝ≥0) (N : BoxCounts V) :
    (materialKernel V r d hV hr hr' hd hd').poissonized ((3000:ℝ≥0)*V*t)
      (FiniteKernel.eventIndicator {X | ¬resourceGood (boxCounts X) V}) N ≤
        resourcePotential V (boxCounts N)+(t:ℝ)*(4*resourceSource V) := by
  have h := (materialModel V r d hV hr hd).uniformized_event_bound
    ((3000:ℝ≥0)*V) t (by change 0 < (3000:ℝ)*(V:ℝ); positivity)
    (material_total_bound V r d hV hr hr' hd hd')
    {X | ¬resourceGood (boxCounts X) V} (fun X => resourcePotential V (boxCounts X))
    1 (4*resourceSource V) (fun X => resourcePotential_nonneg V (boxCounts X))
    (fun X hX => resourcePotential_exit V (boxCounts X) hX)
    (material_resource_foster V r d hV hr hr' hd) N
  simpa only [one_mul,materialKernel,NNReal.coe_mul,NNReal.coe_natCast,NNReal.coe_ofNat] using h

end
end FiniteCopyReactor
