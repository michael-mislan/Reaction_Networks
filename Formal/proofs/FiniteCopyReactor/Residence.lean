import proofs.FiniteCopyReactor.ResidencePotential

namespace FiniteCopyReactor
noncomputable section
open ProductiveRecovery RandomViability.Binding FiniteCopy Classical
open scoped NNReal

def residenceActive (V : ℕ) (N : BoxCounts V) : Prop :=
  resourceGood (boxCounts N) V ∧ (V:ℝ)/20 < weightedCount (boxCounts N)

def residenceModel (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ)) (hr : 0 ≤ r) (hd : 0 ≤ d) :
    FiniteJumpModel (BoxCounts V) CompetitionChannel where
  next N j := boxNext V N (competitionBase j)
  rate N j := if residenceActive V N then
    competitionRate (boxCounts N) V (1/500000000) (1/10) r d j else 0
  nonneg N j := by
    split_ifs
    · exact competitionRate_nonneg (boxCounts N) V (1/500000000) (1/10) r d hV
        (by norm_num) (by norm_num) hr hd j
    · rfl

theorem residence_model_generator (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ))
    (hr : 0 ≤ r) (hd : 0 ≤ d) (f : Counts → ℝ) (N : BoxCounts V) :
    (residenceModel V r d hV hr hd).generator (fun X => f (boxCounts X)) N =
      if residenceActive V N then competitionGenerator (boxCounts N) V
        (1/500000000) (1/10) r d f else 0 := by
  by_cases h : residenceActive V N
  · simp only [FiniteJumpModel.generator,residenceModel,if_pos h,competitionGenerator]
    apply Finset.sum_congr rfl
    intro j _
    rw [boxNext_exact V N (competitionBase j) h.1]
    rfl
  · simp only [FiniteJumpModel.generator,residenceModel,if_neg h,zero_mul,Finset.sum_const_zero]

theorem residence_total_bound (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ))
    (hr : 0 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25) (N : BoxCounts V) :
    (residenceModel V r d hV hr hd).total N ≤ 3000*(V:ℝ) := by
  by_cases h : residenceActive V N
  · have hh := material_total_bound V r d hV hr hr' hd hd' N
    simpa only [FiniteJumpModel.total,residenceModel,materialModel,if_pos h,if_pos h.1] using hh
  · simp only [FiniteJumpModel.total,residenceModel,if_neg h,Finset.sum_const_zero]
    positivity

def residenceKernel (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ))
    (hr : 0 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25) :
    FiniteKernel (BoxCounts V) :=
  (residenceModel V r d hV hr hd).uniformize (3000*(V:ℝ)) (by positivity)
    (residence_total_bound V r d hV hr hr' hd hd')

theorem residence_foster (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ))
    (hr : 19 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25) (N : BoxCounts V) :
    (residenceModel V r d hV (by linarith) hd).generator
      (fun X => residencePotential V (boxCounts X)) N ≤
        (3000*(V:ℝ))*Real.exp (-3*(V:ℝ)/5000+9/500) := by
  rw [residence_model_generator]
  split_ifs with h
  · exact residence_potential_generator (boxCounts N) V r d hV hr hr' hd hd' h.1
  · positivity

/-- A downward exit is retained by the stopped law. Material exits must still
be paid when transporting this event to unrestricted trajectories. -/
theorem residence_lower_exit (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ))
    (hr : 19 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25)
    (t : ℝ≥0) (N : BoxCounts V) (hN : (3/50)*(V:ℝ) ≤ weightedCount (boxCounts N)) :
    (residenceKernel V r d hV (by linarith) hr' hd hd').poissonized ((3000:ℝ≥0)*V*t)
      (FiniteKernel.eventIndicator {X | weightedCount (boxCounts X) ≤ (V:ℝ)/20}) N ≤
      (1+3000*(V:ℝ)*(t:ℝ)*Real.exp (9/500))*Real.exp (-(V:ℝ)/10000) := by
  have h := (residenceModel V r d hV (by linarith) hd).uniformized_event_bound
    ((3000:ℝ≥0)*V) t (by change 0 < (3000:ℝ)*(V:ℝ); positivity)
    (residence_total_bound V r d hV (by linarith) hr' hd hd')
    {X | weightedCount (boxCounts X) ≤ (V:ℝ)/20}
    (fun X => residencePotential V (boxCounts X)) (Real.exp (-(V:ℝ)/2000))
    ((3000*(V:ℝ))*Real.exp (-3*(V:ℝ)/5000+9/500))
    (fun X => residence_potential_nonneg V (boxCounts X))
    (fun X hX => (Real.exp_le_exp.mpr (by
      change weightedCount (boxCounts X) ≤ (V:ℝ)/20 at hX
      linarith : -(V:ℝ)/2000 ≤ -weightedCount (boxCounts X)/100)).trans (le_max_left _ _))
    (residence_foster V r d hV hr hr' hd hd') N
  have hi : residencePotential V (boxCounts N) = Real.exp (-3*(V:ℝ)/5000) := by
    apply max_eq_right
    apply Real.exp_le_exp.mpr
    linarith
  rw [hi] at h
  have he : Real.exp (-3*(V:ℝ)/5000)+(t:ℝ)*(3000*(V:ℝ)*Real.exp (-3*(V:ℝ)/5000+9/500)) =
      Real.exp (-(V:ℝ)/2000)*((1+3000*(V:ℝ)*(t:ℝ)*Real.exp (9/500))*Real.exp (-(V:ℝ)/10000)) := by
    rw [Real.exp_add]
    have hh : Real.exp (-(V:ℝ)/2000)*Real.exp (-(V:ℝ)/10000) = Real.exp (-3*(V:ℝ)/5000) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [← hh]
    ring
  rw [he] at h
  exact le_of_mul_le_mul_left h (Real.exp_pos _)

end
end FiniteCopyReactor
