import proofs.FiniteReservoir.ResidencePotential

namespace FiniteReservoir
noncomputable section
open Classical ProductiveRecovery RandomViability.Binding FiniteCopy
open FiniteCopyReactor (residencePotential residence_potential_nonneg)
open scoped NNReal

def residenceModel (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ)) :=
  model V M p hV (fun N => resourceGood N V ∧ (V:ℝ)/20 < weightedCount N)

theorem residence_total (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ))
    (X : BoxState V M) : (residenceModel V M p hV).total X ≤ 3000*(V:ℝ) :=
  model_total V M p hV _ (fun _ h => h.1) X

def residenceKernel (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ)) :=
  (residenceModel V M p hV).uniformize (3000*(V:ℝ)) (by positivity)
    (residence_total V M p hV)

theorem residence_foster (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ))
    (X : BoxState V M) :
    (residenceModel V M p hV).generator (fun Y => residencePotential V (boxCounts Y.1)) X ≤
      (3000*(V:ℝ))*Real.exp (-3*(V:ℝ)/5000+9/500) := by
  by_cases h : resourceGood (boxCounts X.1) V ∧ (V:ℝ)/20 < weightedCount (boxCounts X.1)
  · rw [show (residenceModel V M p hV).generator _ X = _ from
      model_inside V M p hV _ X h h.1 (residencePotential V)]
    exact residence_potential_generator _ V p.release _ _ hV p.release_lower
      p.release_upper (parameters_box p X.2) h.1
  · rw [show (residenceModel V M p hV).generator _ X = 0 from
      model_outside V M p hV _ X h _]
    positivity

theorem residence_lower_exit (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ))
    (t : ℝ≥0) (N : BoxState V M) (hN : (3/50)*(V:ℝ) ≤ weightedCount (boxCounts N.1)) :
    (residenceKernel V M p hV).poissonized ((3000:ℝ≥0)*V*t)
      (FiniteKernel.eventIndicator {X | weightedCount (boxCounts X.1) ≤ (V:ℝ)/20}) N ≤
      (1+3000*(V:ℝ)*(t:ℝ)*Real.exp (9/500))*Real.exp (-(V:ℝ)/10000) := by
  have h := (residenceModel V M p hV).uniformized_event_bound
    ((3000:ℝ≥0)*V) t (by change 0 < (3000:ℝ)*(V:ℝ); positivity)
    (residence_total V M p hV)
    {X | weightedCount (boxCounts X.1) ≤ (V:ℝ)/20}
    (fun X => residencePotential V (boxCounts X.1)) (Real.exp (-(V:ℝ)/2000))
    ((3000*(V:ℝ))*Real.exp (-3*(V:ℝ)/5000+9/500))
    (fun X => residence_potential_nonneg V (boxCounts X.1))
    (fun X hX => (Real.exp_le_exp.mpr (by
      change weightedCount (boxCounts X.1) ≤ (V:ℝ)/20 at hX
      linarith : -(V:ℝ)/2000 ≤ -weightedCount (boxCounts X.1)/100)).trans (le_max_left _ _))
    (residence_foster V M p hV) N
  have hi : residencePotential V (boxCounts N.1) = Real.exp (-3*(V:ℝ)/5000) := by
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
end FiniteReservoir
