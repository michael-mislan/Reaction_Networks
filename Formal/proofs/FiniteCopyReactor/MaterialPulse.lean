import proofs.FiniteCopyReactor.PulseBox

namespace FiniteCopyReactor
noncomputable section
open ProductiveRecovery RandomViability.Binding FiniteCopy Classical
open scoped BigOperators NNReal

def materialExitError (V : ℝ) : ℝ :=
  4*Real.exp (-V/2000)+48000*V*Real.exp (-V/2000+1/50)

theorem materialExitError_nonneg (V : ℕ) : 0 ≤ materialExitError V := by
  unfold materialExitError
  positivity

theorem prepared_resource_potential (N : Counts) (V : ℕ)
    (h : ∀ side, (24/25)*(V:ℝ) ≤ unitObs side N ∧ unitObs side N ≤ (51/50)*(V:ℝ)) :
    resourcePotential V N ≤ 4*Real.exp (-(V:ℝ)/2000) := by
  have hu (side : Bool) : upperUnitPotential side V N ≤ Real.exp (-(V:ℝ)/2000) := by
    apply Real.exp_le_exp.mpr
    dsimp [upperUnitPotential]
    linarith [(h side).2,Nat.cast_nonneg (α := ℝ) V]
  have hl (side : Bool) : lowerUnitPotential side V N ≤ Real.exp (-(V:ℝ)/2000) := by
    apply Real.exp_le_exp.mpr
    dsimp [lowerUnitPotential]
    linarith [(h side).1,Nat.cast_nonneg (α := ℝ) V]
  unfold resourcePotential
  linarith [hu true,hu false,hl true,hl false]

theorem prepared_material_exit (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ))
    (hr : 0 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25) (N : BoxCounts V)
    (h : ∀ side, (24/25)*(V:ℝ) ≤ unitObs side (boxCounts N) ∧
      unitObs side (boxCounts N) ≤ (51/50)*(V:ℝ)) :
    (materialKernel V r d hV hr hr' hd hd').poissonized ((3000:ℝ≥0)*V*4)
      (FiniteKernel.eventIndicator {X | ¬resourceGood (boxCounts X) V}) N ≤ materialExitError V := by
  have hh := material_exit_probability V r d hV hr hr' hd hd' 4 N
  have hp := prepared_resource_potential (boxCounts N) V h
  norm_num only [NNReal.coe_ofNat] at hh
  unfold materialExitError resourceSource at *
  nlinarith

/-- Actual pulse mixture followed by four units of the stopped literal source.
The full pulse distribution, including adverse outcomes, is integrated. -/
theorem pulse_material_exit (N : Counts) (V : ℕ) (p : Intervention) (hN : Restart V N)
    (hVlarge : 1000 ≤ V) (r d : ℝ) (hV : 0 < (V:ℝ))
    (hr : 0 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25) :
    (∑ o, pulseMass N p o *
      (materialKernel V r d hV hr hr' hd hd').poissonized ((3000:ℝ≥0)*V*4)
        (FiniteKernel.eventIndicator {X | ¬resourceGood (boxCounts X) V})
        (postPulseBox N V p hN o)) ≤
      4*Real.exp (-(V:ℝ)/100000)+materialExitError V := by
  let P := materialKernel V r d hV hr hr' hd hd'
  let E : Set (BoxCounts V) := {X | ¬resourceGood (boxCounts X) V}
  have hpoint (o : PulseOutcome N) : P.poissonized ((3000:ℝ≥0)*V*4)
      (FiniteKernel.eventIndicator E) (postPulseBox N V p hN o) ≤
      (if o ∈ BadPulseMaterial N V p then 1 else 0)+materialExitError V := by
    by_cases hb : o ∈ BadPulseMaterial N V p
    · rw [if_pos hb]
      exact (P.poissonized_event_bounds _ E _).2.trans (le_add_of_nonneg_right (materialExitError_nonneg V))
    · rw [if_neg hb,zero_add]
      apply prepared_material_exit V r d hV hr hr' hd hd' (postPulseBox N V p hN o)
      intro side
      rw [postPulseBox_counts]
      have hh : ¬(unitObs side (postPulseCounts N V p o) < (24/25)*(V:ℝ) ∨
          (51/50)*(V:ℝ) < unitObs side (postPulseCounts N V p o)) := by
        intro hbad
        exact hb ⟨side,hbad⟩
      constructor <;> by_contra hc <;> apply hh <;> simp_all
  have hsum := Finset.sum_le_sum (fun (o : PulseOutcome N) (_ : o ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (hpoint o) (pulseMass_nonneg N p o))
  have he : (∑ o, pulseMass N p o*((if o ∈ BadPulseMaterial N V p then 1 else 0)+materialExitError V)) =
      pulseProbability N p (BadPulseMaterial N V p)+materialExitError V := by
    simp only [mul_add,Finset.sum_add_distrib]
    rw [← Finset.sum_mul,pulseMass_total,one_mul]
    congr 1
    unfold pulseProbability
    apply Finset.sum_congr rfl
    intro o _
    split_ifs <;> simp
  rw [he] at hsum
  exact hsum.trans (add_le_add (pulse_material_probability N V p hVlarge hN) le_rfl)

end
end FiniteCopyReactor
