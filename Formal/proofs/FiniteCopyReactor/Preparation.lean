import proofs.FiniteCopyReactor.MaterialPulse

namespace FiniteCopyReactor
noncomputable section
open ProductiveRecovery RandomViability.Binding FiniteCopy Classical
open scoped BigOperators NNReal

theorem postPulse_stock_eq (N : Counts) (V : ℕ) (p : Intervention) (o : PulseOutcome N) :
    weightedCount (postPulseCounts N V p o) = retainedStock N (moleculeWeight N) o := by
  have he : retainedStock N (moleculeWeight N) o =
      ∑ i, speciesWeight i*(categoryCounts N o 0 i:ℝ) := by
    unfold retainedStock
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro i _
    unfold categoryCounts
    rw [Nat.cast_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    dsimp [moleculeWeight]
    split_ifs <;> simp
  rw [he]
  norm_num [weightedCount,weighted,postPulseCounts,speciesWeight,Fin.sum_univ_succ,Fin.succ]
  change _ = (categoryCounts N o 0 2:ℝ)+((9/8)*(categoryCounts N o 0 3:ℝ)+
    ((7/5)*(categoryCounts N o 0 4:ℝ)+(9/5)*(categoryCounts N o 0 5:ℝ)))
  ring

def BadPulseStock (N : Counts) (V : ℕ) (p : Intervention) : Set (PulseOutcome N) :=
  {o | weightedCount (postPulseCounts N V p o) ≤ (3/250)*(V:ℝ)}

theorem pulse_stock_probability (N : Counts) (V : ℕ) (p : Intervention) (hN : Restart V N) :
    pulseProbability N p (BadPulseStock N V p) ≤ Real.exp (-(1177/1000000000)*(V:ℝ)) := by
  have he : pulseProbability N p (BadPulseStock N V p) =
      pulseTail N p (moleculeWeight N) ((3/250)*(V:ℝ)) := by
    unfold pulseProbability BadPulseStock pulseTail
    simp only [Set.mem_setOf_eq,postPulse_stock_eq]
  rw [he]
  exact restart_pulse_stock_tail N V p hN

def preparationError (V : ℝ) : ℝ :=
  Real.exp (-(1177/1000000000)*V)+4*Real.exp (-V/100000)+materialExitError V

/-- Joint catalytic preparation, material preparation and four-unit material survival.
All adverse pulse outcomes count as failure in this same mixture. -/
theorem preparation_failure_probability (N : Counts) (V : ℕ) (p : Intervention) (hN : Restart V N)
    (hVlarge : 1000 ≤ V) (r d : ℝ) (hV : 0 < (V:ℝ))
    (hr : 0 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25) :
    (∑ o, pulseMass N p o *
      (if o ∈ BadPulseStock N V p ∪ BadPulseMaterial N V p then 1 else
        (materialKernel V r d hV hr hr' hd hd').poissonized ((3000:ℝ≥0)*V*4)
          (FiniteKernel.eventIndicator {X | ¬resourceGood (boxCounts X) V})
          (postPulseBox N V p hN o))) ≤ preparationError V := by
  let E := BadPulseStock N V p ∪ BadPulseMaterial N V p
  have hp (o : PulseOutcome N) :
      (if o ∈ E then 1 else
        (materialKernel V r d hV hr hr' hd hd').poissonized ((3000:ℝ≥0)*V*4)
          (FiniteKernel.eventIndicator {X | ¬resourceGood (boxCounts X) V}) (postPulseBox N V p hN o)) ≤
      (if o ∈ E then 1 else 0)+materialExitError V := by
    by_cases he : o ∈ E
    · simp only [if_pos he]
      exact le_add_of_nonneg_right (materialExitError_nonneg V)
    · simp only [if_neg he,zero_add]
      apply prepared_material_exit V r d hV hr hr' hd hd' (postPulseBox N V p hN o)
      intro side
      rw [postPulseBox_counts]
      have hb : o ∉ BadPulseMaterial N V p := fun hm => he (Or.inr hm)
      have hh : ¬(unitObs side (postPulseCounts N V p o) < (24/25)*(V:ℝ) ∨
          (51/50)*(V:ℝ) < unitObs side (postPulseCounts N V p o)) := fun hbad => hb ⟨side,hbad⟩
      constructor <;> by_contra hc <;> apply hh <;> simp_all
  have hsum := Finset.sum_le_sum (fun (o : PulseOutcome N) (_ : o ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (hp o) (pulseMass_nonneg N p o))
  have heq : (∑ o, pulseMass N p o*((if o ∈ E then 1 else 0)+materialExitError V)) =
      pulseProbability N p E+materialExitError V := by
    simp only [mul_add,Finset.sum_add_distrib]
    rw [← Finset.sum_mul,pulseMass_total,one_mul]
    congr 1
    unfold pulseProbability
    apply Finset.sum_congr rfl
    intro o _
    split_ifs <;> simp
  rw [heq] at hsum
  have hprob := pulseProbability_union N p (BadPulseStock N V p) (BadPulseMaterial N V p)
  have hs := pulse_stock_probability N V p hN
  have hm := pulse_material_probability N V p hVlarge hN
  dsimp [preparationError]
  exact hsum.trans (add_le_add (hprob.trans (add_le_add hs hm)) le_rfl)

end
end FiniteCopyReactor
