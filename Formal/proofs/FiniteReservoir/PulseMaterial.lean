import proofs.FiniteReservoir.MaterialControl

namespace FiniteReservoir
noncomputable section
open Classical ProductiveRecovery RandomViability.Binding FiniteCopy FiniteCopyReactor
open scoped BigOperators NNReal

def postPulse (N : Counts) (V M : ℕ) (p : Intervention) (hN : Restart V N)
    (fuel : FuelState M) (o : PulseOutcome N) : BoxState V M :=
  (postPulseBox N V p hN o,fuel)

theorem postPulse_bath (N : Counts) (V M : ℕ) (p : Intervention) (hN : Restart V N)
    (fuel : FuelState M) (o : PulseOutcome N) :
    (boxState (postPulse N V M p hN fuel o)).2=bathOf fuel := rfl

theorem postPulse_counts (N : Counts) (V M : ℕ) (p : Intervention) (hN : Restart V N)
    (fuel : FuelState M) (o : PulseOutcome N) :
    (boxState (postPulse N V M p hN fuel o)).1=postPulseCounts N V p o := rfl

theorem pulse_total (N : Counts) (p : Intervention) : (∑ o,pulseMass N p o)=1 :=
  pulseMass_total N p

/-- Actual pulse mixture followed by four units of the stopped literal source.
The full pulse distribution, including adverse outcomes, is integrated. -/
theorem pulse_material_exit (N : Counts) (V M : ℕ) (p : Intervention) (hN : Restart V N)
    (hVlarge : 1000 ≤ V) (params : Parameters M) (hV : 0 < (V:ℝ)) (fuel : FuelState M) :
    (∑ o, pulseMass N p o *
      (materialKernel V M params hV).poissonized ((3000:ℝ≥0)*V*4)
        (FiniteKernel.eventIndicator {X | ¬resourceGood (boxCounts X.1) V})
        (postPulse N V M p hN fuel o)) ≤
      4*Real.exp (-(V:ℝ)/100000)+materialExitError V := by
  let P := materialKernel V M params hV
  let E : Set (BoxState V M) := {X | ¬resourceGood (boxCounts X.1) V}
  have hpoint (o : PulseOutcome N) : P.poissonized ((3000:ℝ≥0)*V*4)
      (FiniteKernel.eventIndicator E) (postPulse N V M p hN fuel o) ≤
      (if o ∈ BadPulseMaterial N V p then 1 else 0)+materialExitError V := by
    by_cases hb : o ∈ BadPulseMaterial N V p
    · rw [if_pos hb]
      exact (P.poissonized_event_bounds _ E _).2.trans (le_add_of_nonneg_right (materialExitError_nonneg V))
    · rw [if_neg hb,zero_add]
      apply prepared_material_exit V M params hV (postPulse N V M p hN fuel o)
      intro side
      change (24/25)*(V:ℝ) ≤ unitObs side (postPulseCounts N V p o) ∧
        unitObs side (postPulseCounts N V p o) ≤ (51/50)*(V:ℝ)
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
end FiniteReservoir
