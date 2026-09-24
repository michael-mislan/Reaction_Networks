import proofs.DiagnosticWindows.Numerical
import proofs.DiagnosticWindows.Monotonicity

namespace DiagnosticWindows
open FiniteCopy
open scoped BigOperators

theorem kernel5_uncalled_decay (x : Fin 6) : kernel5.step uncalled x ≤ uncalled x := by
  fin_cases x <;>
    norm_num [kernel5,birthKernel,FiniteKernel.step,uncalled,rates5,Fin.sum_univ_succ]

theorem survival5_antitone (x : Fin 6) :
    Antitone (fun t : NNReal => kernel5.poissonized t uncalled x) := by
  intro s t hst
  change kernel5.poissonized t uncalled x ≤ kernel5.poissonized s uncalled x
  rw [capacity5_survival,capacity5_survival]
  exact spectral_antitone kernel5 uncalled modes5 eigen5 capacity5_sum
    capacity5_eigen kernel5_uncalled_decay x s.property t.property hst

theorem blank5_monotone : Monotone blank5 := by
  intro s t hst
  have hm := survival5_antitone 0 (mul_le_mul_of_nonneg_left hst (by positivity : (0:NNReal) ≤ 5/2))
  unfold blank5
  linarith

theorem miss5_antitone : Antitone miss5 := by
  intro s t hst
  unfold miss5 loadedSurvival
  apply Summable.tsum_le_tsum
  · intro n
    exact mul_le_mul_of_nonneg_left
      (survival5_antitone (loadIndex n)
        (mul_le_mul_of_nonneg_left hst (by positivity : (0:NNReal) ≤ 5/2)))
      (poissonWeight_nonneg 4 n)
  · exact loading_summable kernel5 4 ((5/2)*t)
  · exact loading_summable kernel5 4 ((5/2)*s)

theorem capacity5_no_deadline (t : NNReal) :
    ¬(blank5 t ≤ 1/100 ∧ miss5 t ≤ 1/20) := by
  intro h
  rcases le_total t 5 with ht | ht
  · have hm := miss5_antitone ht
    linarith [capacity5_separating_errors.2,h.2]
  · have hb := blank5_monotone ht
    linarith [capacity5_separating_errors.1,h.1]

/-- One fixed-loading capacity change restores a feasible detection deadline.
All probabilities are the actual source-defined Poissonized kernel mixtures.
This is an illustrative effective-model theorem, not an empirical assay claim. -/
theorem main :
    (blank10 (16/5) ≤ 1/100 ∧ miss10 (16/5) ≤ 1/20) ∧
    ∀ t : NNReal, ¬(blank5 t ≤ 1/100 ∧ miss5 t ≤ 1/20) :=
  ⟨capacity10_errors,capacity5_no_deadline⟩

end DiagnosticWindows
