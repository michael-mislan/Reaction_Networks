import proofs.DiagnosticWindows.BirthSource

namespace DiagnosticWindows
open FiniteCopy
open scoped BigOperators

def loadIndex (n : ℕ) : Fin 6 := ⟨min n 5, by omega⟩

noncomputable def loadedSurvival (P : FiniteKernel (Fin 6)) (load t : NNReal) : ℝ :=
  ∑' n, poissonWeight load n * P.poissonized t uncalled (loadIndex n)

theorem loading_summable (P : FiniteKernel (Fin 6)) (load t : NNReal) :
    Summable (fun n => poissonWeight load n * P.poissonized t uncalled (loadIndex n)) := by
  have hb (n : ℕ) : 0 ≤ P.poissonized t uncalled (loadIndex n) ∧
      P.poissonized t uncalled (loadIndex n) ≤ 1 := by
    rw [uncalled_indicator]
    exact P.poissonized_event_bounds _ _ _
  apply Summable.of_nonneg_of_le
    (fun n => mul_nonneg (poissonWeight_nonneg load n) (hb n).1)
    (fun n => mul_le_of_le_one_right (poissonWeight_nonneg load n) (hb n).2)
    (poissonWeight_sum load).summable

/-- Empty loaded reactions have the very same blank kernel, giving the sampling
floor directly on the source-defined mixture. -/
theorem empty_loading_floor (P : FiniteKernel (Fin 6)) (load t : NNReal) :
    Real.exp (-(load:ℝ))*P.poissonized t uncalled 0 ≤ loadedSurvival P load t := by
  have hn (n : ℕ) : 0 ≤ poissonWeight load n * P.poissonized t uncalled (loadIndex n) := by
    apply mul_nonneg (poissonWeight_nonneg load n)
    rw [uncalled_indicator]
    exact (P.poissonized_event_bounds _ _ _).1
  have h := (loading_summable P load t).le_tsum 0 (fun n _ => hn n)
  simpa [poissonWeight,loadIndex,loadedSurvival] using h

theorem birth_absorbed_steps (r : Fin 6 → ℝ) (hr : ∀ z, r z ∈ Set.Icc 0 1)
    (n : ℕ) : (birthKernel r hr).steps n uncalled 5 = 0 := by
  induction n with
  | zero => simp [FiniteKernel.steps,uncalled]
  | succ n ih =>
    simpa [FiniteKernel.steps,FiniteKernel.step,birthKernel,Fin.sum_univ_succ] using ih

theorem birth_absorbed (r : Fin 6 → ℝ) (hr : ∀ z, r z ∈ Set.Icc 0 1)
    (t : NNReal) : (birthKernel r hr).poissonized t uncalled 5 = 0 := by
  simp [FiniteKernel.poissonized,birth_absorbed_steps]

/-- The infinite Poisson loading tail contributes zero negative calls because it
is already above threshold. It is neither discarded nor renormalized. -/
theorem loading_finite (r : Fin 6 → ℝ) (hr : ∀ z, r z ∈ Set.Icc 0 1)
    (load t : NNReal) :
    loadedSurvival (birthKernel r hr) load t =
      ∑ n ∈ Finset.range 5, poissonWeight load n *
        (birthKernel r hr).poissonized t uncalled (loadIndex n) := by
  unfold loadedSurvival
  apply tsum_eq_sum
  intro n hn
  have hn5 : 5 ≤ n := by simpa using hn
  have hi : loadIndex n = 5 := by
    apply Fin.ext
    simp [loadIndex,Nat.min_eq_right hn5]
  rw [hi,birth_absorbed,mul_zero]

end DiagnosticWindows
