import proofs.CompositionalMemory.SafeClockRenewal

namespace CompositionalMemory
open Classical RandomViability FiniteCopy MeasureTheory
open scoped ENNReal
noncomputable section
variable {α : Type*} [Fintype α]

theorem safeClockSteps_le_one (P : FiniteKernel α) (D : Set α) (f : α → ℝ≥0∞)
    (hf : ∀ x,f x ≤ 1) (n : ℕ) (x : α) : safeClockSteps P D f n x ≤ 1 := by
  induction n generalizing x with
  | zero => simp only [safeClockSteps]; split_ifs <;> first | exact hf x | exact zero_le
  | succ n ih =>
    simp only [safeClockSteps]
    split_ifs
    · calc
        _ ≤ ∑ y,ENNReal.ofReal (P.prob x y)*1 :=
          Finset.sum_le_sum (fun y _ => mul_le_mul_right (ih y) _)
        _ = 1 := by
          simp only [mul_one]
          rw [← ENNReal.ofReal_sum_of_nonneg (fun y _ => P.nonneg x y),P.row_sum,ENNReal.ofReal_one]
    · exact zero_le

theorem safeClockPayoff_le_one (P : FiniteKernel α) (D : Set α) (f : α → ℝ≥0∞)
    (hf : ∀ x,f x ≤ 1) (q T : NNReal) (x : α) : safeClockPayoff P D f q T x ≤ 1 := by
  calc
    _ ≤ ∑' n,ENNReal.ofReal (clockWeight q T n) :=
      ENNReal.tsum_le_tsum (fun n => mul_le_of_le_one_right' (safeClockSteps_le_one P D f hf n x))
    _ = 1 := by
      simp_rw [clockWeight_eq_poisson]
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => poissonWeight_nonneg (q*T) n) (poissonWeight_sum (q*T)).summable,
        (poissonWeight_sum (q*T)).tsum_eq,ENNReal.ofReal_one]

theorem safeClockSteps_univ (P : FiniteKernel α) (f : α → ℝ) (hf : ∀ x,0 ≤ f x)
    (n : ℕ) (x : α) : safeClockSteps P Set.univ (fun y => ENNReal.ofReal (f y)) n x =
      ENNReal.ofReal (P.steps n f x) := by
  induction n generalizing x with
  | zero => simp [safeClockSteps,FiniteKernel.steps]
  | succ n ih =>
    simp only [safeClockSteps,Set.mem_univ,if_true,ih,FiniteKernel.steps,FiniteKernel.step]
    rw [ENNReal.ofReal_sum_of_nonneg (fun y _ => mul_nonneg (P.nonneg x y) (P.steps_nonneg n hf y))]
    apply Finset.sum_congr rfl
    intro y _
    exact (ENNReal.ofReal_mul (P.nonneg x y)).symm

/-- Exact docking to the repository's real-valued finite Poisson law. -/
theorem safeClockPayoff_univ (P : FiniteKernel α) (f : α → ℝ)
    (hf : ∀ x,0 ≤ f x) (hf1 : ∀ x,f x ≤ 1) (q T : NNReal) (x : α) :
    safeClockPayoff P Set.univ (fun y => ENNReal.ofReal (f y)) q T x =
      ENNReal.ofReal (P.poissonized (q*T) f x) := by
  have hs : Summable (fun n => poissonWeight (q*T) n*P.steps n f x) :=
    Summable.of_nonneg_of_le
      (fun n => mul_nonneg (poissonWeight_nonneg (q*T) n) (P.steps_nonneg n hf x))
      (fun n => mul_le_of_le_one_right (poissonWeight_nonneg (q*T) n) (P.steps_le_one n hf1 x))
      (poissonWeight_sum (q*T)).summable
  unfold safeClockPayoff FiniteKernel.poissonized
  simp_rw [safeClockSteps_univ P f hf,clockWeight_eq_poisson]
  rw [ENNReal.ofReal_tsum_of_nonneg
    (fun n => mul_nonneg (poissonWeight_nonneg (q*T) n) (P.steps_nonneg n hf x)) hs]
  apply tsum_congr
  intro n
  exact (ENNReal.ofReal_mul (poissonWeight_nonneg (q*T) n)).symm

variable [MeasurableSpace α] [MeasurableSingletonClass α]

theorem safeClockPayoff_measurable (P : FiniteKernel α) (D : Set α) (f : α → ℝ≥0∞) (q : ℝ) :
    Measurable (fun p : α × ℝ => safeClockPayoff P D f q p.2 p.1) := by
  unfold safeClockPayoff
  apply Measurable.tsum
  intro n
  exact (((clockWeight_continuous q n).measurable.comp measurable_snd).ennreal_ofReal).mul
    ((measurable_of_countable (safeClockSteps P D f n)).comp measurable_fst)

end
end CompositionalMemory
