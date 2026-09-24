import proofs.DiagnosticWindows.Loading

namespace DiagnosticWindows
open FiniteCopy
open scoped BigOperators

def nextState (x : Fin 6) : Fin 6 := loadIndex (x.val+1)

theorem birth_step (r : Fin 6 → ℝ) (hr : ∀ z, r z ∈ Set.Icc 0 1)
    (f : Fin 6 → ℝ) (x : Fin 6) :
    (birthKernel r hr).step f x = (1-r x)*f x+r x*f (nextState x) := by
  fin_cases x <;>
    simp [birthKernel,FiniteKernel.step,Fin.sum_univ_succ,nextState,loadIndex,
      show (⟨2,by decide⟩ : Fin 6) = 2 from rfl,
      show (⟨3,by decide⟩ : Fin 6) = 3 from rfl,
      show (⟨4,by decide⟩ : Fin 6) = 4 from rfl,
      show (⟨5,by decide⟩ : Fin 6) = 5 from rfl]
  all_goals ring

theorem next_ge (x : Fin 6) : x ≤ nextState x := by
  change x.val ≤ min (x.val+1) 5
  have := x.isLt
  omega

theorem next_le {x y : Fin 6} (h : x < y) : nextState x ≤ y := by
  change min (x.val+1) 5 ≤ y.val
  have : x.val < y.val := h
  omega

theorem birth_step_antitone (r : Fin 6 → ℝ) (hr : ∀ z, r z ∈ Set.Icc 0 1)
    (f : Fin 6 → ℝ) (hf : Antitone f) : Antitone ((birthKernel r hr).step f) := by
  intro x y hxy
  rcases eq_or_lt_of_le hxy with he | hl
  · subst y; rfl
  · rw [birth_step,birth_step]
    have hx := hf (next_ge x)
    have hy := hf (next_ge y)
    have hm := hf (next_le hl)
    have hx0 := (hr x).1
    have hx1 := (hr x).2
    have hy0 := (hr y).1
    nlinarith [mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hx1),
      mul_nonneg (sub_nonneg.mpr hy) hy0]

theorem uncalled_antitone : Antitone uncalled := by
  intro x y hxy
  unfold uncalled
  split_ifs <;> norm_num at *
  have := x.isLt
  have := y.isLt
  have : x.val ≤ y.val := hxy
  omega

theorem birth_steps_antitone (r : Fin 6 → ℝ) (hr : ∀ z, r z ∈ Set.Icc 0 1)
    (n : ℕ) : Antitone ((birthKernel r hr).steps n uncalled) := by
  induction n with
  | zero => exact uncalled_antitone
  | succ n ih => exact birth_step_antitone r hr _ ih

theorem birth_step_order (r s : Fin 6 → ℝ)
    (hr : ∀ z, r z ∈ Set.Icc 0 1) (hs : ∀ z, s z ∈ Set.Icc 0 1)
    (hrs : ∀ z, r z ≤ s z) (f : Fin 6 → ℝ) (hf : Antitone f) (x : Fin 6) :
    (birthKernel s hs).step f x ≤ (birthKernel r hr).step f x := by
  rw [birth_step,birth_step]
  have := mul_nonneg (sub_nonneg.mpr (hrs x)) (sub_nonneg.mpr (hf (next_ge x)))
  nlinarith

theorem birth_steps_order (r s : Fin 6 → ℝ)
    (hr : ∀ z, r z ∈ Set.Icc 0 1) (hs : ∀ z, s z ∈ Set.Icc 0 1)
    (hrs : ∀ z, r z ≤ s z) (n : ℕ) (x : Fin 6) :
    (birthKernel s hs).steps n uncalled x ≤ (birthKernel r hr).steps n uncalled x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    exact ((birthKernel s hs).step_mono ih x).trans
      (birth_step_order r s hr hs hrs _ (birth_steps_antitone r hr n) x)

theorem uncalled_summable (P : FiniteKernel (Fin 6)) (t : NNReal) (x : Fin 6) :
    Summable (fun n => poissonWeight t n * P.steps n uncalled x) := by
  rw [uncalled_indicator]
  exact P.event_summable t _ x

theorem birth_survival_order (r s : Fin 6 → ℝ)
    (hr : ∀ z, r z ∈ Set.Icc 0 1) (hs : ∀ z, s z ∈ Set.Icc 0 1)
    (hrs : ∀ z, r z ≤ s z) (t : NNReal) (x : Fin 6) :
    (birthKernel s hs).poissonized t uncalled x ≤
      (birthKernel r hr).poissonized t uncalled x := by
  apply Summable.tsum_le_tsum
  · intro n
    exact mul_le_mul_of_nonneg_left (birth_steps_order r s hr hs hrs n x)
      (poissonWeight_nonneg t n)
  · exact uncalled_summable _ t x
  · exact uncalled_summable _ t x

theorem birth_survival_antitone_state (r : Fin 6 → ℝ)
    (hr : ∀ z, r z ∈ Set.Icc 0 1) (t : NNReal) :
    Antitone ((birthKernel r hr).poissonized t uncalled) := by
  intro x y hxy
  apply Summable.tsum_le_tsum
  · intro n
    exact mul_le_mul_of_nonneg_left (birth_steps_antitone r hr n hxy)
      (poissonWeight_nonneg t n)
  · exact uncalled_summable _ t y
  · exact uncalled_summable _ t x

end DiagnosticWindows
