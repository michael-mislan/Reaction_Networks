import proofs.InheritedCellAssay.CountThresholdSource

namespace InheritedCellAssay.CountAssay
open FiniteCopy CompositionalMemory CountThreshold

abbrev State := Bool ⊕ Fin 4

/-- Time is measured in ten days. Sensitive cells die at rate 3, resistant
    cells divide at rate equal to their count. Observation records 4-or-more. -/
noncomputable def source : FiniteJumpModel State Unit where
  next s _ := match s with
    | .inl _ => .inl false
    | .inr n => .inr (birthNext n)
  rate s _ := match s with
    | .inl alive => if alive then 3 else 0
    | .inr n => (n.val+1 : ℝ)
  nonneg s _ := by
    cases s with
    | inl alive => cases alive <;> norm_num
    | inr n => positivity

def observedCount : State → ℕ
  | .inl alive => if alive then 1 else 0
  | .inr n => n.val+1

def below (k : ℕ) (s : State) : ℝ := if observedCount s ≤ k then 1 else 0

def lift (f : Fin 4 → ℝ) : State → ℝ
  | .inl _ => 1
  | .inr n => f n

theorem lift_backward (f : ℝ → Fin 4 → ℝ)
    (hf : ∀ t n, HasDerivAt (fun s => f s n) (birthSource.generator (f t) n) t)
    (t : ℝ) (s : State) :
    HasDerivAt (fun u => lift (f u) s) (source.generator (lift (f t)) s) t := by
  cases s with
  | inl alive =>
    simpa [lift, source, FiniteJumpModel.generator] using hasDerivAt_const t (1 : ℝ)
  | inr n =>
    simpa [lift, source, birthSource, FiniteJumpModel.generator] using hf t n

theorem below_two_initial : below 2 = lift (belowTwo 0) := by
  funext s
  cases s with
  | inl alive => cases alive <;> norm_num [below, observedCount, lift]
  | inr n => fin_cases n <;> norm_num [below, observedCount, lift, belowTwo]

theorem below_three_initial : below 3 = lift (belowThree 0) := by
  funext s
  cases s with
  | inl alive => cases alive <;> norm_num [below, observedCount, lift]
  | inr n => fin_cases n <;> norm_num [below, observedCount, lift, belowThree]

noncomputable def coverage (k : ℕ) : ℝ :=
  (19/24)*finiteTimeExpectation source horizon (below k) (.inl true) +
  (5/24)*finiteTimeExpectation source horizon (below k) (.inr 0)

theorem actual_source_failure_and_repair :
    coverage 2 = 91/96 ∧ coverage 2 < 19/20 ∧
    coverage 3 = 187/192 ∧ 19/20 < coverage 3 := by
  have h2 (s : State) := backward_solution_expectation source
    (fun t => lift (belowTwo t)) (lift_backward belowTwo belowTwo_backward) horizon s
  have h3 (s : State) := backward_solution_expectation source
    (fun t => lift (belowThree t)) (lift_backward belowThree belowThree_backward) horizon s
  have he : Real.exp (-(horizon : ℝ)) = 1/2 := by
    change Real.exp (-Real.log 2) = 1/2
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  simp only [coverage, below_two_initial, below_three_initial]
  simp only [h2, h3]
  norm_num [lift, belowTwo, belowThree, he]

def fullNext : Bool ⊕ ℕ → Bool ⊕ ℕ
  | .inl _ => .inl false
  | .inr n => .inr (n+1)

noncomputable def fullRate : Bool ⊕ ℕ → ℝ
  | .inl alive => if alive then 3 else 0
  | .inr n => n+1

def observe : Bool ⊕ ℕ → State
  | .inl alive => .inl alive
  | .inr n => .inr ⟨min n 3, by omega⟩

/-- No birth beyond the reporting threshold is discarded: its increment on
    every observed payoff is zero. This is the exact generator projection. -/
theorem full_generator_projection (f : State → ℝ) (s : Bool ⊕ ℕ) :
    fullRate s*(f (observe (fullNext s))-f (observe s)) =
      source.generator f (observe s) := by
  cases s with
  | inl alive => simp [fullRate, fullNext, observe, source, FiniteJumpModel.generator]
  | inr n =>
    by_cases hn : n < 3
    · interval_cases n <;> norm_num [fullRate, fullNext, observe, source,
        FiniteJumpModel.generator, birthNext]
    · have hn' : 3 ≤ n := by omega
      have hn1 : 3 ≤ n+1 := by omega
      simp [fullRate, fullNext, observe, source, FiniteJumpModel.generator,
        Nat.min_eq_right hn', Nat.min_eq_right hn1, birthNext]

end InheritedCellAssay.CountAssay
