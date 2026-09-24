import proofs.ProductiveMemory.ExtractionRecovery

namespace ProductiveMemory
open FiniteCopy Set
open scoped NNReal
noncomputable section
set_option Elab.async false

def terminalReady (N : ℕ) (D : Finset Counts) (s : Point) (E : Point → ℝ) :
    Set (ExtractionStoppedCounts D) :=
  {n | match n with
    | none => False
    | some n => E (fun i => concentration N n.val i-s i) ≤ readyLevel}

theorem terminal_partition (N : ℕ) (D : Finset Counts) (s : Point) (E : Point → ℝ)
    (P : FiniteKernel (ExtractionStoppedCounts D)) (t : NNReal)
    (x : ExtractionStoppedCounts D) :
    P.poissonized t (FiniteKernel.eventIndicator (terminalReady N D s E)) x +
      P.poissonized t (FiniteKernel.eventIndicator (terminalUnready N D s E)) x +
      P.poissonized t (FiniteKernel.eventIndicator {none}) x = 1 := by
  classical
  let f := FiniteKernel.eventIndicator (terminalReady N D s E)
  let g := FiniteKernel.eventIndicator (terminalUnready N D s E)
  let h := FiniteKernel.eventIndicator ({none} : Set (ExtractionStoppedCounts D))
  have hf : ∀ y, 0 ≤ f y := by intro y; simp [f, FiniteKernel.eventIndicator]; split_ifs <;> norm_num
  have hg : ∀ y, 0 ≤ g y := by intro y; simp [g, FiniteKernel.eventIndicator]; split_ifs <;> norm_num
  have hh : ∀ y, 0 ≤ h y := by intro y; simp [h, FiniteKernel.eventIndicator]; split_ifs <;> norm_num
  have hid : (fun y => (f y + g y) + h y) = (fun _ => 1) := by
    funext y
    cases y with
    | none => simp [f, g, h, FiniteKernel.eventIndicator, terminalReady, terminalUnready]
    | some y =>
      by_cases he : E (fun i => concentration N y.val i-s i) ≤ readyLevel
      · simp [f, g, h, FiniteKernel.eventIndicator, terminalReady, terminalUnready, he, not_lt.mpr he]
      · simp [f, g, h, FiniteKernel.eventIndicator, terminalReady, terminalUnready, he, lt_of_not_ge he]
  have ha := P.poissonized_add t (fun y => f y+g y) h (fun y => add_nonneg (hf y) (hg y)) hh x
  rw [P.poissonized_add t f g hf hg x, hid, P.poissonized_const] at ha
  exact ha.symm

theorem terminal_ready_lower (N : ℕ) (D : Finset Counts) (s : Point) (E : Point → ℝ)
    (P : FiniteKernel (ExtractionStoppedCounts D)) (t : NNReal)
    (x : ExtractionStoppedCounts D) (b c : ℝ)
    (hb : P.poissonized t (FiniteKernel.eventIndicator (terminalUnready N D s E)) x ≤ b)
    (hc : P.poissonized t (FiniteKernel.eventIndicator {none}) x ≤ c) :
    1-b-c ≤ P.poissonized t (FiniteKernel.eventIndicator (terminalReady N D s E)) x := by
  have hp := terminal_partition N D s E P t x
  linarith

end
end ProductiveMemory
