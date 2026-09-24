import proofs.LowFounderPrediction.Source

namespace MemoryPrediction
noncomputable section
open LowFounderPrediction

def totalCount (x : State) : ℕ := x.1+x.2

/-- Exact action of the six-event source generator on an unmarked count
observable. Switching cancels, but the demographic intensities retain type
composition unless birth and death rates separately agree. -/
theorem count_generator (a : Rates) (w : ℕ → ℝ) (x : State) :
    (∑ e, rate a x e * (w (totalCount (next x e))-w (totalCount x))) =
      (a.bS*x.1+a.bR*x.2)*(w (totalCount x+1)-w (totalCount x)) +
      (a.dS*x.1+a.dR*x.2)*(w (totalCount x-1)-w (totalCount x)) := by
  rcases x with ⟨s,r⟩
  cases s <;> cases r <;>
    simp [Fin.sum_univ_succ, rate, next, totalCount, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm, Nat.cast_add, Nat.cast_one]; ring

theorem equal_demographic_generator (a : Rates) (b d : ℝ)
    (hbS : a.bS=b) (hbR : a.bR=b) (hdS : a.dS=d) (hdR : a.dR=d)
    (w : ℕ → ℝ) (x : State) :
    (∑ e, rate a x e * (w (totalCount (next x e))-w (totalCount x))) =
      b*(totalCount x : ℝ)*(w (totalCount x+1)-w (totalCount x)) +
      d*(totalCount x : ℝ)*(w (totalCount x-1)-w (totalCount x)) := by
  rw [count_generator, hbS, hbR, hdS, hdR]
  simp only [totalCount, Nat.cast_add]
  ring

/-- Uniform generator comparison for decreasing count observables. This is
the local implication needed for the stopped-clock comparison; it does not
by itself assert a comparison of chronological laws. -/
theorem count_generator_lower (a : Rates) (b d : ℝ)
    (hbS : a.bS ≤ b) (hbR : a.bR ≤ b) (hdS : d ≤ a.dS) (hdR : d ≤ a.dR)
    (w : ℕ → ℝ) (hw : Antitone w) (x : State) :
    b*(totalCount x : ℝ)*(w (totalCount x+1)-w (totalCount x)) +
      d*(totalCount x : ℝ)*(w (totalCount x-1)-w (totalCount x)) ≤
    (∑ e, rate a x e * (w (totalCount (next x e))-w (totalCount x))) := by
  rw [count_generator]
  have hbirth : a.bS*x.1+a.bR*x.2 ≤ b*(totalCount x : ℝ) := by
    simp only [totalCount, Nat.cast_add, mul_add]
    exact add_le_add (mul_le_mul_of_nonneg_right hbS (Nat.cast_nonneg _))
      (mul_le_mul_of_nonneg_right hbR (Nat.cast_nonneg _))
  have hdeath : d*(totalCount x : ℝ) ≤ a.dS*x.1+a.dR*x.2 := by
    simp only [totalCount, Nat.cast_add, mul_add]
    exact add_le_add (mul_le_mul_of_nonneg_right hdS (Nat.cast_nonneg _))
      (mul_le_mul_of_nonneg_right hdR (Nat.cast_nonneg _))
  have hup : w (totalCount x+1)-w (totalCount x) ≤ 0 :=
    sub_nonpos.mpr (hw (Nat.le_succ _))
  have hdown : 0 ≤ w (totalCount x-1)-w (totalCount x) :=
    sub_nonneg.mpr (hw (Nat.sub_le _ _))
  exact add_le_add (mul_le_mul_of_nonpos_right hbirth hup)
    (mul_le_mul_of_nonneg_right hdeath hdown)

end
end MemoryPrediction
