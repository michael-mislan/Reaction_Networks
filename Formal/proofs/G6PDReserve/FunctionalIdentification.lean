import proofs.G6PDReserve.ObservationBounds

namespace G6PDReserve
noncomputable section
open scoped BigOperators

/-- Row-space membership identifies a functional without full parameter rank. -/
theorem row_combination_identifies {ι : Type*} [Fintype ι]
    (F : ι → Six) (w : ι → ℝ) (c b b' : Six)
    (hc : ∀ j, c j = ∑ i, w i * F i j)
    (hobs : ∀ i, dot (F i) b = dot (F i) b') :
    dot c b = dot c b' := by
  have expand (x : Six) : dot c x = ∑ i, w i * dot (F i) x := by
    simp only [dot, hc, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [expand, expand]
  simp_rw [hobs]

theorem dot_perturb (c b z : Six) (ε : ℝ) :
    dot c (fun j => b j + ε*z j) = dot c b + ε*dot c z := by
  simp only [dot, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Explicit feasible null-direction converse. Extra biological constraints must
be checked separately; this statement concerns the unrestricted positive class. -/
theorem null_direction_nonidentification {ι : Type*} (F : ι → Six)
    (c b z : Six) (ε : ℝ) (hb : PositiveSix b)
    (hsmall : ∀ j, |ε*z j| < b j) (hε : ε ≠ 0)
    (hz : ∀ i, dot (F i) z = 0) (hc : dot c z ≠ 0) :
    PositiveSix b ∧ PositiveSix (fun j => b j + ε*z j) ∧
    (∀ i, dot (F i) (fun j => b j + ε*z j) = dot (F i) b) ∧
    dot c (fun j => b j + ε*z j) ≠ dot c b := by
  refine ⟨hb, ?_, ?_, ?_⟩
  · intro j
    have := (abs_lt.mp (hsmall j)).1
    linarith
  · intro i
    rw [dot_perturb, hz i, mul_zero, add_zero]
  · rw [dot_perturb]
    intro h
    have : ε * dot c z = 0 := by linarith
    exact (mul_ne_zero hε hc) this

end
end G6PDReserve
