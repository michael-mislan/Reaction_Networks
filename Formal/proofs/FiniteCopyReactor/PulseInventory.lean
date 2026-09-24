import proofs.FiniteCopyReactor.PulseStock

namespace FiniteCopyReactor
noncomputable section
open ProductiveRecovery RandomViability.Binding
open scoped BigOperators

def categoryCounts (N : Counts) (o : PulseOutcome N) (a : Fin 3) : Counts :=
  fun i => ∑ k : Fin (N i), if o ⟨i,k⟩=a then 1 else 0

/-- Every molecule has exactly one fate; losses and withdrawal are both recorded. -/
theorem category_inventory (N : Counts) (o : PulseOutcome N) (i : Fin 6) :
    (∑ a, categoryCounts N o a i) = N i := by
  classical
  unfold categoryCounts
  rw [Finset.sum_comm]
  have h (k : Fin (N i)) : (∑ a : Fin 3, if o ⟨i,k⟩=a then 1 else 0) = (1:ℕ) := by
    simp
  simp_rw [h]
  simp

def doseU (V : ℕ) (p : Intervention) : ℕ := ⌊(V:ℝ)*(1-p.q+p.eU)⌋₊
def doseW (V : ℕ) (p : Intervention) : ℕ := ⌊(V:ℝ)*(1-p.q+p.eW)⌋₊
def postPulseCounts (N : Counts) (V : ℕ) (p : Intervention) (o : PulseOutcome N) : Counts :=
  fun i => categoryCounts N o 0 i + if i=0 then doseU V p else if i=1 then doseW V p else 0

theorem doseU_rounding (V : ℕ) (p : Intervention) :
    (V:ℝ)*(1-p.q+p.eU)-1 < (doseU V p:ℝ) ∧
    (doseU V p:ℝ) ≤ (V:ℝ)*(1-p.q+p.eU) := by
  have h := food_feasible p
  constructor
  · have hh := Nat.lt_floor_add_one ((V:ℝ)*(1-p.q+p.eU))
    unfold doseU
    linarith
  · exact Nat.floor_le (mul_nonneg (Nat.cast_nonneg _) (by linarith [h.1]))

theorem doseW_rounding (V : ℕ) (p : Intervention) :
    (V:ℝ)*(1-p.q+p.eW)-1 < (doseW V p:ℝ) ∧
    (doseW V p:ℝ) ≤ (V:ℝ)*(1-p.q+p.eW) := by
  have h := food_feasible p
  constructor
  · have hh := Nat.lt_floor_add_one ((V:ℝ)*(1-p.q+p.eW))
    unfold doseW
    linarith
  · exact Nat.floor_le (mul_nonneg (Nat.cast_nonneg _) (by linarith [h.2.2.1]))

theorem pulse_food_budget (V : ℕ) (p : Intervention) :
    (doseU V p:ℝ) ≤ (151/200)*(V:ℝ) ∧ (doseW V p:ℝ) ≤ (151/200)*(V:ℝ) := by
  obtain ⟨_,hu,_,hw⟩ := food_feasible p
  constructor
  · have h := mul_le_mul_of_nonneg_left hu (Nat.cast_nonneg (α := ℝ) V)
    linarith [(doseU_rounding V p).2]
  · have h := mul_le_mul_of_nonneg_left hw (Nat.cast_nonneg (α := ℝ) V)
    linarith [(doseW_rounding V p).2]

end
end FiniteCopyReactor
