import proofs.RandomViability.BindingRateSupport
import proofs.RandomViability.BindingMechanism

namespace RandomViability.Binding
noncomputable section
open scoped BigOperators

def countGrowth (N : Counts) (V eps k r : ℝ) : ℝ :=
  ∑ j,countRate N V eps k r j*(weightedCount (countNext N j)-weightedCount N)

theorem factorial_identity (n : ℕ) : ((n*(n-1):ℕ):ℝ) = (n:ℝ)^2-(n:ℝ) := by
  by_cases h : n = 0
  · simp [h]
  · rw [Nat.cast_mul,Nat.cast_sub (by omega : 1 ≤ n),Nat.cast_one]
    ring

theorem countGrowth_expansion (N : Counts) (V eps k r : ℝ) :
    countGrowth N V eps k r =
      eps*(N 0)*(N 1)/V-eps*k*(N 2)+
      (5/2)*(N 2)*(N 0)/V-(N 2)-(29/8)*(N 3)+
      (11/2)*(N 3)*(N 1)/V+(11/10)*(N 4)+
      (r/5-9/5-8*k)*(N 5)-r/(5*V)*((N 2:ℝ)^2-(N 2:ℝ)) := by
  simp only [countGrowth,rated_weighted_jump]
  simp only [countRate,weightedJump,Fin.sum_univ_succ,Matrix.cons_val_zero,
    Matrix.cons_val_succ,Fin.sum_univ_zero]
  rw [factorial_identity]
  ring

/-- The actual falling factorial improves the lower drift, rather than
introducing an uncharged adverse finite-size correction. -/
theorem actual_count_corridor_growth (N : Counts) (V eps k r : ℝ)
    (hV : 0 < V) (heps : 0 ≤ eps) (hepsSmall : eps ≤ 1/1000000)
    (hk : 0 ≤ k) (hk1 : k ≤ 1/8) (hr : 18 ≤ r) (hr1 : r ≤ 22)
    (hu : 4/5 ≤ (N 0:ℝ)/V) (hw : 4/5 ≤ (N 1:ℝ)/V)
    (hx : (N 2:ℝ)/V ≤ 1/1000) :
    (39/100)*weightedCount N+(16/25)*eps*V ≤ countGrowth N V eps k r := by
  have he := corridor_growth ((N 0:ℝ)/V) ((N 1:ℝ)/V) ((N 2:ℝ)/V)
    ((N 3:ℝ)/V) ((N 4:ℝ)/V) ((N 5:ℝ)/V) eps k r hu hw
    (by positivity) (by positivity) (by positivity) (by positivity)
    heps hepsSmall hk hk1 hr hr1 hx
  have hm := mul_le_mul_of_nonneg_right he hV.le
  have hid : countGrowth N V eps k r =
    (eps*((N 0:ℝ)/V)*((N 1:ℝ)/V)-eps*k*((N 2:ℝ)/V)+
      (5/2*((N 0:ℝ)/V)-1)*((N 2:ℝ)/V)+
      (-29/8+11/2*((N 1:ℝ)/V))*((N 3:ℝ)/V)+
      11/10*((N 4:ℝ)/V)+(r/5-9/5-8*k)*((N 5:ℝ)/V)-
      r/5*((N 2:ℝ)/V)*((N 2:ℝ)/V))*V + r/(5*V)*(N 2) := by
    rw [countGrowth_expansion]
    field_simp
    ring
  have hl : ((39/100)*weighted ((N 2:ℝ)/V) ((N 3:ℝ)/V)
      ((N 4:ℝ)/V) ((N 5:ℝ)/V)+(16/25)*eps)*V =
      (39/100)*weightedCount N+(16/25)*eps*V := by
    dsimp [weighted,weightedCount]
    field_simp
  rw [hl] at hm
  rw [hid]
  have hr0 : 0 ≤ r := by linarith
  exact hm.trans (le_add_of_nonneg_right (by positivity))

end
end RandomViability.Binding
