import proofs.RandomViability.BindingCountVariance
import proofs.RandomViability.CopyNumberLogBound

namespace RandomViability.Binding
noncomputable section
open scoped BigOperators

abbrev Counts := Fin 6 → ℕ

/-- U,W,X,C1,C2,Z; paired internal channels, then two feeds and six washouts.
The parameter k is 1/K, not K. No stochastic factorial divisor is present. -/
def countRate (N : Counts) (V eps k r : ℝ) : Fin 18 → ℝ :=
  ![eps*(N 0)*(N 1)/V, eps*k*(N 2),
    20*(N 2)*(N 0)/V,20*(N 3),
    20*(N 3)*(N 1)/V,20*(N 4),
    20*(N 4),20*k*(N 5),r*(N 5),r*(N 2*(N 2-1):ℕ)/V,
    V,V,N 0,N 1,N 2,N 3,N 4,N 5]

def weightedJump : Fin 18 → ℝ :=
  ![1,-1,1/8,-1/8,11/40,-11/40,2/5,-2/5,1/5,-1/5,
    0,0,0,0,-1,-9/8,-7/5,-9/5]

def weightedCount (N : Counts) : ℝ := weighted (N 2) (N 3) (N 4) (N 5)

def countVariance (N : Counts) (V eps k r : ℝ) : ℝ :=
  ∑ j, countRate N V eps k r j * (weightedJump j)^2

theorem countRate_nonneg (N : Counts) (V eps k r : ℝ)
    (hV : 0 < V) (heps : 0 ≤ eps) (hk : 0 ≤ k) (hr : 0 ≤ r)
    (j : Fin 18) : 0 ≤ countRate N V eps k r j := by
  fin_cases j <;> norm_num [countRate] <;> positivity

theorem weightedJump_bound (j : Fin 18) : |weightedJump j| ≤ (9/5 : ℝ) := by
  fin_cases j <;> norm_num [weightedJump]

theorem countVariance_expansion (N : Counts) (V eps k r : ℝ) :
    countVariance N V eps k r =
      eps*(N 0)*(N 1)/V + eps*k*(N 2) +
      (20*(N 2)*(N 0)/V+20*(N 3))*(1/8)^2 +
      (20*(N 3)*(N 1)/V+20*(N 4))*(11/40)^2 +
      (20*(N 4)+20*k*(N 5))*(2/5)^2 +
      (r*(N 5)+r*(N 2*(N 2-1):ℕ)/V)*(1/5)^2 +
      (N 2)+(9/8)^2*(N 3)+(7/5)^2*(N 4)+(9/5)^2*(N 5) := by
  simp only [countVariance,countRate,weightedJump,Fin.sum_univ_succ,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.sum_univ_zero]
  ring

theorem factorial_le_square (n : ℕ) : ((n*(n-1):ℕ):ℝ) ≤ (n:ℝ)^2 := by
  have h : n*(n-1) ≤ n*n := Nat.mul_le_mul_left n (Nat.sub_le _ _)
  simpa only [sq] using (show ((n*(n-1):ℕ):ℝ) ≤ (n:ℝ)*(n:ℝ) by exact_mod_cast h)

/-- Literal count quadratic variation bound, under explicit local resource
inequalities. These conditions are to be proved up to a paid stopping event. -/
theorem actual_count_variance_bound (N : Counts) (V eps k r : ℝ)
    (hV : 0 < V) (heps : 0 ≤ eps) (heps1 : eps ≤ 1)
    (hk : 0 ≤ k) (hk1 : k ≤ 1/8) (hr : 0 ≤ r) (hr1 : r ≤ 22)
    (hu : (N 0:ℝ)/V ≤ 5/2) (hw : (N 1:ℝ)/V ≤ 5/2)
    (huw : ((N 0:ℝ)/V)*((N 1:ℝ)/V) ≤ 25/16)
    (hx : (N 2:ℝ)/V ≤ 5/4) :
    countVariance N V eps k r ≤ 5*weightedCount N+(25/16)*eps*V := by
  have he := variance_envelope_bound ((N 0:ℝ)/V) ((N 1:ℝ)/V) ((N 2:ℝ)/V)
    ((N 3:ℝ)/V) ((N 4:ℝ)/V) ((N 5:ℝ)/V) eps k r
    hu hw huw (by positivity) hx (by positivity) (by positivity) (by positivity)
    heps heps1 hk hk1 hr hr1
  have hf := factorial_le_square (N 2)
  have hid : countVariance N V eps k r =
      varianceEnvelope ((N 0:ℝ)/V) ((N 1:ℝ)/V) ((N 2:ℝ)/V)
        ((N 3:ℝ)/V) ((N 4:ℝ)/V) ((N 5:ℝ)/V) eps k r * V -
      (r/V)*((N 2:ℝ)^2-(N 2*(N 2-1):ℕ))/25 := by
    rw [countVariance_expansion]
    dsimp [varianceEnvelope]
    field_simp
    ring
  rw [hid]
  calc
    _ ≤ varianceEnvelope ((N 0:ℝ)/V) ((N 1:ℝ)/V) ((N 2:ℝ)/V)
        ((N 3:ℝ)/V) ((N 4:ℝ)/V) ((N 5:ℝ)/V) eps k r * V :=
      sub_le_self _ (div_nonneg (mul_nonneg (div_nonneg hr hV.le) (sub_nonneg.mpr hf)) (by norm_num))
    _ ≤ (5*weighted ((N 2:ℝ)/V) ((N 3:ℝ)/V) ((N 4:ℝ)/V) ((N 5:ℝ)/V)
        +(25/16)*eps)*V := mul_le_mul_of_nonneg_right he hV.le
    _ = _ := by
      dsimp [weighted,weightedCount]
      field_simp

end
end RandomViability.Binding
