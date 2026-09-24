import proofs.OptimalAffinityRealizability.CapacityEquality

namespace OptimalAffinityRealizability

open scoped BigOperators
noncomputable section

/-- The coordinate gradient of the log response objective, written using the
positive response image `h = Tᵀ f`. -/
def formalLogResponseGradient {n : ℕ}
    (T : Matrix (Fin n) (Fin n) ℝ) (weights : Fin n → ℕ)
    (f h : Fin n → ℝ) (k : Fin n) : ℝ :=
  (∑ i, (weights i : ℝ) * T k i * f k / h i) - weights k

def InteriorLogProfileKKT {n : ℕ}
    (T : Matrix (Fin n) (Fin n) ℝ) (weights : Fin n → ℕ)
    (f h : Fin n → ℝ) : Prop :=
  ∀ k, formalLogResponseGradient T weights f h k = 0

theorem formalLogResponseGradient_eq_routingResidual {n : ℕ}
    (T : Matrix (Fin n) (Fin n) ℝ) (weights : Fin n → ℕ)
    (q f h : Fin n → ℝ) (hratio : ∀ i, h i = q i * f i)
    (k : Fin n) :
    formalLogResponseGradient T weights f h k =
      (routingMatrix T q f).transpose.mulVec (fun i => (weights i : ℝ)) k -
        weights k := by
  unfold formalLogResponseGradient routingMatrix Matrix.mulVec
  apply congrArg (fun x : ℝ => x - weights k)
  apply Finset.sum_congr rfl
  intro i hi
  rw [hratio i]
  simp only [Matrix.transpose_apply]
  ring

/-- The matrix-scaling KKT characterization: the interior log-profile
first-order equations are exactly stationarity of the weight vector for the
induced response routing matrix. -/
theorem interiorLogProfileKKT_iff_routingStationary {n : ℕ}
    (T : Matrix (Fin n) (Fin n) ℝ) (weights : Fin n → ℕ)
    (q f h : Fin n → ℝ) (hratio : ∀ i, h i = q i * f i) :
    InteriorLogProfileKKT T weights f h ↔
      (routingMatrix T q f).transpose.mulVec (fun i => (weights i : ℝ)) =
        fun i => (weights i : ℝ) := by
  constructor
  · intro hkkt
    funext k
    have hk := hkkt k
    rw [formalLogResponseGradient_eq_routingResidual T weights q f h hratio k] at hk
    linarith
  · intro hstationary k
    rw [formalLogResponseGradient_eq_routingResidual T weights q f h hratio k,
      hstationary]
    simp

theorem formalLogResponseGradient_sum_eq_zero {n : ℕ}
    (T : Matrix (Fin n) (Fin n) ℝ) (weights : Fin n → ℕ)
    (q f h : Fin n → ℝ) (hratio : ∀ i, h i = q i * f i)
    (hrow : RowStochastic (routingMatrix T q f)) :
    ∑ k, formalLogResponseGradient T weights f h k = 0 := by
  simp_rw [formalLogResponseGradient_eq_routingResidual T weights q f h hratio]
  rw [Finset.sum_sub_distrib]
  change (∑ k, ∑ i, routingMatrix T q f i k * (weights i : ℝ)) -
      ∑ k, (weights k : ℝ) = 0
  rw [Finset.sum_comm]
  have heach : ∀ i, (∑ k, routingMatrix T q f i k * (weights i : ℝ)) =
      weights i := by
    intro i
    rw [← Finset.sum_mul, hrow i]
    simp
  simp_rw [heach]
  exact sub_self _

/-- Along the `k`th log-profile coordinate, the response image changes by
`(exp t - 1) T_{ki} f_k`.  Constants independent of `t` are omitted. -/
def coordinateLogProfileObjective {n : ℕ}
    (T : Matrix (Fin n) (Fin n) ℝ) (weights : Fin n → ℕ)
    (f h : Fin n → ℝ) (k : Fin n) (t : ℝ) : ℝ :=
  ∑ i, (weights i : ℝ) *
    (Real.log (h i + (Real.exp t - 1) * (T k i * f k)) -
      if i = k then t else 0)

theorem coordinateLogProfileObjective_hasDerivAt {n : ℕ}
    (T : Matrix (Fin n) (Fin n) ℝ) (weights : Fin n → ℕ)
    (f h : Fin n → ℝ) (k : Fin n) (hh : ∀ i, 0 < h i) :
    HasDerivAt (coordinateLogProfileObjective T weights f h k)
      (formalLogResponseGradient T weights f h k) 0 := by
  unfold coordinateLogProfileObjective formalLogResponseGradient
  have hterm : ∀ i : Fin n, HasDerivAt
      (fun t => (weights i : ℝ) *
        (Real.log (h i + (Real.exp t - 1) * (T k i * f k)) -
          if i = k then t else 0))
      ((weights i : ℝ) * ((T k i * f k) / h i - if i = k then 1 else 0)) 0 := by
    intro i
    have hmass : HasDerivAt
        (fun t => h i + (Real.exp t - 1) * (T k i * f k))
        (T k i * f k) 0 := by
      convert (((Real.hasDerivAt_exp 0).sub_const 1).mul_const
        (T k i * f k)).const_add (h i) using 1
      all_goals simp [Real.exp_zero]
    have hpenalty : HasDerivAt (fun t : ℝ => if i = k then t else 0)
        (if i = k then 1 else 0) 0 := by
      by_cases hik : i = k
      · simp only [hik, if_true]
        exact hasDerivAt_id (x := 0)
      · simp only [hik, if_false]
        exact hasDerivAt_const (x := 0) (0 : ℝ)
    convert ((hmass.log (by simpa using ne_of_gt (hh i))).sub hpenalty).const_mul
      (weights i : ℝ) using 1
    all_goals simp [Real.exp_zero]
  convert HasDerivAt.fun_sum (u := Finset.univ) (fun i hi => hterm i) using 1
  rw [show (∑ i, (weights i : ℝ) *
      (T k i * f k / h i - if i = k then 1 else 0)) =
      (∑ i, (weights i : ℝ) * T k i * f k / h i) -
        ∑ i, (weights i : ℝ) * (if i = k then 1 else 0) by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring]
  simp

def InteriorLogProfileMinimizer {n : ℕ}
    (T : Matrix (Fin n) (Fin n) ℝ) (weights : Fin n → ℕ)
    (f h : Fin n → ℝ) : Prop :=
  ∀ k, IsLocalMin (coordinateLogProfileObjective T weights f h k) 0

/-- Every unconstrained interior log-profile minimizer satisfies the
matrix-scaling stationarity equations. -/
theorem interiorLogProfileMinimizer_implies_routingStationary {n : ℕ}
    (T : Matrix (Fin n) (Fin n) ℝ) (weights : Fin n → ℕ)
    (q f h : Fin n → ℝ) (hratio : ∀ i, h i = q i * f i)
    (hh : ∀ i, 0 < h i)
    (hmin : InteriorLogProfileMinimizer T weights f h) :
    (routingMatrix T q f).transpose.mulVec (fun i => (weights i : ℝ)) =
      fun i => (weights i : ℝ) := by
  apply (interiorLogProfileKKT_iff_routingStationary T weights q f h hratio).mp
  intro k
  exact (hmin k).hasDerivAt_eq_zero
    (coordinateLogProfileObjective_hasDerivAt T weights f h k hh)

end
end OptimalAffinityRealizability
