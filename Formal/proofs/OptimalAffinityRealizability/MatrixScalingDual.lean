import proofs.OptimalAffinityRealizability.MatrixScalingKKT

namespace OptimalAffinityRealizability

open scoped BigOperators
noncomputable section

def logResponseObjective {n : ℕ} (T : Matrix (Fin n) (Fin n) ℝ)
    (g f : Fin n → ℝ) : ℝ :=
  ∑ i, g i *
    (Real.log (OptimalAffinityCorrected.responseImage T f i) - Real.log (f i))

def routingEntropy {n : ℕ} (T P : Matrix (Fin n) (Fin n) ℝ)
    (g : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, g i * P i j * Real.log (T j i / P i j)

/-- At an interior response profile, the induced routing entropy is exactly
the log response objective whenever the prescribed production weights are
stationary.  This is the attained strong-duality identity behind the
matrix-scaling interpretation. -/
theorem routingEntropy_induced_eq_logResponseObjective {n : ℕ}
    (T : Matrix (Fin n) (Fin n) ℝ) (g q f h : Fin n → ℝ)
    (hT : ∀ i j, 0 < T i j) (hf : ∀ i, 0 < f i)
    (hh : ∀ i, 0 < h i)
    (hresponse : T.transpose.mulVec f = h)
    (hratio : ∀ i, h i = q i * f i)
    (hstationary : (routingMatrix T q f).transpose.mulVec g = g) :
    routingEntropy T (routingMatrix T q f) g =
      logResponseObjective T g f := by
  let P := routingMatrix T q f
  have hrow : RowStochastic P :=
    routingMatrix_rowStochastic T q f h hresponse hratio hf
      (fun i => by
        have hmul : 0 < q i * f i := by rw [← hratio i]; exact hh i
        exact pos_of_mul_pos_left hmul (le_of_lt (hf i)))
  have hlog : ∀ i j,
      Real.log (T j i / P i j) = Real.log (h i) - Real.log (f j) := by
    intro i j
    have hratioEq : T j i / P i j = h i / f j := by
      unfold P routingMatrix
      rw [← hratio i]
      simp only [Matrix.transpose_apply]
      field_simp [ne_of_gt (hT j i), ne_of_gt (hf j), ne_of_gt (hh i)]
    rw [hratioEq, Real.log_div (ne_of_gt (hh i)) (ne_of_gt (hf j))]
  unfold routingEntropy logResponseObjective
  change (∑ i, ∑ j, g i * P i j * Real.log (T j i / P i j)) = _
  simp_rw [hlog]
  calc
    (∑ i, ∑ j, g i * P i j * (Real.log (h i) - Real.log (f j))) =
        (∑ i, g i * Real.log (h i)) -
          ∑ j, g j * Real.log (f j) := by
      rw [show (∑ i, ∑ j, g i * P i j *
          (Real.log (h i) - Real.log (f j))) =
          (∑ i, ∑ j, g i * P i j * Real.log (h i)) -
            (∑ i, ∑ j, g i * P i j * Real.log (f j)) by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        ring]
      congr 1
      · apply Finset.sum_congr rfl
        intro i hi
        rw [show (∑ j, g i * P i j * Real.log (h i)) =
            (∑ j, P i j) * (g i * Real.log (h i)) by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro j hj
          ring]
        rw [hrow i]
        ring
      · rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j hj
        rw [show (∑ i, g i * P i j * Real.log (f j)) =
            (∑ i, P i j * g i) * Real.log (f j) by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i hi
          ring]
        change (P.transpose.mulVec g j) * Real.log (f j) =
          g j * Real.log (f j)
        rw [hstationary]
    _ = ∑ i, g i * (Real.log (h i) - Real.log (f i)) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = ∑ i, g i *
        (Real.log (OptimalAffinityCorrected.responseImage T f i) -
          Real.log (f i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [responseImage_eq_transpose_mulVec T f, hresponse]

/-- The compiled KKT equations therefore produce an attained entropy-dual
witness for the weighted response objective. -/
theorem interiorKKT_has_attainedMatrixScalingWitness {n : ℕ}
    (T : Matrix (Fin n) (Fin n) ℝ) (weights : Fin n → ℕ)
    (q f h : Fin n → ℝ)
    (hT : ∀ i j, 0 < T i j) (hf : ∀ i, 0 < f i)
    (hh : ∀ i, 0 < h i)
    (hresponse : T.transpose.mulVec f = h)
    (hratio : ∀ i, h i = q i * f i)
    (hkkt : InteriorLogProfileKKT T weights f h) :
    routingEntropy T (routingMatrix T q f) (fun i => (weights i : ℝ)) =
      logResponseObjective T (fun i => (weights i : ℝ)) f := by
  apply routingEntropy_induced_eq_logResponseObjective T
    (fun i => (weights i : ℝ)) q f h hT hf hh hresponse hratio
  exact (interiorLogProfileKKT_iff_routingStationary
    T weights q f h hratio).mp hkkt

end
end OptimalAffinityRealizability
