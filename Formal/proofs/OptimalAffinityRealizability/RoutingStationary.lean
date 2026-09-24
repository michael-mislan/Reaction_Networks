import proofs.OptimalAffinityRealizability.Capacity
import proofs.DegradationControl.PerronExistence

namespace OptimalAffinityRealizability

open Matrix
open DegradationControl
open scoped BigOperators
noncomputable section

/-- An irreducible nonnegative row-stochastic matrix has a normalized strictly
positive stationary column vector.  This is the left Perron vector needed by
the kinetic curvature certificate. -/
theorem irreducibleRowStochastic_exists_positiveStationary {n : ℕ}
    [Nonempty (Fin n)] (P : Matrix (Fin n) (Fin n) ℝ)
    (hP : ∀ i j, 0 ≤ P i j) (hirr : P.IsIrreducible)
    (hrow : RowStochastic P) :
    ∃ pi : Fin n → ℝ, (∀ i, 0 < pi i) ∧
      (∑ i, pi i = 1) ∧ P.transpose.mulVec pi = pi := by
  obtain ⟨rho, pi, hpi, heig, hspectral⟩ :=
    irreducibleNonnegative_exists_realSpectralBound P.transpose
      (fun i j => by simpa using hP j i) hirr.transpose
  have hPone : P.mulVec (fun _ => (1 : ℝ)) = fun _ => (1 : ℝ) := by
    funext i
    simpa [Matrix.mulVec, dotProduct] using hrow i
  have hbil := Matrix.dotProduct_transpose_mulVec P (fun _ => (1 : ℝ)) pi
  have hrho : rho = 1 := by
    rw [heig, hPone] at hbil
    simp only [Pi.smul_apply, smul_eq_mul, dotProduct, one_mul] at hbil
    rw [← Finset.mul_sum, hpi.2, mul_one] at hbil
    simp only [mul_one] at hbil
    rw [hpi.2] at hbil
    exact hbil
  refine ⟨pi, hpi.1, hpi.2, ?_⟩
  simpa [hrho] using heig

/-- The stationary routing vector transports through the positive diagonal
similarity to a left-nullvector of the response Laplacian. -/
theorem responseLaplacian_exists_positiveLeftNull {n : ℕ}
    [Nonempty (Fin n)] (T : Matrix (Fin n) (Fin n) ℝ)
    (q f h : Fin n → ℝ)
    (hresponse : T.transpose.mulVec f = h)
    (hratio : ∀ i, h i = q i * f i)
    (hf : ∀ i, 0 < f i) (hq : ∀ i, 0 < q i)
    (hP : ∀ i j, 0 ≤ routingMatrix T q f i j)
    (hirr : (routingMatrix T q f).IsIrreducible) :
    ∃ mu : Fin n → ℝ, (∀ i, 0 < mu i) ∧
      (responseLaplacian T q).transpose.mulVec mu = 0 := by
  let P := routingMatrix T q f
  have hrow : RowStochastic P :=
    routingMatrix_rowStochastic T q f h hresponse hratio hf hq
  obtain ⟨pi, hpipos, hpisum, hpistat⟩ :=
    irreducibleRowStochastic_exists_positiveStationary P hP hirr hrow
  let mu : Fin n → ℝ := fun i => pi i / (q i * f i)
  have hmupos : ∀ i, 0 < mu i := by
    intro i
    exact div_pos (hpipos i) (mul_pos (hq i) (hf i))
  refine ⟨mu, hmupos, ?_⟩
  rw [responseLaplacian_routing_factorization T q f hf hq]
  simp only [Matrix.transpose_mul, Matrix.diagonal_transpose]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have hdiag : (Matrix.diagonal (fun i => q i * f i)).mulVec mu = pi := by
    funext i
    simp only [Matrix.mulVec_diagonal]
    change (q i * f i) * (pi i / (q i * f i)) = pi i
    rw [← mul_div_assoc]
    exact mul_div_cancel_left₀ (pi i) (ne_of_gt (mul_pos (hq i) (hf i)))
  rw [hdiag]
  have hmiddle : (1 - P).transpose.mulVec pi = 0 := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.sub_mulVec,
      Matrix.one_mulVec, hpistat, sub_self]
  rw [hmiddle, Matrix.mulVec_zero]

/-- Positive irreducible response routing automatically supplies the positive
left-nullvector required by the literal current-Jacobian curvature theorem. -/
theorem literalCurrentJacobian_exists_positiveLeftNull {n : ℕ}
    [Nonempty (Fin n)] (source : SquareSource n) (J : ℝ)
    (production q f h : Fin n → ℝ)
    (hJ : 0 < J) (hproduction : ∀ i, 0 < production i)
    (hq : ∀ i, 1 < q i) (hf : ∀ i, 0 < f i)
    (hresponse : (responseMatrix source).transpose.mulVec f = h)
    (hratio : ∀ i, h i = q i * f i)
    (hP : ∀ i j, 0 ≤ routingMatrix (responseMatrix source) q f i j)
    (hirr : (routingMatrix (responseMatrix source) q f).IsIrreducible) :
    ∃ lambda : Fin n → ℝ, (∀ i, 0 < lambda i) ∧
      (literalCurrentJacobian source J production q).transpose.mulVec lambda = 0 := by
  have hqpos : ∀ i, 0 < q i := fun i => lt_trans zero_lt_one (hq i)
  obtain ⟨mu, hmupos, hmu⟩ := responseLaplacian_exists_positiveLeftNull
    (responseMatrix source) q f h hresponse hratio hf hqpos hP hirr
  let reverse := reconstructedReverseFlow J production q
  have hreverse : ∀ i, 0 < reverse i := by
    exact (reconstructedFlows_positive J production q hJ hproduction hq).1
  let lambda : Fin n → ℝ := fun i => mu i / reverse i
  have hlambdapos : ∀ i, 0 < lambda i := by
    intro i
    exact div_pos (hmupos i) (hreverse i)
  refine ⟨lambda, hlambdapos, ?_⟩
  rw [currentJacobian_factor_responseLaplacian source J production q hq]
  unfold factoredCurrentJacobian
  simp only [Matrix.transpose_mul, Matrix.diagonal_transpose]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have hdiag : (Matrix.diagonal reverse).mulVec lambda = mu := by
    funext i
    simp only [Matrix.mulVec_diagonal]
    change reverse i * (mu i / reverse i) = mu i
    rw [← mul_div_assoc]
    exact mul_div_cancel_left₀ (mu i) (ne_of_gt (hreverse i))
  rw [hdiag, hmu, Matrix.mulVec_zero]

/-- Every normalized positive profile with irreducible nonnegative routing is
strict-local realizable for the literal source.  The Perron construction above
removes the left-nullvector from the user-facing hypotheses. -/
theorem irreducibleRouting_strictLocalRealizable {n : ℕ}
    [Nonempty (Fin n)] (source : SquareSource n) (J : ℝ)
    (production q f h : Fin n → ℝ)
    (hJ : 0 < J) (hproduction : ∀ i, 0 < production i)
    (hq : ∀ i, 1 < q i) (hf : ∀ i, 0 < f i)
    (hresponse : (responseMatrix source).transpose.mulVec f = h)
    (hratio : ∀ i, h i = q i * f i)
    (hmode : ControlledProductionMode source production)
    (hP : ∀ i j, 0 ≤ routingMatrix (responseMatrix source) q f i j)
    (hirr : (routingMatrix (responseMatrix source) q f).IsIrreducible)
    (hcontrol : controlCovector source f = 1) :
    StrictLocalRealizable source J production f := by
  obtain ⟨lambda, hlambdapos, hleft⟩ :=
    literalCurrentJacobian_exists_positiveLeftNull source J production q f h
      hJ hproduction hq hf hresponse hratio hP hirr
  have hlambda0 : lambda ≠ 0 := by
    intro hlambda
    let i : Fin n := Classical.choice (inferInstance : Nonempty (Fin n))
    have hi := hlambdapos i
    rw [hlambda] at hi
    simp at hi
  have hnormalized : responseTangent source f source.controlled = 1 := by
    exact hcontrol
  have cert : RegularStrictLocalSourceCertificate source J production q
      f h (responseTangent source f) lambda :=
    exists_regularStrictLocalSourceCertificate source J production q f h
      (responseTangent source f) lambda hJ hproduction hq hf hresponse
      hratio hmode hP hirr (reactantResponse_responseTangent source f)
      hleft (fun i => le_of_lt (hlambdapos i)) hlambda0 hnormalized
  exact ⟨{
    q := q
    h := h
    u := responseTangent source f
    lambda := lambda
    certificate := cert
  }⟩

theorem responseTangent_smul {n : ℕ} (source : SquareSource n)
    (a : ℝ) (f : Fin n → ℝ) :
    responseTangent source (a • f) = a • responseTangent source f := by
  apply reactantTranspose_mulVec_injective source
  rw [reactantResponse_responseTangent, Matrix.mulVec_smul,
    reactantResponse_responseTangent]

theorem routingMatrix_smul {n : ℕ} (T : Matrix (Fin n) (Fin n) ℝ)
    (q f : Fin n → ℝ) (a : ℝ) (ha : a ≠ 0) :
    routingMatrix T q (a • f) = routingMatrix T q f := by
  ext i j
  unfold routingMatrix
  simp only [Matrix.transpose_apply, Pi.smul_apply, smul_eq_mul]
  field_simp [ha]

/-- Every control-accessible positive irreducible response ray has a normalized
representative realized by a strict local kinetic maximum.  Thus on this
explicit source class pointwise ray realization is stronger than density. -/
theorem controlAccessible_irreducibleRouting_rayStrictLocalRealizable {n : ℕ}
    [Nonempty (Fin n)] (source : SquareSource n) (J : ℝ)
    (production q f h : Fin n → ℝ)
    (hJ : 0 < J) (hproduction : ∀ i, 0 < production i)
    (hq : ∀ i, 1 < q i) (hf : ∀ i, 0 < f i)
    (hresponse : (responseMatrix source).transpose.mulVec f = h)
    (hratio : ∀ i, h i = q i * f i)
    (hmode : ControlledProductionMode source production)
    (hP : ∀ i j, 0 ≤ routingMatrix (responseMatrix source) q f i j)
    (hirr : (routingMatrix (responseMatrix source) q f).IsIrreducible)
    (haccessible : ControlAccessible source f) :
    RayStrictLocalRealizable source J production f := by
  let a := (controlCovector source f)⁻¹
  have ha : 0 < a := inv_pos.mpr haccessible
  let f' := a • f
  let h' := a • h
  have hf' : ∀ i, 0 < f' i := by
    intro i
    exact smul_pos ha (hf i)
  have hresponse' : (responseMatrix source).transpose.mulVec f' = h' := by
    rw [Matrix.mulVec_smul, hresponse]
  have hratio' : ∀ i, h' i = q i * f' i := by
    intro i
    simp only [h', f', Pi.smul_apply, smul_eq_mul, hratio i]
    ring
  have hrouting : routingMatrix (responseMatrix source) q f' =
      routingMatrix (responseMatrix source) q f :=
    routingMatrix_smul (responseMatrix source) q f a (ne_of_gt ha)
  have hcontrol' : controlCovector source f' = 1 := by
    unfold controlCovector
    rw [responseTangent_smul]
    change a * controlCovector source f = 1
    exact inv_mul_cancel₀ (ne_of_gt haccessible)
  have hstrict : StrictLocalRealizable source J production f' :=
    irreducibleRouting_strictLocalRealizable source J production q f' h'
      hJ hproduction hq hf' hresponse' hratio' hmode
      (by simpa [hrouting] using hP) (by simpa [hrouting] using hirr) hcontrol'
  exact ⟨f', ⟨a, ha, rfl⟩, hstrict⟩

end
end OptimalAffinityRealizability
