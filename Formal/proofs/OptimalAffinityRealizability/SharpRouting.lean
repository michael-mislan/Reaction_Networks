import proofs.OptimalAffinityRealizability.RoutingStationary

namespace OptimalAffinityRealizability

open Matrix
open DegradationControl
open scoped BigOperators
noncomputable section

/-- A primitive graph condition for a finite routing matrix: one state is
reachable with positive path weight from every state.  For a finite Markov
chain this is equivalent to having exactly one final communicating class. -/
def HasCommonReachableState {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∃ root : Fin n, ∀ i : Fin n, ∃ k : ℕ, 0 < (P ^ k) i root

theorem nonnegative_fixed_zero_at_source_zero_at_reachable {n : ℕ}
    (P : Matrix (Fin n) (Fin n) ℝ) (hP : ∀ i j, 0 ≤ P i j)
    (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hfixed : P.mulVec w = w) (i root : Fin n) (hi : w i = 0)
    (hreach : ∃ k : ℕ, 0 < (P ^ k) i root) : w root = 0 := by
  obtain ⟨k, hk⟩ := hreach
  have hpowNonneg : ∀ a b, 0 ≤ (P ^ k) a b := Matrix.pow_apply_nonneg hP k
  have hsum : ∑ j, (P ^ k) i j * w j = 0 := by
    change (P ^ k).mulVec w i = 0
    rw [pow_mulVec_fixed P w hfixed k, hi]
  have hterm : (P ^ k) i root * w root = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => mul_nonneg (hpowNonneg i j) (hw j))).mp hsum root
        (Finset.mem_univ root)
  exact (mul_eq_zero.mp hterm).resolve_left (ne_of_gt hk)

/-- The sharp one-final-class maximum principle, stated using the primitive
common-reachable-state condition. -/
theorem commonReachable_rowStochastic_fixedSpaceOne {n : ℕ} [Nonempty (Fin n)]
    (P : Matrix (Fin n) (Fin n) ℝ)
    (hP : ∀ i j, 0 ≤ P i j) (hroot : HasCommonReachableState P)
    (hrow : RowStochastic P) : FixedSpaceOne P := by
  intro v hfixed
  obtain ⟨root, hreach⟩ := hroot
  obtain ⟨imax, _, hmax⟩ :=
    Finset.exists_max_image Finset.univ v Finset.univ_nonempty
  obtain ⟨imin, _, hmin⟩ :=
    Finset.exists_min_image Finset.univ v Finset.univ_nonempty
  let wmax : Fin n → ℝ := fun j => v imax - v j
  let wmin : Fin n → ℝ := fun j => v j - v imin
  have hwmax : ∀ j, 0 ≤ wmax j := by
    intro j
    exact sub_nonneg.mpr (hmax j (Finset.mem_univ j))
  have hwmin : ∀ j, 0 ≤ wmin j := by
    intro j
    exact sub_nonneg.mpr (hmin j (Finset.mem_univ j))
  have hwmaxfixed : P.mulVec wmax = wmax := by
    funext i
    change (∑ j, P i j * (v imax - v j)) = v imax - v i
    calc
      (∑ j, P i j * (v imax - v j)) =
          (∑ j, P i j) * v imax - ∑ j, P i j * v j := by
            simp_rw [mul_sub]
            rw [Finset.sum_sub_distrib, Finset.sum_mul]
      _ = v imax - v i := by
        rw [hrow i]
        change 1 * v imax - P.mulVec v i = v imax - v i
        rw [hfixed]
        ring
  have hwminfixed : P.mulVec wmin = wmin := by
    funext i
    change (∑ j, P i j * (v j - v imin)) = v i - v imin
    calc
      (∑ j, P i j * (v j - v imin)) =
          ∑ j, P i j * v j - (∑ j, P i j) * v imin := by
            simp_rw [mul_sub]
            rw [Finset.sum_sub_distrib, Finset.sum_mul]
      _ = v i - v imin := by
        rw [hrow i]
        change P.mulVec v i - 1 * v imin = v i - v imin
        rw [hfixed]
        ring
  have hwmaxroot : wmax root = 0 :=
    nonnegative_fixed_zero_at_source_zero_at_reachable P hP wmax hwmax
      hwmaxfixed imax root (by simp [wmax]) (hreach imax)
  have hwminroot : wmin root = 0 :=
    nonnegative_fixed_zero_at_source_zero_at_reachable P hP wmin hwmin
      hwminfixed imin root (by simp [wmin]) (hreach imin)
  refine ⟨v root, ?_⟩
  funext j
  have hjmax := hwmax j
  have hjmin := hwmin j
  simp only [wmax] at hwmaxroot hjmax
  simp only [wmin] at hwminroot hjmin
  linarith

/-- A common reachable routing state is sufficient for the exact one-ray
response kernel statement; irreducibility is unnecessary. -/
theorem commonReachable_routing_responseKernelOne {n : ℕ} [Nonempty (Fin n)]
    (T : Matrix (Fin n) (Fin n) ℝ) (q f h : Fin n → ℝ)
    (hresponse : T.transpose.mulVec f = h)
    (hratio : ∀ i, h i = q i * f i)
    (hf : ∀ i, 0 < f i) (hq : ∀ i, 0 < q i)
    (hP : ∀ i j, 0 ≤ routingMatrix T q f i j)
    (hroot : HasCommonReachableState (routingMatrix T q f)) :
    ResponseKernelOne T q f := by
  apply fixedSpaceOne_implies_responseKernelOne T q f h hresponse hratio hf hq
  exact commonReachable_rowStochastic_fixedSpaceOne
    (routingMatrix T q f) hP hroot
      (routingMatrix_rowStochastic T q f h hresponse hratio hf hq)

/-- Every finite nonnegative row-stochastic matrix has a normalized
nonnegative stationary column vector. -/
theorem rowStochastic_exists_nonnegativeStationary {n : ℕ} [Nonempty (Fin n)]
    (P : Matrix (Fin n) (Fin n) ℝ)
    (hP : ∀ i j, 0 ≤ P i j) (hrow : RowStochastic P) :
    ∃ pi : Fin n → ℝ, (∀ i, 0 ≤ pi i) ∧
      (∑ i, pi i = 1) ∧ P.transpose.mulVec pi = pi := by
  obtain ⟨rho, pi, hpi, heig⟩ :=
    nonnegativeMatrix_exists_normalizedNonnegative_eigenvector P.transpose
      (fun i j => by simpa using hP j i)
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

/-- The response Laplacian always has a nonzero nonnegative left nullvector
when its routing is nonnegative; strict positivity is not needed for curvature. -/
theorem responseLaplacian_exists_nonnegativeLeftNull {n : ℕ}
    [Nonempty (Fin n)] (T : Matrix (Fin n) (Fin n) ℝ)
    (q f h : Fin n → ℝ)
    (hresponse : T.transpose.mulVec f = h)
    (hratio : ∀ i, h i = q i * f i)
    (hf : ∀ i, 0 < f i) (hq : ∀ i, 0 < q i)
    (hP : ∀ i j, 0 ≤ routingMatrix T q f i j) :
    ∃ mu : Fin n → ℝ, (∀ i, 0 ≤ mu i) ∧ mu ≠ 0 ∧
      (responseLaplacian T q).transpose.mulVec mu = 0 := by
  let P := routingMatrix T q f
  have hrow : RowStochastic P :=
    routingMatrix_rowStochastic T q f h hresponse hratio hf hq
  obtain ⟨pi, hpinonneg, hpisum, hpistat⟩ :=
    rowStochastic_exists_nonnegativeStationary P hP hrow
  let mu : Fin n → ℝ := fun i => pi i / (q i * f i)
  have hmunonneg : ∀ i, 0 ≤ mu i := by
    intro i
    exact div_nonneg (hpinonneg i) (le_of_lt (mul_pos (hq i) (hf i)))
  have hmu0 : mu ≠ 0 := by
    intro hz
    have hpi0 : pi = 0 := by
      funext i
      have hi := congrFun hz i
      simp only [mu] at hi
      exact (div_eq_zero_iff).mp hi |>.resolve_right
        (mul_ne_zero (ne_of_gt (hq i)) (ne_of_gt (hf i)))
    rw [hpi0] at hpisum
    simp at hpisum
  refine ⟨mu, hmunonneg, hmu0, ?_⟩
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

/-- Common-reachable routing plus the primitive source data gives the full
algebraic branch certificate. -/
theorem exists_algebraicBranchCertificate_of_commonReachable {n : ℕ}
    [Nonempty (Fin n)]
    (source : SquareSource n) (J : ℝ) (g q f h u lambda : Fin n → ℝ)
    (hJ : 0 < J) (hg : ∀ i, 0 < g i) (hq : ∀ i, 1 < q i)
    (hf : ∀ i, 0 < f i)
    (hresponse : (responseMatrix source).transpose.mulVec f = h)
    (hratio : ∀ i, h i = q i * f i)
    (hmode : ControlledProductionMode source g)
    (hP : ∀ i j, 0 ≤ routingMatrix (responseMatrix source) q f i j)
    (hroot : HasCommonReachableState
      (routingMatrix (responseMatrix source) q f))
    (hreactant : source.reactant.transpose.mulVec u = f)
    (hleft : (literalCurrentJacobian source J g q).transpose.mulVec lambda = 0)
    (htransverse : dotProduct lambda g ≠ 0)
    (hcontrol : u source.controlled ≠ 0) :
    AlgebraicBranchCertificate source J g q f h u lambda := by
  have hqpos : ∀ i, 0 < q i := fun i => lt_trans zero_lt_one (hq i)
  have hresponseKernel : ResponseKernelOne (responseMatrix source) q f :=
    commonReachable_routing_responseKernelOne (responseMatrix source) q f h
      hresponse hratio hf hqpos hP hroot
  have hfactoredKernel : MatrixKernelOne
      (factoredCurrentJacobian source J g q) u :=
    factoredCurrentJacobian_matrixKernelOne source J g q u f
      hJ hg hq hresponseKernel hreactant
  have hliteralKernel : MatrixKernelOne
      (literalCurrentJacobian source J g q) u := by
    rw [currentJacobian_factor_responseLaplacian source J g q hq]
    exact hfactoredKernel
  refine {
    firstOrder := exists_firstOrderSourceRealization source J g q f h
      hJ hg hq hratio hmode
    responseKernel := hresponseKernel
    currentKernel := hliteralKernel
    leftNull := hleft
    transverse := htransverse
    reducedSteady := matrixKernelOne_noncontrolledSteadyJacobianInjective
      source (literalCurrentJacobian source J g q) u g lambda
      hliteralKernel hmode hleft htransverse hcontrol
  }

/-- Nonnegative routing supplies the nonzero nonnegative left nullvector needed
by the strict-curvature theorem, even when transient routing states are present. -/
theorem literalCurrentJacobian_exists_nonnegativeLeftNull {n : ℕ}
    [Nonempty (Fin n)] (source : SquareSource n) (J : ℝ)
    (g q f h : Fin n → ℝ)
    (hJ : 0 < J) (hg : ∀ i, 0 < g i)
    (hq : ∀ i, 1 < q i) (hf : ∀ i, 0 < f i)
    (hresponse : (responseMatrix source).transpose.mulVec f = h)
    (hratio : ∀ i, h i = q i * f i)
    (hP : ∀ i j, 0 ≤ routingMatrix (responseMatrix source) q f i j) :
    ∃ lambda : Fin n → ℝ, (∀ i, 0 ≤ lambda i) ∧ lambda ≠ 0 ∧
      (literalCurrentJacobian source J g q).transpose.mulVec lambda = 0 := by
  have hqpos : ∀ i, 0 < q i := fun i => lt_trans zero_lt_one (hq i)
  obtain ⟨mu, hmunonneg, hmu0, hmu⟩ :=
    responseLaplacian_exists_nonnegativeLeftNull
      (responseMatrix source) q f h hresponse hratio hf hqpos hP
  let reverse := reconstructedReverseFlow J g q
  have hreverse : ∀ i, 0 < reverse i :=
    (reconstructedFlows_positive J g q hJ hg hq).1
  let lambda : Fin n → ℝ := fun i => mu i / reverse i
  have hlambdanonneg : ∀ i, 0 ≤ lambda i := by
    intro i
    exact div_nonneg (hmunonneg i) (le_of_lt (hreverse i))
  have hlambda0 : lambda ≠ 0 := by
    intro hz
    apply hmu0
    funext i
    have hi := congrFun hz i
    simp only [lambda] at hi
    exact ((div_eq_zero_iff).mp hi).resolve_right (ne_of_gt (hreverse i))
  refine ⟨lambda, hlambdanonneg, hlambda0, ?_⟩
  rw [currentJacobian_factor_responseLaplacian source J g q hq]
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

/-- The sharp local theorem: common-reachable (equivalently one-final-class)
routing replaces irreducibility, including transient routing coordinates. -/
theorem commonReachableRouting_strictLocalRealizable {n : ℕ}
    [Nonempty (Fin n)] (source : SquareSource n) (J : ℝ)
    (g q f h : Fin n → ℝ)
    (hJ : 0 < J) (hg : ∀ i, 0 < g i)
    (hq : ∀ i, 1 < q i) (hf : ∀ i, 0 < f i)
    (hresponse : (responseMatrix source).transpose.mulVec f = h)
    (hratio : ∀ i, h i = q i * f i)
    (hmode : ControlledProductionMode source g)
    (hP : ∀ i j, 0 ≤ routingMatrix (responseMatrix source) q f i j)
    (hroot : HasCommonReachableState
      (routingMatrix (responseMatrix source) q f))
    (hcontrol : controlCovector source f = 1) :
    StrictLocalRealizable source J g f := by
  obtain ⟨lambda, hlambda, hlambda0, hleft⟩ :=
    literalCurrentJacobian_exists_nonnegativeLeftNull source J g q f h
      hJ hg hq hf hresponse hratio hP
  let u := responseTangent source f
  have hreactant : source.reactant.transpose.mulVec u = f :=
    reactantResponse_responseTangent source f
  have hcontrol' : u source.controlled = 1 := hcontrol
  have htransverse : dotProduct lambda g ≠ 0 :=
    ne_of_gt (dotProduct_pos_of_nonnegative_nonzero_left lambda g
      hlambda hlambda0 hg)
  have halgebraic : AlgebraicBranchCertificate source J g q f h u lambda :=
    exists_algebraicBranchCertificate_of_commonReachable source J g q f h
      u lambda hJ hg hq hf hresponse hratio hmode hP hroot hreactant
      hleft htransverse (by rw [hcontrol']; norm_num)
  have hproduct : source.product.transpose.mulVec u = h := by
    calc
      source.product.transpose.mulVec u =
          source.product.transpose.mulVec (responseTangent source f) := rfl
      _ = productResponse source f := rfl
      _ = (responseMatrix source).transpose.mulVec f :=
        productResponse_eq_responseMatrix_transpose_mulVec source f
      _ = h := hresponse
  have cert : RegularStrictLocalSourceCertificate source J g q f h u lambda := {
    positiveCurrent := hJ
    positiveProduction := hg
    positiveRatio := hq
    positiveResponse := hf
    productionMode := hmode
    algebraic := halgebraic
    reactantResponse := hreactant
    productResponse := hproduct
    responseRatio := hratio
    leftNonnegative := hlambda
    leftNonzero := hlambda0
    normalizedControl := hcontrol'
  }
  exact ⟨{
    q := q
    h := h
    u := u
    lambda := lambda
    certificate := cert
  }⟩

/-- Control accessibility normalizes a common-reachable response ray to the
sharp strict-local theorem. -/
theorem controlAccessible_commonReachableRouting_rayStrictLocalRealizable
    {n : ℕ} [Nonempty (Fin n)] (source : SquareSource n) (J : ℝ)
    (g q f h : Fin n → ℝ)
    (hJ : 0 < J) (hg : ∀ i, 0 < g i)
    (hq : ∀ i, 1 < q i) (hf : ∀ i, 0 < f i)
    (hresponse : (responseMatrix source).transpose.mulVec f = h)
    (hratio : ∀ i, h i = q i * f i)
    (hmode : ControlledProductionMode source g)
    (hP : ∀ i j, 0 ≤ routingMatrix (responseMatrix source) q f i j)
    (hroot : HasCommonReachableState
      (routingMatrix (responseMatrix source) q f))
    (haccessible : ControlAccessible source f) :
    RayStrictLocalRealizable source J g f := by
  let a := (controlCovector source f)⁻¹
  have ha : 0 < a := inv_pos.mpr haccessible
  let f' := a • f
  let h' := a • h
  have hf' : ∀ i, 0 < f' i := fun i => smul_pos ha (hf i)
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
  have hstrict : StrictLocalRealizable source J g f' :=
    commonReachableRouting_strictLocalRealizable source J g q f' h'
      hJ hg hq hf' hresponse' hratio' hmode
      (by simpa [hrouting] using hP) (by simpa [hrouting] using hroot) hcontrol'
  exact ⟨f', ⟨a, ha, rfl⟩, hstrict⟩


end
end OptimalAffinityRealizability
