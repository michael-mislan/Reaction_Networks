import proofs.OptimalAffinityRealizability.RoutingCorank

namespace OptimalAffinityRealizability

open Matrix
noncomputable section

def MatrixKernelOne {n : ℕ} (E : Matrix (Fin n) (Fin n) ℝ)
    (u : Fin n → ℝ) : Prop :=
  ∀ v, E.mulVec v = 0 ↔ ∃ c : ℝ, v = c • u

def ControlReducedInjective {n : ℕ} (E : Matrix (Fin n) (Fin n) ℝ)
    (controlled : Fin n) : Prop :=
  ∀ v, E.mulVec v = 0 → v controlled = 0 → v = 0

def NoncontrolledSteadyJacobianInjective {n : ℕ} (source : SquareSource n)
    (E : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ w, w source.controlled = 0 →
    (∀ i, i ≠ source.controlled →
      source.netStoich.mulVec (E.mulVec w) i = 0) → w = 0

theorem diagonal_mulVec_injective_of_positive {n : ℕ} (d : Fin n → ℝ)
    (hd : ∀ i, 0 < d i) : Function.Injective (Matrix.diagonal d).mulVec := by
  intro x y hxy
  funext i
  have hi := congrFun hxy i
  simp only [Matrix.mulVec_diagonal] at hi
  nlinarith [hd i]

theorem matrixKernelOne_triple {n : ℕ}
    (A B C : Matrix (Fin n) (Fin n) ℝ) (u f : Fin n → ℝ)
    (hA : Function.Injective A.mulVec)
    (hB : MatrixKernelOne B f)
    (hC : Function.Injective C.mulVec)
    (hCu : C.mulVec u = f) :
    MatrixKernelOne (A * B * C) u := by
  intro v
  constructor
  · intro hv
    have hnest : A.mulVec (B.mulVec (C.mulVec v)) = 0 := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      exact hv
    have hBzero : B.mulVec (C.mulVec v) = 0 := by
      apply hA
      rw [Matrix.mulVec_zero]
      exact hnest
    obtain ⟨c, hc⟩ := (hB (C.mulVec v)).mp hBzero
    refine ⟨c, hC ?_⟩
    rw [Matrix.mulVec_smul, hCu]
    exact hc
  · rintro ⟨c, rfl⟩
    have hBzero : B.mulVec (c • f) = 0 :=
      (hB (c • f)).mpr ⟨c, rfl⟩
    calc
      (A * B * C).mulVec (c • u) =
          A.mulVec (B.mulVec (C.mulVec (c • u))) := by
            rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      _ = A.mulVec (B.mulVec (c • f)) := by rw [Matrix.mulVec_smul, hCu]
      _ = 0 := by rw [hBzero, Matrix.mulVec_zero]

theorem reactantTranspose_mulVec_injective {n : ℕ} (source : SquareSource n) :
    Function.Injective source.reactant.transpose.mulVec := by
  apply Matrix.mulVec_injective_iff_isUnit.mpr
  apply (source.reactant.transpose.isUnit_iff_isUnit_det).mpr
  exact source.reactant.isUnit_det_transpose source.reactant_det_isUnit

theorem factoredCurrentJacobian_matrixKernelOne {n : ℕ}
    (source : SquareSource n) (J : ℝ) (g q u f : Fin n → ℝ)
    (hJ : 0 < J) (hg : ∀ i, 0 < g i) (hq : ∀ i, 1 < q i)
    (hresponseKernel : ResponseKernelOne (responseMatrix source) q f)
    (hreactant : source.reactant.transpose.mulVec u = f) :
    MatrixKernelOne (factoredCurrentJacobian source J g q) u := by
  apply matrixKernelOne_triple
  · exact diagonal_mulVec_injective_of_positive _
      (reconstructedFlows_positive J g q hJ hg hq).1
  · exact hresponseKernel
  · exact reactantTranspose_mulVec_injective source
  · exact hreactant

theorem matrixKernelOne_controlReducedInjective {n : ℕ}
    (E : Matrix (Fin n) (Fin n) ℝ) (u : Fin n → ℝ) (controlled : Fin n)
    (hkernel : MatrixKernelOne E u) (hu : u controlled ≠ 0) :
    ControlReducedInjective E controlled := by
  intro v hv hcontrol
  obtain ⟨c, rfl⟩ := (hkernel v).mp hv
  simp only [Pi.smul_apply, smul_eq_mul] at hcontrol ⊢
  have hc : c = 0 := by
    exact (mul_eq_zero.mp hcontrol).resolve_right hu
  simp [hc]

theorem matrixKernelOne_noncontrolledSteadyJacobianInjective {n : ℕ}
    (source : SquareSource n) (E : Matrix (Fin n) (Fin n) ℝ)
    (u g lambda : Fin n → ℝ)
    (hkernel : MatrixKernelOne E u)
    (hmode : ControlledProductionMode source g)
    (hleft : E.transpose.mulVec lambda = 0)
    (htransverse : dotProduct lambda g ≠ 0)
    (hcontrol : u source.controlled ≠ 0) :
    NoncontrolledSteadyJacobianInjective source E := by
  intro w hwcontrol hsteady
  let c := source.netStoich.mulVec (E.mulVec w) source.controlled
  have hsource : source.netStoich.mulVec (E.mulVec w) =
      c • (source.netStoich.mulVec g) := by
    funext i
    by_cases hi : i = source.controlled
    · subst i
      simp [c, hmode source.controlled]
    · rw [hsteady i hi]
      simp [Pi.smul_apply, hmode i, hi]
  have hcurrent : E.mulVec w = c • g := by
    apply netStoich_mulVec_injective source
    rw [Matrix.mulVec_smul]
    exact hsource
  have hdotzero : dotProduct lambda (E.mulVec w) = 0 := by
    calc
      dotProduct lambda (E.mulVec w) =
          dotProduct w (E.transpose.mulVec lambda) := by
            exact (Matrix.dotProduct_transpose_mulVec E w lambda).symm
      _ = 0 := by rw [hleft]; simp
  have hcprod : c * dotProduct lambda g = 0 := by
    rw [hcurrent, dotProduct_smul] at hdotzero
    exact hdotzero
  have hc : c = 0 := (mul_eq_zero.mp hcprod).resolve_right htransverse
  have hcurrentZero : E.mulVec w = 0 := by rw [hcurrent, hc]; simp
  exact matrixKernelOne_controlReducedInjective E u source.controlled
    hkernel hcontrol w hcurrentZero hwcontrol

/-- The full Jacobian has only the scaling kernel, so fixing an accessible
control coordinate makes the reduced Jacobian injective. -/
theorem reconstructedCurrent_controlReducedInjective {n : ℕ}
    (source : SquareSource n) (J : ℝ) (g q u f : Fin n → ℝ)
    (hJ : 0 < J) (hg : ∀ i, 0 < g i) (hq : ∀ i, 1 < q i)
    (hresponseKernel : ResponseKernelOne (responseMatrix source) q f)
    (hreactant : source.reactant.transpose.mulVec u = f)
    (hcontrol : u source.controlled ≠ 0) :
    ControlReducedInjective (factoredCurrentJacobian source J g q)
      source.controlled := by
  apply matrixKernelOne_controlReducedInjective _ u source.controlled
  · exact factoredCurrentJacobian_matrixKernelOne source J g q u f
      hJ hg hq hresponseKernel hreactant
  · exact hcontrol

structure AlgebraicBranchCertificate {n : ℕ} (source : SquareSource n)
    (J : ℝ) (g q f h u lambda : Fin n → ℝ) : Prop where
  firstOrder : FirstOrderSourceRealization source J g q f h
  responseKernel : ResponseKernelOne (responseMatrix source) q f
  currentKernel : MatrixKernelOne (literalCurrentJacobian source J g q) u
  leftNull : (literalCurrentJacobian source J g q).transpose.mulVec lambda = 0
  transverse : dotProduct lambda g ≠ 0
  reducedSteady : NoncontrolledSteadyJacobianInjective source
    (literalCurrentJacobian source J g q)

/-- All finite algebraic hypotheses needed before the analytic implicit-function
step are packaged in one literal-source certificate. -/
theorem exists_algebraicBranchCertificate {n : ℕ} [Nonempty (Fin n)]
    (source : SquareSource n) (J : ℝ) (g q f h u lambda : Fin n → ℝ)
    (hJ : 0 < J) (hg : ∀ i, 0 < g i) (hq : ∀ i, 1 < q i)
    (hf : ∀ i, 0 < f i)
    (hresponse : (responseMatrix source).transpose.mulVec f = h)
    (hratio : ∀ i, h i = q i * f i)
    (hmode : ControlledProductionMode source g)
    (hP : ∀ i j, 0 ≤ routingMatrix (responseMatrix source) q f i j)
    (hirr : (routingMatrix (responseMatrix source) q f).IsIrreducible)
    (hreactant : source.reactant.transpose.mulVec u = f)
    (hleft : (literalCurrentJacobian source J g q).transpose.mulVec lambda = 0)
    (htransverse : dotProduct lambda g ≠ 0)
    (hcontrol : u source.controlled ≠ 0) :
    AlgebraicBranchCertificate source J g q f h u lambda := by
  have hqpos : ∀ i, 0 < q i := fun i => lt_trans zero_lt_one (hq i)
  have hresponseKernel : ResponseKernelOne (responseMatrix source) q f :=
    irreducible_routing_responseKernelOne (responseMatrix source) q f h
      hresponse hratio hf hqpos hP hirr
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

end
end OptimalAffinityRealizability
