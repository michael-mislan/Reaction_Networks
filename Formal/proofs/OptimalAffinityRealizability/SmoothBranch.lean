import proofs.OptimalAffinityRealizability.Curvature
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

namespace OptimalAffinityRealizability

open Filter
open scoped ContDiff Topology
noncomputable section

theorem reconstructedLogReactionCurrent_contDiff {n : ℕ}
    (source : SquareSource n) (J : ℝ) (g q : Fin n → ℝ) :
    ContDiff ℝ ⊤ (reconstructedLogReactionCurrent source J g q) := by
  rw [contDiff_pi]
  intro i
  let LR : (Fin n → ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj i).comp
      (matrixContinuousLinearMap source.reactant.transpose)
  let LP : (Fin n → ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj i).comp
      (matrixContinuousLinearMap source.product.transpose)
  have hR : ContDiff ℝ ⊤
      (fun z : Fin n → ℝ => source.reactant.transpose.mulVec z i) := by
    simpa [LR] using LR.contDiff
  have hP : ContDiff ℝ ⊤
      (fun z : Fin n → ℝ => source.product.transpose.mulVec z i) := by
    simpa [LP] using LP.contDiff
  simpa [reconstructedLogReactionCurrent, reconstructedLogForwardFlow,
    reconstructedLogReverseFlow] using
      (ContDiff.const_smul (reconstructedForwardFlow J g q i)
        (Real.contDiff_exp.comp hR)).sub
      (ContDiff.const_smul (reconstructedReverseFlow J g q i)
        (Real.contDiff_exp.comp hP))

theorem reconstructedLogSourceDrift_contDiff {n : ℕ}
    (source : SquareSource n) (J : ℝ) (g q : Fin n → ℝ) :
    ContDiff ℝ ⊤ (reconstructedLogSourceDrift source J g q) := by
  have hcomp := (matrixContinuousLinearMap source.netStoich).contDiff.comp
    (reconstructedLogReactionCurrent_contDiff source J g q)
  simpa [reconstructedLogSourceDrift] using hcomp

theorem augmentedLogStationarity_contDiff {n : ℕ}
    (source : SquareSource n) (J : ℝ) (g q : Fin n → ℝ) :
    ContDiff ℝ ⊤ (augmentedLogStationarity source J g q) := by
  rw [contDiff_pi]
  intro i
  by_cases hi : i = source.controlled
  · subst i
    let coord : (Fin n → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj source.controlled
    simpa [augmentedLogStationarity, coord] using coord.contDiff
  · have hcomponent := (contDiff_pi.mp
      (reconstructedLogSourceDrift_contDiff source J g q)) i
    simpa [augmentedLogStationarity, hi] using hcomponent

def smoothLocalBranch {n : ℕ} (source : SquareSource n)
    (J : ℝ) (g q : Fin n → ℝ)
    (hreduced : NoncontrolledSteadyJacobianInjective source
      (literalCurrentJacobian source J g q)) : ℝ → (Fin n → ℝ) := by
  let F := augmentedLogStationarity source J g q
  let D := augmentedSteadyContinuousLinearEquiv source
    (literalCurrentJacobian source J g q) hreduced
  let hcont : ContDiffAt ℝ ⊤ F 0 := by
    simpa [F] using (augmentedLogStationarity_contDiff source J g q).contDiffAt
  let hderiv : HasFDerivAt F (D : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) 0 := by
    simpa [F, D] using
      (augmentedLogStationarity_hasStrictFDerivAt_zero source J g q).hasFDerivAt
  let hstrict := hcont.hasStrictFDerivAt' hderiv (by simp)
  exact inverseFunctionBranch F 0 D hstrict (controlledTargetDirection source)

theorem smoothLocalBranch_contDiffAt {n : ℕ} (source : SquareSource n)
    (J : ℝ) (g q : Fin n → ℝ)
    (hreduced : NoncontrolledSteadyJacobianInjective source
      (literalCurrentJacobian source J g q)) :
    ContDiffAt ℝ ⊤ (smoothLocalBranch source J g q hreduced) 0 := by
  let F := augmentedLogStationarity source J g q
  let D := augmentedSteadyContinuousLinearEquiv source
    (literalCurrentJacobian source J g q) hreduced
  let hcont : ContDiffAt ℝ ⊤ F 0 := by
    simpa [F] using (augmentedLogStationarity_contDiff source J g q).contDiffAt
  let hderiv : HasFDerivAt F (D : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) 0 := by
    simpa [F, D] using
      (augmentedLogStationarity_hasStrictFDerivAt_zero source J g q).hasFDerivAt
  have hinv := hcont.to_localInverse hderiv (by simp)
  let line : ℝ → (Fin n → ℝ) :=
    fun s => F 0 + s • controlledTargetDirection source
  have hline : ContDiffAt ℝ ⊤ line 0 := by
    dsimp [line]
    exact contDiffAt_const.add
      (contDiffAt_id.smul_const (controlledTargetDirection source))
  have hinvLine : ContDiffAt ℝ ⊤ (hcont.localInverse hderiv (by simp)) (line 0) := by
    simpa [line] using hinv
  have hcomp := ContDiffAt.comp (f := line)
    (g := hcont.localInverse hderiv (by simp)) 0 hinvLine hline
  simpa [smoothLocalBranch, F, D, hcont, hderiv, line, inverseFunctionBranch,
    ContDiffAt.localInverse, Function.comp_def] using hcomp

theorem contDiffAt_exists_secondVelocity
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (z : ℝ → E) (hz : ContDiffAt ℝ ⊤ z 0) :
    ∃ v : E, HasFDerivAt (fun s : ℝ => fderiv ℝ z s 1)
      (scalarDirectionMap v) 0 := by
  have hfderiv : ContDiffAt ℝ 1 (fderiv ℝ z) 0 :=
    hz.fderiv_right (m := 1) (by simp)
  have hvelocity : ContDiffAt ℝ 1 (fun s : ℝ => fderiv ℝ z s 1) 0 :=
    hfderiv.clm_apply contDiffAt_const
  let L := fderiv ℝ (fun s : ℝ => fderiv ℝ z s 1) 0
  let v := L 1
  have hL : L = scalarDirectionMap v := by
    apply ContinuousLinearMap.ext
    intro s
    change L s = s • v
    rw [show s = s • (1 : ℝ) by simp, L.map_smul]
    simp [v]
  refine ⟨v, ?_⟩
  have hhas := (hvelocity.differentiableAt one_ne_zero).hasFDerivAt
  change HasFDerivAt (fun s : ℝ => fderiv ℝ z s 1) L 0 at hhas
  rwa [hL] at hhas

def reactionCurrentAlongVelocity {n : ℕ} (source : SquareSource n)
    (J : ℝ) (g q : Fin n → ℝ) (z dz : ℝ → (Fin n → ℝ))
    (i : Fin n) (s : ℝ) : ℝ :=
  reconstructedForwardFlow J g q i *
      Real.exp (source.reactant.transpose.mulVec (z s) i) *
      source.reactant.transpose.mulVec (dz s) i -
    reconstructedReverseFlow J g q i *
      Real.exp (source.product.transpose.mulVec (z s) i) *
      source.product.transpose.mulVec (dz s) i

theorem reconstructedLogReactionCurrent_hasDerivAt_of_velocity
    {n : ℕ} (source : SquareSource n) (J : ℝ) (g q : Fin n → ℝ)
    (z dz : ℝ → (Fin n → ℝ)) (i : Fin n) (s : ℝ)
    (hz : HasFDerivAt z (scalarDirectionMap (dz s)) s) :
    HasDerivAt
      (fun t => reconstructedLogReactionCurrent source J g q (z t) i)
      (reactionCurrentAlongVelocity source J g q z dz i s) s := by
  let LR : (Fin n → ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj i).comp
      (matrixContinuousLinearMap source.reactant.transpose)
  let LP : (Fin n → ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj i).comp
      (matrixContinuousLinearMap source.product.transpose)
  have hRz : HasDerivAt
      (fun t => source.reactant.transpose.mulVec (z t) i)
      (source.reactant.transpose.mulVec (dz s) i) s := by
    convert (LR.hasFDerivAt.comp s hz).hasDerivAt using 1
    all_goals simp [LR, scalarDirectionMap]
  have hPz : HasDerivAt
      (fun t => source.product.transpose.mulVec (z t) i)
      (source.product.transpose.mulVec (dz s) i) s := by
    convert (LP.hasFDerivAt.comp s hz).hasDerivAt using 1
    all_goals simp [LP, scalarDirectionMap]
  have hRe := (Real.hasDerivAt_exp
    (source.reactant.transpose.mulVec (z s) i)).comp s hRz
  have hPe := (Real.hasDerivAt_exp
    (source.product.transpose.mulVec (z s) i)).comp s hPz
  have hforward := hRe.const_mul (reconstructedForwardFlow J g q i)
  have hreverse := hPe.const_mul (reconstructedReverseFlow J g q i)
  convert hforward.sub hreverse using 1
  all_goals simp [reactionCurrentAlongVelocity]
  all_goals ring

theorem differentiableAt_hasFDerivAt_scalarDirection_fderiv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (z : ℝ → E) (s : ℝ) (hz : DifferentiableAt ℝ z s) :
    HasFDerivAt z (scalarDirectionMap (fderiv ℝ z s 1)) s := by
  have hmap : fderiv ℝ z s = scalarDirectionMap (fderiv ℝ z s 1) := by
    apply ContinuousLinearMap.ext
    intro t
    rw [show t = t • (1 : ℝ) by simp, ContinuousLinearMap.map_smul]
    simp [scalarDirectionMap]
  rw [← hmap]
  exact hz.hasFDerivAt

theorem reactionCurrentAlongVelocity_eventually_eq_deriv
    {n : ℕ} (source : SquareSource n) (J : ℝ) (g q : Fin n → ℝ)
    (z : ℝ → (Fin n → ℝ)) (i : Fin n) (hz : ContDiffAt ℝ ⊤ z 0) :
    (fun s => reactionCurrentAlongVelocity source J g q z
      (fun t => fderiv ℝ z t 1) i s) =ᶠ[𝓝 0]
      deriv (fun s => reconstructedLogReactionCurrent source J g q (z s) i) := by
  have heventually := hz.eventually (by simp)
  filter_upwards [heventually] with s hs
  have hdiff := hs.differentiableAt (by simp)
  exact (reconstructedLogReactionCurrent_hasDerivAt_of_velocity
    source J g q z (fun t => fderiv ℝ z t 1) i s
    (differentiableAt_hasFDerivAt_scalarDirection_fderiv z s hdiff)).deriv.symm

theorem reconstructedLogReactionCurrent_secondDerivative_of_velocity
    {n : ℕ} (source : SquareSource n) (J : ℝ) (g q u v : Fin n → ℝ)
    (z dz : ℝ → (Fin n → ℝ)) (i : Fin n)
    (hz0 : z 0 = 0) (hdz0 : dz 0 = u)
    (hz : HasFDerivAt z (scalarDirectionMap u) 0)
    (hdz : HasFDerivAt dz (scalarDirectionMap v) 0) :
    HasDerivAt
        (fun s => reconstructedLogReactionCurrent source J g q (z s) i)
        (reactionCurrentAlongVelocity source J g q z dz i 0) 0 ∧
      HasDerivAt (reactionCurrentAlongVelocity source J g q z dz i)
        (reactionCurrentSecondJet source J g q u v i) 0 := by
  let LR : (Fin n → ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj i).comp
      (matrixContinuousLinearMap source.reactant.transpose)
  let LP : (Fin n → ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj i).comp
      (matrixContinuousLinearMap source.product.transpose)
  have hRz : HasDerivAt
      (fun s => source.reactant.transpose.mulVec (z s) i)
      (source.reactant.transpose.mulVec u i) 0 := by
    convert (LR.hasFDerivAt.comp 0 hz).hasDerivAt using 1
    all_goals simp [LR, scalarDirectionMap]
  have hPz : HasDerivAt
      (fun s => source.product.transpose.mulVec (z s) i)
      (source.product.transpose.mulVec u i) 0 := by
    convert (LP.hasFDerivAt.comp 0 hz).hasDerivAt using 1
    all_goals simp [LP, scalarDirectionMap]
  have hRdz : HasDerivAt
      (fun s => source.reactant.transpose.mulVec (dz s) i)
      (source.reactant.transpose.mulVec v i) 0 := by
    convert (LR.hasFDerivAt.comp 0 hdz).hasDerivAt using 1
    all_goals simp [LR, scalarDirectionMap]
  have hPdz : HasDerivAt
      (fun s => source.product.transpose.mulVec (dz s) i)
      (source.product.transpose.mulVec v i) 0 := by
    convert (LP.hasFDerivAt.comp 0 hdz).hasDerivAt using 1
    all_goals simp [LP, scalarDirectionMap]
  have hRe := (Real.hasDerivAt_exp
    (source.reactant.transpose.mulVec (z 0) i)).comp 0 hRz
  have hPe := (Real.hasDerivAt_exp
    (source.product.transpose.mulVec (z 0) i)).comp 0 hPz
  constructor
  · have hforward := hRe.const_mul (reconstructedForwardFlow J g q i)
    have hreverse := hPe.const_mul (reconstructedReverseFlow J g q i)
    convert hforward.sub hreverse using 1
    all_goals simp [reactionCurrentAlongVelocity, hz0, hdz0]
  · have hforward := (hRe.mul hRdz).const_mul
      (reconstructedForwardFlow J g q i)
    have hreverse := (hPe.mul hPdz).const_mul
      (reconstructedReverseFlow J g q i)
    unfold reactionCurrentAlongVelocity
    have hraw := hforward.sub hreverse
    have heq : (fun s => reconstructedForwardFlow J g q i *
          Real.exp (source.reactant.transpose.mulVec (z s) i) *
          source.reactant.transpose.mulVec (dz s) i -
        reconstructedReverseFlow J g q i *
          Real.exp (source.product.transpose.mulVec (z s) i) *
          source.product.transpose.mulVec (dz s) i) =ᶠ[𝓝 0]
        ((fun y => reconstructedForwardFlow J g q i *
          (((Real.exp ∘ fun s => source.reactant.transpose.mulVec (z s) i) *
            fun s => source.reactant.transpose.mulVec (dz s) i) y)) -
        (fun y => reconstructedReverseFlow J g q i *
          (((Real.exp ∘ fun s => source.product.transpose.mulVec (z s) i) *
            fun s => source.product.transpose.mulVec (dz s) i) y))) := by
      filter_upwards [] with s
      simp only [Pi.sub_apply, Pi.mul_apply, Function.comp_apply]
      ring
    have htarget := hraw.congr_of_eventuallyEq heq
    apply htarget.congr_deriv
    unfold reactionCurrentSecondJet literalCurrentJacobian
    rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    simp only [Pi.sub_apply, Matrix.mulVec_diagonal]
    simp [hz0, hdz0]
    ring

end
end OptimalAffinityRealizability
