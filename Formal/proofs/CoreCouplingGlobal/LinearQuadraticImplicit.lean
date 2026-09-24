import proofs.CoreCouplingGlobal.QuadraticImplicit
import Mathlib.Analysis.SpecificLimits.Normed

namespace CoreCouplingGlobal
open Filter
open scoped Topology ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Absorb a contractive linear trajectory term before applying the already
proved analytic quadratic implicit construction. -/
theorem linear_quadratic_implicit_solution (L : E →L[ℝ] F) (A : F →L[ℝ] F)
    (B : F →L[ℝ] F →L[ℝ] F) (hA : ‖A‖ < 1) :
    ∃ S : F ≃L[ℝ] F, (∀ v, S v=v-A v) ∧ ∃ ψ : E → F,
      ψ 0=0 ∧ ContDiffAt ℝ ω ψ 0 ∧
      HasFDerivAt ψ (S.symm.toContinuousLinearMap.comp L) 0 ∧
      ∀ᶠ ξ in 𝓝 (0:E), ψ ξ=L ξ+A (ψ ξ)+B (ψ ξ) (ψ ξ) := by
  obtain ⟨u,hu⟩ := isUnit_one_sub_of_norm_lt_one hA
  let S : F ≃L[ℝ] F := ContinuousLinearEquiv.ofUnit u
  have hS : ∀ v, S v=v-A v := by
    intro v
    change (u : F →L[ℝ] F) v=v-A v
    rw [hu]
    rfl
  let SB : F →L[ℝ] F →L[ℝ] F :=
    (ContinuousLinearMap.compL ℝ F F F S.symm.toContinuousLinearMap).comp B
  obtain ⟨ψ,hzero,hcd,hd,heq,_hunique⟩ :=
    quadratic_implicit_solution (S.symm.toContinuousLinearMap.comp L) SB
  refine ⟨S,hS,ψ,hzero,hcd,hd,?_⟩
  filter_upwards [heq] with ξ hξ
  have hh := congrArg S hξ
  change S (ψ ξ)=S (S.symm (L ξ)+S.symm (B (ψ ξ) (ψ ξ))) at hh
  rw [map_add,S.apply_symm_apply,S.apply_symm_apply,hS] at hh
  calc
    ψ ξ = L ξ+B (ψ ξ) (ψ ξ)+A (ψ ξ) := sub_eq_iff_eq_add.mp hh
    _ = _ := by abel

end CoreCouplingGlobal
