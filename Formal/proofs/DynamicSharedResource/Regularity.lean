import proofs.DynamicSharedResource.Algebra

namespace DynamicSharedResource
noncomputable section
open scoped BigOperators

theorem nominal_contDiffAt (u : State) (hu : 873/10-u 0 ≠ 0) :
    ContDiffAt ℝ 1 nominal u := by
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i <;>
    simp [nominal,field,HG,HT,phi1,phi2,psiG,psiT,
      thetaR,thetaW,thetaH,thetaV,g,e0,y,r,regen]
  all_goals fun_prop (disch := assumption)

theorem affine_contDiff (c : State) (M : Matrix (Fin 8) (Fin 8) ℝ) :
    ContDiff ℝ 1 (fun a : State => c+M.mulVec a) := by
  apply contDiff_pi.mpr
  intro i
  simp only [Pi.add_apply,Matrix.mulVec,dotProduct]
  fun_prop

theorem mulVec_hasDerivAt (M : Matrix (Fin 8) (Fin 8) ℝ)
    (a : ℝ → State) (v : State) (t : ℝ) (ha : HasDerivAt a v t) :
    HasDerivAt (fun t => M.mulVec (a t)) (M.mulVec v) t := by
  apply hasDerivAt_pi.mpr
  intro i
  simpa only [Matrix.mulVec,dotProduct] using
    (HasDerivAt.fun_sum (u := Finset.univ) fun j _ =>
      (hasDerivAt_pi.mp ha j).const_mul (M i j))

end
end DynamicSharedResource
