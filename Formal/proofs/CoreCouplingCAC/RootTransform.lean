import proofs.CoreCouplingCAC.RootCount

namespace CoreCouplingCAC
noncomputable def clearedResidual (e z : ℝ) : ℝ :=
  (z+2)^2*(27+(6668/6667:ℝ)*z^2-(53328/6667:ℝ)*z)-60*(1+e)*(z+2)+
    e*(z*(60+((6668/6667:ℝ)*z-(53328/6667:ℝ))*(z+2)))^2

theorem cleared_residual_identity (e z : ℝ) (hz : z+2 ≠ 0) :
    clearedResidual e z = (z+2)^2*residual (varyRates e) z := by
  simp only [clearedResidual,residual,reducedA,reducedB,reducedK,varyRates,witnessRates]
  field_simp
  ring

theorem count_cleared_identity (e t : ℝ) (ht : 1+t ≠ 0) :
    (countPoly e).eval t = 44448889*(1+t)^6*clearedResidual e (8*t/(1+t)) := by
  norm_num [countPoly,Fin.sum_univ_succ,countCoeff,clearedResidual]
  field_simp
  ring

theorem count_transform (e t : ℝ) (ht : 0 ≤ t) :
    (countPoly e).eval t = 44448889*(1+t)^6*(8*t/(1+t)+2)^2*
      residual (varyRates e) (8*t/(1+t)) := by
  rw [count_cleared_identity e t (by positivity),cleared_residual_identity e _ (by positivity)]
  ring
end CoreCouplingCAC
