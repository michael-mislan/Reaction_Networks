import proofs.CoreCouplingGlobal.ResidualConvergence
import proofs.CoreCouplingCAC.GlobalExistence

namespace CoreCouplingGlobal
open CoreCouplingCAC

def positivePart (x : ResponseVector) : ResponseVector := fun i => max 0 (x i)

theorem positivePart_lipschitz : LipschitzWith 1 positivePart := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one,one_mul]
  apply (dist_pi_le_iff (dist_nonneg : 0 ≤ dist x y)).2
  intro i
  calc
    dist (positivePart x i) (positivePart y i) ≤ dist (x i) (y i) := by
      have hh := ((LipschitzWith.id : LipschitzWith 1 (id : ℝ → ℝ)).const_max 0).dist_le_mul (x i) (y i)
      simpa only [positivePart,id_eq,NNReal.coe_one,one_mul] using hh
    _ ≤ dist x y := dist_le_pi_dist x y i

theorem responseVectorField_contDiff (e : ℝ) : ContDiff ℝ 1 (responseVectorField e) := by
  apply contDiff_pi.2
  intro i
  fin_cases i <;> simp [responseVectorField,fA,fB,fZ,fH,flagshipRates] <;> fun_prop

/-- Globally solvable positive-part extension, with a nonnegative scalar cutoff. -/
theorem positive_extension_solution (e R : ℝ) (hR : 0 < R) (x₀ : ResponseVector) :
    ∃ b : ResponseVector → ℝ, ∃ X : ℝ → ResponseVector,
      (∀ x, 0 ≤ b x ∧ b x ≤ 1) ∧ (∀ x, ‖x‖ ≤ R → b x = 1) ∧
      X 0 = x₀ ∧ ∀ t, HasDerivAt X
        (b (positivePart (X t)) • responseVectorField e (positivePart (X t))) t := by
  let b : ContDiffBump (0 : ResponseVector) := ⟨R,2*R,hR,by linarith⟩
  let f : ResponseVector → ResponseVector := fun x => b x • responseVectorField e x
  have hs : HasCompactSupport f := b.hasCompactSupport.smul_right
  have hd : ContDiff ℝ 1 f := b.contDiff.smul (responseVectorField_contDiff e)
  obtain ⟨K,hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hs hd (by norm_num)
  obtain ⟨C,hC⟩ := hs.exists_bound_of_continuous hd.continuous
  have hlip : LipschitzWith K (fun x => f (positivePart x)) := by
    simpa only [mul_one] using hK.comp positivePart_lipschitz
  obtain ⟨X,hX0,hXd⟩ := bounded_lipschitz_global_solution (fun x => f (positivePart x)) K
    ⟨max C 0,le_max_right _ _⟩ hlip (fun x => (hC _).trans (le_max_left _ _)) x₀
  refine ⟨b,X,(fun _ => ⟨b.nonneg,b.le_one⟩),?_,hX0,hXd⟩
  intro x hx
  exact b.one_of_mem_closedBall (by simpa only [Metric.mem_closedBall,dist_zero_right] using hx)

end CoreCouplingGlobal
