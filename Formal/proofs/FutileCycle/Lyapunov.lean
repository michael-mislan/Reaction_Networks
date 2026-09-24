import proofs.DUnstableCores.DScaling

namespace FutileCycle
open Matrix
open scoped ComplexOrder

/-- A semidefinite Lyapunov form with a strictly negative identity residual
excludes every eigenvalue in the open right half-plane. -/
theorem lyapunov_no_rhp {I : Type*} [Fintype I] [DecidableEq I]
    (A Q : Matrix I I ℂ) (hQ : Q.PosSemidef) (r : ℝ) (hr : 0 < r)
    (hL : A.conjTranspose * Q + Q * A = -(r : ℂ) • (1 : Matrix I I ℂ))
    (z : ℂ) (v : I → ℂ) (hv : v ≠ 0) (he : A *ᵥ v = z • v) : ¬0 < z.re := by
  intro hz
  let E := star v ⬝ᵥ (Q *ᵥ v)
  have hE : 0 ≤ E.re := hQ.re_dotProduct_nonneg v
  have hleft : star v ⬝ᵥ ((A.conjTranspose * Q + Q * A) *ᵥ v) =
      (star z + z) * E := by
    rw [add_mulVec, dotProduct_add, ← mulVec_mulVec, ← mulVec_mulVec,
      dotProduct_mulVec, ← star_mulVec, he, star_smul, smul_dotProduct,
      mulVec_smul, dotProduct_smul]
    simp only [smul_eq_mul, E]
    ring
  have hid : (star z + z) * E = -(r : ℂ) * (star v ⬝ᵥ v) := by
    rw [← hleft, hL, smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul]
  have hnorm : 0 < (star v ⬝ᵥ v).re := by
    have hh := (dotProduct_star_self_pos_iff (v := v)).mpr hv
    exact (Complex.pos_iff.mp hh).1
  have hre := congrArg Complex.re hid
  simp [Complex.mul_re] at hre
  have hn : 0 ≤ 2*z.re*E.re := by positivity
  nlinarith

end FutileCycle
