import proofs.DUnstableCores.DScaling

namespace FutileCycle
open Matrix

theorem eigen_mulVec_pow {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (z : ℂ) (v : I → ℂ) (he : A *ᵥ v = z • v) (n : ℕ) :
    A^n *ᵥ v = z^n • v := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ← mulVec_mulVec, he, mulVec_smul, ih, smul_smul]
    rw [pow_succ]
    congr 1
    ring

theorem annihilator_no_rhp {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A^2 * (A+1)^4 * (A+2)^2 = 0)
    (z : ℂ) (v : I → ℂ) (hv : v ≠ 0) (he : A *ᵥ v = z • v) : ¬0 < z.re := by
  intro hz
  have h1 : (A+1) *ᵥ v = (z+1) • v := by
    simp [add_mulVec, he, add_smul]
  have h2 : (A+2) *ᵥ v = (z+2) • v := by
    simp [add_mulVec, he, add_smul, ofNat_mulVec]
  have hp := congrArg (fun M : Matrix I I ℂ => M *ᵥ v) hA
  dsimp only at hp
  simp only [← mulVec_mulVec] at hp
  rw [eigen_mulVec_pow _ _ _ h2] at hp
  simp only [mulVec_smul] at hp
  rw [eigen_mulVec_pow _ _ _ h1] at hp
  simp only [mulVec_smul] at hp
  rw [eigen_mulVec_pow _ _ _ he] at hp
  simp only [smul_smul, zero_mulVec] at hp
  have hs : (z+2)^2 * ((z+1)^4 * z^2) = 0 := (smul_eq_zero.mp hp).resolve_right hv
  have hn : z ≠ 0 ∧ z+1 ≠ 0 ∧ z+2 ≠ 0 := by
    constructor
    · intro h; simp [h] at hz
    constructor <;> intro h <;> have hh := congrArg Complex.re h <;> norm_num at hh <;> linarith
  exact (mul_ne_zero (pow_ne_zero _ hn.2.2)
    (mul_ne_zero (pow_ne_zero _ hn.2.1) (pow_ne_zero _ hn.1))) hs

end FutileCycle
