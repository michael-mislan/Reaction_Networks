import Mathlib

namespace FutileCycle
open Matrix

theorem sign_conjugate_det {I : Type*} [Fintype I] [DecidableEq I]
    (s : I → ℤ) (hs : ∀ i, s i*s i=1) (A B : Matrix I I ℤ)
    (hB : ∀ i j, B i j=s i*A i j*s j) : B.det=A.det := by
  have hm : B=diagonal s*A*diagonal s := by ext i j; simp [hB]
  have hss : diagonal s*diagonal s=(1:Matrix I I ℤ) := by
    rw [diagonal_mul_diagonal]
    simp only [hs, diagonal_one]
  have hd := congrArg Matrix.det hss
  rw [det_mul, det_one] at hd
  rw [hm, det_mul, det_mul]
  calc
    _ = ((diagonal s).det*(diagonal s).det)*A.det := by ring
    _ = A.det := by rw [hd, one_mul]

theorem sign_conjugate_eigenpair {I : Type*} [Fintype I]
    (s : I → ℂ) (hs : ∀ i, s i*s i=1) (A B : Matrix I I ℂ)
    (hB : ∀ i j, B i j=s i*A i j*s j) (z : ℂ) (w : I → ℂ)
    (hw : w ≠ 0) (he : B *ᵥ w=z • w) :
    (fun i => s i*w i) ≠ 0 ∧ A *ᵥ (fun i => s i*w i)=z • (fun i => s i*w i) := by
  have hn i : s i ≠ 0 := by intro h; simpa [h] using hs i
  constructor
  · intro hh
    apply hw
    funext i
    exact (mul_eq_zero.mp (congrFun hh i)).resolve_left (hn i)
  · funext i
    have hh := congrFun he i
    have hsum : (B *ᵥ w) i=s i*(A *ᵥ (fun j => s j*w j)) i := by
      simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [hB]
      ring
    rw [hsum] at hh
    have hh' := congrArg (fun t => s i*t) hh
    simp only [← mul_assoc, hs, one_mul, Pi.smul_apply, smul_eq_mul] at hh'
    calc
      _ = s i * z * w i := hh'
      _ = _ := by simp only [Pi.smul_apply, smul_eq_mul]; ring

end FutileCycle
