import proofs.CoreCouplingCAC.Source

namespace CoreCouplingGlobal
open CoreCouplingCAC

theorem flagship_total_drift (p : Rates) (A B z : ℝ) :
    fA p A B z + fB p A B z = p.a+p.b-(A+B)+p.e*(B-A^2) := by
  unfold fA fB
  ring

/-- All constant linear combinations eliminating the three nonlinear monomials
are multiples of one signed vector. This obstructs a positive relaxing total. -/
theorem nonlinear_cancellation_kernel (wA wB wz wH : ℝ)
    (hBZ : wA-wB-wz=0) (hAA : -2*wA+wB=0) (hZZ : -2*wz+wH=0) :
    wB=2*wA ∧ wz= -wA ∧ wH= -2*wA := by
  constructor
  · linarith
  constructor <;> linarith

theorem no_nonzero_nonnegative_cancelling_total (wA wB wz wH : ℝ)
    (hA : 0 ≤ wA) (hz : 0 ≤ wz)
    (hBZ : wA-wB-wz=0) (hAA : -2*wA+wB=0) (hZZ : -2*wz+wH=0) :
    wA=0 ∧ wB=0 ∧ wz=0 ∧ wH=0 := by
  obtain ⟨hB,hz',hH⟩ := nonlinear_cancellation_kernel wA wB wz wH hBZ hAA hZZ
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

theorem signed_total_drift (p : Rates) (A B z H : ℝ) :
    fA p A B z + 2*fB p A B z - fZ p A B z H - 2*fH p z H =
      p.a+2*p.b-A-2*B-p.u*z+(1+2*p.d)*H := by
  unfold fA fB fZ fH
  ring

end CoreCouplingGlobal
