import proofs.CoreCouplingCAC.LocalBoxes
import proofs.CoreCouplingCAC.LocalEnergy
import proofs.CoreCouplingCAC.EnergyBarrier

namespace CoreCouplingCAC

noncomputable def midpointState (x y : State) : State :=
  ⟨(x.A+y.A)/2,(x.B+y.B)/2,(x.z+y.z)/2,(x.H+y.H)/2⟩

theorem midpoint_transform (x y : State) :
    transform (midpointState x y) = fun i => (transform x i+transform y i)/2 := by
  funext i
  fin_cases i <;> simp [transform,midpointState] <;> ring

theorem midpoint_inBox (x y lo hi : State) (hx : InBox x lo hi) (hy : InBox y lo hi) :
    InBox (midpointState x y) lo hi := by
  rcases hx with ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩
  rcases hy with ⟨k1,k2,k3,k4,k5,k6,k7,k8⟩
  dsimp [InBox,midpointState]
  exact ⟨by linarith,by linarith,by linarith,by linarith,
    by linarith,by linarith,by linarith,by linarith⟩

theorem low_nonlinear_energy (x c : State) (hx : InBox x lowLower lowUpper)
    (hc : InBox c lowLower lowUpper) (hs : Stationary witnessRates c) :
    energyRate witnessRates lowLeft lowRight (transform c) (transform x) ≤
      -(1/100:ℝ)*energy lowLeft lowRight (transform c) (transform x) := by
  have hmid := low_jacobian_domination (midpointState x c)
    (midpoint_inBox x c lowLower lowUpper hx hc)
  rw [midpoint_transform] at hmid
  exact nonlinear_energy_bound witnessRates lowComparison lowLeft lowRight
    (transform c) (transform x) (1/100)
    low_comparison_certificate.2.1 low_comparison_certificate.1
    (stationary_transformed witnessRates c hs) hmid.1 hmid.2 low_energy_row_bound

theorem high_nonlinear_energy (x c : State) (hx : InBox x highLower highUpper)
    (hc : InBox c highLower highUpper) (hs : Stationary witnessRates c) :
    energyRate witnessRates highLeft highRight (transform c) (transform x) ≤
      -(1/100:ℝ)*energy highLeft highRight (transform c) (transform x) := by
  have hmid := high_jacobian_domination (midpointState x c)
    (midpoint_inBox x c highLower highUpper hx hc)
  rw [midpoint_transform] at hmid
  exact nonlinear_energy_bound witnessRates highComparison highLeft highRight
    (transform c) (transform x) (1/100)
    high_comparison_certificate.2.1 high_comparison_certificate.1
    (stationary_transformed witnessRates c hs) hmid.1 hmid.2 high_energy_row_bound

end CoreCouplingCAC
