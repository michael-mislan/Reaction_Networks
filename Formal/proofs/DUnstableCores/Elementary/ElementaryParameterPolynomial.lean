import proofs.DUnstableCores.Elementary.FinFourPolynomial
import proofs.DUnstableCores.Elementary.QuarticSpectral

namespace DUnstableCores
set_option maxHeartbeats 50000

def elementaryFamilyMatrix (T L : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  ![![-T, 0, 0, L*(2-T)], ![0, -4, -4, 8*L], ![2*T, -4, -4*T-4, L*(2*T+8)], ![-T, 0, 2*T, L*(-T-4)]]

def elementaryFamilyCoeff1 (T L : ℝ) : ℝ := (T+4)*L+5*T+8
def elementaryFamilyCoeff2 (T L : ℝ) : ℝ := (14*T+32)*L+4*T*(T+6)
def elementaryFamilyCoeff3 (T L : ℝ) : ℝ := 112*T*L+16*T^2
def elementaryFamilyCoeff4 (T L : ℝ) : ℝ := 64*T^2*L

theorem elementary_family_charpoly (T L : ℝ) :
    IsElementaryQuartic (elementaryFamilyMatrix T L)
      (elementaryFamilyCoeff1 T L) (elementaryFamilyCoeff2 T L)
      (elementaryFamilyCoeff3 T L) (elementaryFamilyCoeff4 T L) := by
  have hc1 : elementaryCoeff1 (elementaryFamilyMatrix T L) = elementaryFamilyCoeff1 T L := by
    change -((-T) + (-4) + (-4*T-4) + (L*(-T-4))) = (T+4)*L+5*T+8
    ring
  have hc2 : elementaryCoeff2 (elementaryFamilyMatrix T L) = elementaryFamilyCoeff2 T L := by
    change ((-T)*(-4) - (0)*(0)) + ((-T)*(-4*T-4) - (0)*(2*T)) + ((-T)*(L*(-T-4)) - (L*(2-T))*(-T)) + ((-4)*(-4*T-4) - (-4)*(-4)) + ((-4)*(L*(-T-4)) - (8*L)*(0)) + ((-4*T-4)*(L*(-T-4)) - (L*(2*T+8))*(2*T)) = (14*T+32)*L+4*T*(T+6)
    ring
  have hc3 : elementaryCoeff3 (elementaryFamilyMatrix T L) = elementaryFamilyCoeff3 T L := by
    change -(((-T)*(-4)*(-4*T-4) - (-T)*(-4)*(-4) - (0)*(0)*(-4*T-4) + (0)*(-4)*(2*T) + (0)*(0)*(-4) - (0)*(-4)*(2*T)) + ((-T)*(-4)*(L*(-T-4)) - (-T)*(8*L)*(0) - (0)*(0)*(L*(-T-4)) + (0)*(8*L)*(-T) + (L*(2-T))*(0)*(0) - (L*(2-T))*(-4)*(-T)) + ((-T)*(-4*T-4)*(L*(-T-4)) - (-T)*(L*(2*T+8))*(2*T) - (0)*(2*T)*(L*(-T-4)) + (0)*(L*(2*T+8))*(-T) + (L*(2-T))*(2*T)*(2*T) - (L*(2-T))*(-4*T-4)*(-T)) + ((-4)*(-4*T-4)*(L*(-T-4)) - (-4)*(L*(2*T+8))*(2*T) - (-4)*(-4)*(L*(-T-4)) + (-4)*(L*(2*T+8))*(0) + (8*L)*(-4)*(2*T) - (8*L)*(-4*T-4)*(0))) = 112*T*L+16*T^2
    ring
  have hc4 : elementaryCoeff4 (elementaryFamilyMatrix T L) = elementaryFamilyCoeff4 T L := by
    change (-T)*((-4)*(-4*T-4)*(L*(-T-4)) - (-4)*(L*(2*T+8))*(2*T) - (-4)*(-4)*(L*(-T-4)) + (-4)*(L*(2*T+8))*(0) + (8*L)*(-4)*(2*T) - (8*L)*(-4*T-4)*(0)) - (0)*((0)*(-4*T-4)*(L*(-T-4)) - (0)*(L*(2*T+8))*(2*T) - (-4)*(2*T)*(L*(-T-4)) + (-4)*(L*(2*T+8))*(-T) + (8*L)*(2*T)*(2*T) - (8*L)*(-4*T-4)*(-T)) + (0)*((0)*(-4)*(L*(-T-4)) - (0)*(L*(2*T+8))*(0) - (-4)*(2*T)*(L*(-T-4)) + (-4)*(L*(2*T+8))*(-T) + (8*L)*(2*T)*(0) - (8*L)*(-4)*(-T)) - (L*(2-T))*((0)*(-4)*(2*T) - (0)*(-4*T-4)*(0) - (-4)*(2*T)*(2*T) + (-4)*(-4*T-4)*(-T) + (-4)*(2*T)*(0) - (-4)*(-4)*(-T)) = 64*T^2*L
    ring
  unfold IsElementaryQuartic
  rw [elementary_charpoly_fin4,hc1,hc2,hc3,hc4]

def elementaryFamilyDelta (T L : ℝ) : ℝ := elementaryDelta
  (elementaryFamilyCoeff1 T L) (elementaryFamilyCoeff2 T L)
  (elementaryFamilyCoeff3 T L) (elementaryFamilyCoeff4 T L)

theorem elementary_fast_D_delta_negative (u : ℝ) (hu : 0 ≤ u) :
    elementaryFamilyDelta 100 (100+u) < 0 := by
  have hi : elementaryFamilyDelta 100 (100+u) = -(5254246400*u^3+1562660812800*u^2+154010347520000*u+5025252352000000) := by
    unfold elementaryFamilyDelta elementaryDelta elementaryFamilyCoeff1 elementaryFamilyCoeff2 elementaryFamilyCoeff3 elementaryFamilyCoeff4
    ring
  rw [hi]
  have hp : 0 < 5254246400*u^3+1562660812800*u^2+154010347520000*u+5025252352000000 := by positivity
  linarith

theorem elementary_same_source_control :
    elementaryFamilyCoeff1 2 1 = 24 ∧ elementaryFamilyCoeff2 2 1 = 124 ∧
    elementaryFamilyCoeff3 2 1 = 288 ∧ elementaryFamilyCoeff4 2 1 = 256 ∧
    elementaryFamilyDelta 2 1 = 626688 := by
  norm_num [elementaryFamilyCoeff1,elementaryFamilyCoeff2,elementaryFamilyCoeff3,elementaryFamilyCoeff4,elementaryFamilyDelta,elementaryDelta]

end DUnstableCores

