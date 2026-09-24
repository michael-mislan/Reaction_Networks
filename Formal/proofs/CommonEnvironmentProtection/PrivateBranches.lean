import proofs.CommonEnvironmentProtection.QuadraticPool
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

namespace CommonEnvironmentProtection.PrivateBranches
noncomputable section

def gRho (a b c : ℝ) : ℝ := a*(1/b+1/c)
def gFlux (a b c E g : ℝ) : ℝ := E*a*g/(g+gRho a b c)
def gPoly (a b c E G g₀ k x g : ℝ) : ℝ :=
  g^2+(gRho a b c-(G-2*g₀)+(2*E*a/k)/x)*g-
    ((G-2*g₀)*gRho a b c-E*a/c)

theorem g_rho_pos (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    0 < gRho a b c := mul_pos ha (add_pos (one_div_pos.mpr hb) (one_div_pos.mpr hc))

theorem g_enzyme_pool (a b c E g : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hg : 0 < g) :
    gFlux a b c E g/a + gFlux a b c E g/(b*g) + gFlux a b c E g/(c*g)=E := by
  have hr := g_rho_pos a b c ha hb hc
  have hden : g+gRho a b c ≠ 0 := ne_of_gt (add_pos hg hr)
  unfold gFlux
  field_simp
  unfold gRho
  field_simp
  ring

theorem g_pool_residual (a b c E G g₀ k x g : ℝ)
    (hc : c ≠ 0) (hk : k ≠ 0) (hx : x ≠ 0) (hg : g ≠ 0)
    (hden : g+gRho a b c ≠ 0) :
    g+2*(g₀+gFlux a b c E g/(k*x))+gFlux a b c E g/(c*g)-G =
      gPoly a b c E G g₀ k x g/(g+gRho a b c) := by
  unfold gFlux gPoly
  field_simp
  ring

theorem g_reconstruct_pool (a b c E G g₀ k x g : ℝ)
    (hc : c ≠ 0) (hk : k ≠ 0) (hx : x ≠ 0) (hg : g ≠ 0)
    (hden : g+gRho a b c ≠ 0) (hpoly : gPoly a b c E G g₀ k x g = 0) :
    g+2*(g₀+gFlux a b c E g/(k*x))+gFlux a b c E g/(c*g)=G := by
  have h := g_pool_residual a b c E G g₀ k x g hc hk hx hg hden
  rw [hpoly,zero_div] at h
  linarith

def tRho (a b c d : ℝ) : ℝ := 1/a+1/d+b/(c*d)
def tFlux (a b c d e E y : ℝ) : ℝ := E*e*y/(1+y*e*tRho a b c d)
def tPoly (a b c d e E T z₀ k x y : ℝ) : ℝ :=
  (tRho a b c d*e)*y^2+
    (1-(T-z₀)*tRho a b c d*e+(E*e/k)/x)*y-(T-z₀)

theorem t_enzyme_pool (a b c d e E y : ℝ)
    (he : e ≠ 0) (hy : y ≠ 0)
    (hden : 1+y*e*tRho a b c d ≠ 0) :
    tFlux a b c d e E y/a+tFlux a b c d e E y/d+
      b*tFlux a b c d e E y/(c*d)+tFlux a b c d e E y/(e*y)=E := by
  have hf : tFlux a b c d e E y/a+tFlux a b c d e E y/d+
      b*tFlux a b c d e E y/(c*d)+tFlux a b c d e E y/(e*y) =
      tFlux a b c d e E y*(tRho a b c d+1/(e*y)) := by
    unfold tRho
    ring
  rw [hf]
  unfold tFlux
  have hn : 1+e*y*tRho a b c d ≠ 0 := by simpa only [mul_comm y e] using hden
  field_simp [he,hy,hden,hn]
  ring

theorem t_pool_residual (a b c d e E T z₀ k x y : ℝ)
    (hk : k ≠ 0) (hx : x ≠ 0) (hden : 1+y*e*tRho a b c d ≠ 0) :
    y+z₀+tFlux a b c d e E y/(k*x)-T =
      tPoly a b c d e E T z₀ k x y/(1+y*e*tRho a b c d) := by
  unfold tFlux tPoly
  field_simp [hk,hx,hden]
  ring

/-- All catalytic currents and the hyperoxidation/repair side loop balance.
The repair returns SO2H to SOH, as in the source Figure 1. -/
theorem t_stationarity (a b c d e j y : ℝ)
    (ha : a ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (he : e ≠ 0) (hy : y ≠ 0) :
    j-a*(j/a)=0 ∧
    a*(j/a)+c*(b*j/(c*d))-(b+d)*(j/d)=0 ∧
    b*(j/d)-c*(b*j/(c*d))=0 ∧
    d*(j/d)-e*y*(j/(e*y))=0 := by
  field_simp [ha,hc,hd,he,hy]
  ring_nf
  trivial

end
end CommonEnvironmentProtection.PrivateBranches
