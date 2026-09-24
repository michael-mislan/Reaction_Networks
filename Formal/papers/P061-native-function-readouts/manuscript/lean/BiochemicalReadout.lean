import Mathlib

/-! Explicit-complex cofactor readout. ODE existence, comparison bounds and
physical calibration are proved/discussed conventionally in THEORY.md.
This module checks the source algebra, finite integral account and exact
robust decision arithmetic. It does not assert empirical validation. -/
namespace BiochemicalReadout
noncomputable section
open MeasureTheory Set

def freeField (p k C alpha beta R x b : ℝ) : ℝ :=
  p*(C-x-b)-k*x-alpha*x*(R-b)+beta*b
def boundField (alpha beta c R x b : ℝ) : ℝ :=
  alpha*x*(R-b)-(beta+c)*b

theorem source_deficit_identity (p k C alpha beta c R x x0 b : ℝ) :
    (p*(C-x0)-k*x0)-freeField p k C alpha beta R x b =
      -(p+k)*(x0-x)+boundField alpha beta c R x b+(p+c)*b := by
  unfold freeField boundField
  ring

theorem stored_deficit_identity (p k c e b db : ℝ) :
    (-(p+k)*e+db+(p+c)*b)-db = -(p+k)*(e-b)+(c-k)*b := by
  ring

theorem finite_account (p k c T : ℝ) (e b : ℝ → ℝ)
    (he : Continuous e) (hb : Continuous b)
    (hder : ∀ t ∈ uIcc 0 T,
      HasDerivAt (fun t => e t-b t) (-(p+k)*e t+(p+c)*b t) t)
    (hinit : e 0-b 0=0) :
    (p+k)*(∫ t in 0..T, k*e t) =
      k*((p+c)*(∫ t in 0..T, b t)+b T-e T) := by
  have ie : IntervalIntegrable e volume 0 T := he.intervalIntegrable 0 T
  have ib : IntervalIntegrable b volume 0 T := hb.intervalIntegrable 0 T
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt hder
    ((ie.const_mul (-(p+k))).add (ib.const_mul (p+c)))
  rw [intervalIntegral.integral_add (ie.const_mul (-(p+k)))
    (ib.const_mul (p+c)), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, hinit] at hi
  rw [intervalIntegral.integral_const_mul]
  have hm := congrArg (fun z : ℝ => k*z) hi
  nlinarith only [hm]

theorem turnover_cost (p k c a I q D : ℝ)
    (ha : a ≠ 0) (hc : c ≠ 0)
    (hq : q=c*I) (hd : a*D=k*(p+c)*I) :
    D=k/a*(1+p/c)*q := by
  rw [hq]
  field_simp
  nlinarith [hd]

theorem recovery_remainder (a p beta h k e b J : ℝ)
    (ha : a ≠ 0)
    (hj : a*J=e+(p-beta)*b/h) :
    k*J=k/a*(e+(p-beta)*b/h) := by
  rw [← hj]
  field_simp

theorem merged_source (p C alpha beta c R x b k ell k' ell' : ℝ)
    (h : k+ell=k'+ell') :
    freeField p (k+ell) C alpha beta R x b =
      freeField p (k'+ell') C alpha beta R x b ∧
    boundField alpha beta c R x b = boundField alpha beta c R x b := by
  rw [h]
  exact ⟨rfl,rfl⟩

theorem alias_fluxes : (1:ℝ)*(1/2)/(1+1/2+3/2)=1/6 ∧
    (1:ℝ)*(3/2)/(1+3/2+1/2)=1/2 := by norm_num

theorem equal_law_error (r alpha beta : ℝ)
    (hl : alpha=r) (hh : beta=1-r) : alpha+beta=1 := by linarith

def seedUpper : ℝ := 75099863/730945000
def seedLower : ℝ := 189189/1535000
theorem seed_window : seedUpper+1/100 < 113/1000 ∧
    (113:ℝ)/1000 < seedLower-1/100 ∧ (10:ℝ)/203 < 1/20 := by
  norm_num [seedUpper,seedLower]

def loadBound : ℝ := (81/1000)*(1+(205/100)/20)/(193/100)
def upper (T : ℝ) : ℝ :=
  (102/100)*(81/1000)*(101/100)*((105/100)*(101/100)/(203/100))*T
def lower (T : ℝ) : ℝ :=
  (98/100)*(79/1000)*(94/100)*((195/100)*(99/100)/(297/100))/(1005/1000)*(T-1/21)
def threshold : ℝ := (upper 8+lower 8)/2

theorem parameter_certificate :
    (101:ℝ)/99*loadBound < 1/20 ∧
    94/100 < 1-1/100-(101/100)*loadBound ∧
    (81/1000)*(101/100)/(20*(99/100)) < (5:ℝ)/1000 := by
  norm_num [loadBound]

theorem decision_certificate :
    upper 8+1/100 < threshold ∧ threshold < lower 8-1/100 ∧
    (5:ℝ)/1000 < lower 8-upper 8-2/100 := by
  norm_num [upper,lower,threshold]

theorem preparation_preservation (xb x0 e : ℝ) (hxb : 0<xb)
    (hx0 : (99/100)*xb ≤ x0) (he : e ≤ (101/100)*xb*loadBound) :
    e < (1/20)*x0 := by
  have hc : (101:ℝ)/100*loadBound < (1/20)*(99/100) := by
    norm_num [loadBound]
  have hm := mul_lt_mul_of_pos_right hc hxb
  nlinarith

theorem joint_protocol (y e x0 xb : ℝ) (isHigh : Prop)
    (hxb : 0<xb) (hx0 : (99/100)*xb ≤ x0)
    (he : e ≤ (101/100)*xb*loadBound)
    (hL : ¬isHigh → y ≤ upper 8+1/100)
    (hH : isHigh → lower 8-1/100 ≤ y) :
    e < (1/20)*x0 ∧ (isHigh ↔ threshold < y) := by
  refine ⟨preparation_preservation xb x0 e hxb hx0 he, ?_⟩
  constructor
  · intro hh
    exact lt_of_lt_of_le decision_certificate.2.1 (hH hh)
  · intro hy
    by_contra hh
    exact (not_lt_of_ge (hL hh)) (lt_trans decision_certificate.1 hy)

end
end BiochemicalReadout
