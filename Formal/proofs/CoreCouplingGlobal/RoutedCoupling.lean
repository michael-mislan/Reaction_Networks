import proofs.CoreCouplingGlobal.Absorbing
import proofs.CoreCouplingCAC.Isolation
import proofs.CoreCouplingCAC.CreationRegime

namespace CoreCouplingGlobal
open CoreCouplingCAC

/-- The fixed total fork rate is routed between buffered z=1 and dynamic z.
The two branches have reversible rate pairs (1-g,1-g) and (g,g). -/
noncomputable def routedZ (_e g : ℝ) (x : State) : ℝ :=
  g*(x.A-x.B*x.z)-16*x.z-4*x.z^2+3*x.H

def RoutedStationary (e g : ℝ) (x : State) : Prop :=
  fA (flagshipRates e) x.A x.B (1-g+g*x.z)=0 ∧
  fB (flagshipRates e) x.A x.B (1-g+g*x.z)=0 ∧
  routedZ e g x=0 ∧ fH (flagshipRates e) x.z x.H=0

theorem routed_one_iff (e : ℝ) (x : State) :
    RoutedStationary e 1 x ↔ Stationary (varyRates e) x := by
  norm_num [RoutedStationary,Stationary,routedZ,flagshipRates,varyRates,witnessRates,fZ]

theorem routed_zero_z (e : ℝ) (x : State) (hx : 0 < x.z)
    (hs : RoutedStationary e 0 x) : x.z = 13332/1667 := by
  have hz := hs.2.2.1
  have hh := hs.2.2.2
  dsimp [routedZ,fH,flagshipRates] at hz hh
  have hf : x.z*(1667*x.z-13332)=0 := by
    linear_combination -(20001/12:ℝ)*hz - 2500*hh
  have heq := (mul_eq_zero.mp hf).resolve_left (ne_of_gt hx)
  linarith only [heq]

theorem routed_zero_unique (e : ℝ) (he : 0 ≤ e) (x y : State)
    (hx : x.Positive) (hy : y.Positive)
    (hsx : RoutedStationary e 0 x) (hsy : RoutedStationary e 0 y) : x=y := by
  have hAx : fA (flagshipRates e) x.A x.B 1=0 := by simpa using hsx.1
  have hBx : fB (flagshipRates e) x.A x.B 1=0 := by simpa using hsx.2.1
  have hAy : fA (flagshipRates e) y.A y.B 1=0 := by simpa using hsy.1
  have hBy : fB (flagshipRates e) y.A y.B 1=0 := by simpa using hsy.2.1
  obtain ⟨hA,hB⟩ := isolated_AB_unistationary (flagshipRates e) he 1
    x.A x.B y.A y.B (by norm_num) hx.1 hy.1 hAx hBx hAy hBy
  have hz : x.z=y.z := (routed_zero_z e x hx.2.2.1 hsx).trans
    (routed_zero_z e y hy.2.2.1 hsy).symm
  have hH : x.H=y.H := by
    have hhx := hsx.2.2.2
    have hhy := hsy.2.2.2
    dsimp [fH,flagshipRates] at hhx hhy
    rw [hz] at hhx
    linarith only [hhx,hhy]
  cases x
  cases y
  simp_all

theorem routed_zero_exists (e : ℝ) (he : 0 ≤ e) :
    ∃ x : State, x.Positive ∧ RoutedStationary e 0 x := by
  let R := 14+20*e
  have hR : 0 < R := by dsimp [R]; positivity
  have hc : ContinuousOn (fun A : ℝ => e*A^2+A-(13+20*e)) (Set.Icc 0 R) := by fun_prop
  have h0 : e*0^2+0-(13+20*e) < 0 := by nlinarith only [he]
  have h1 : 0 < e*R^2+R-(13+20*e) := by
    have hs := mul_nonneg he (sq_nonneg R)
    dsimp [R] at *
    nlinarith only [hs]
  obtain ⟨A,hA,hroot⟩ := intermediate_value_Icc hR.le hc ⟨h0.le,h1.le⟩
  have hAp : 0 < A := by
    by_contra hh
    have ha0 : A=0 := by linarith [hA.1]
    rw [ha0] at hroot
    linarith only [h0,hroot]
  let z : ℝ := 13332/1667
  let H : ℝ := (16*z+2*z^2)/(2+1/10000)
  refine ⟨⟨A,20,z,H⟩,?_,?_⟩
  · exact ⟨hAp,by norm_num,by norm_num [z],by norm_num [H,z]⟩
  · dsimp [RoutedStationary,fA,fB,fH,routedZ,flagshipRates,z,H]
    norm_num
    constructor <;> nlinarith only [hroot]

/-- Exact causal root-count contrast for the routed family. Hyperbolicity,
open gamma-neighborhoods and the literal reservoir adapter are separate targets. -/
theorem routed_stationary_creation (e : ℝ) (hl : (1/200000:ℝ) ≤ e)
    (hr : e ≤ 1/50000) :
    (∃! x : State, x.Positive ∧ RoutedStationary e 0 x) ∧
    ∃ x y w : State, x.Positive ∧ y.Positive ∧ w.Positive ∧
      RoutedStationary e 1 x ∧ RoutedStationary e 1 y ∧ RoutedStationary e 1 w ∧
      x.z<y.z ∧ y.z<w.z := by
  have he : 0 ≤ e := by linarith
  constructor
  · obtain ⟨x,hx,hsx⟩ := routed_zero_exists e he
    exact ⟨x,⟨hx,hsx⟩,fun y hy => routed_zero_unique e he y x hy.1 hx hy.2 hsx⟩
  · obtain ⟨x,y,w,hx,hy,hw,hsx,hsy,hsw,hxy,hyw⟩ := creation_interval e hl hr
    exact ⟨x,y,w,hx,hy,hw,(routed_one_iff e x).2 hsx,
      (routed_one_iff e y).2 hsy,(routed_one_iff e w).2 hsw,hxy,hyw⟩

end CoreCouplingGlobal
