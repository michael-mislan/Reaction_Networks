import proofs.CoreCouplingGlobal.RoutedCharacterization
import proofs.CoreCouplingGlobal.RoutedCausalComparison

namespace CoreCouplingGlobal
open CoreCouplingCAC Set

/-- Positive module balance bounds the increase in A by the decrease in B.
This algebraic inequality applies to any common feed total. -/
theorem positive_response_increment (e total A₁ A₂ B₁ B₂ : ℝ)
    (he : 0 ≤ e) (hA₁ : 0 < A₁) (hA₂ : 0 < A₂) (hB : B₂ < B₁)
    (h₁ : e*A₁^2+A₁+(1-e)*B₁=total)
    (h₂ : e*A₂^2+A₂+(1-e)*B₂=total) : A₂-A₁ ≤ B₁-B₂ := by
  by_contra h
  have ha : A₁ < A₂ := by linarith
  have hs : 0 < A₂^2-A₁^2 := by
    nlinarith [mul_pos (sub_pos.mpr ha) (add_pos hA₂ hA₁)]
  have hp := mul_nonneg he hs.le
  have hb := mul_nonneg he (sub_pos.mpr hB).le
  nlinarith only [h₁,h₂,h,hp,hb]

/-- Necessary feedback mechanism, valid beyond the certified bistable rectangle:
distinct positive stationary states require a strictly decreasing load secant. -/
theorem routed_multiplicity_requires_decreasing_load (e g : ℝ) (he : 0 ≤ e)
    (hg : 0 < g) (hgu : g ≤ 1) (x y : State)
    (hx : x.Positive) (hy : y.Positive)
    (hsx : RoutedStationary e g x) (hsy : RoutedStationary e g y)
    (hz : x.z < y.z) : routedK y.z < routedK x.z := by
  obtain ⟨hBx,hAx,hKx⟩ := routed_stationary_balances e g x hsx
  obtain ⟨hBy,hAy,hKy⟩ := routed_stationary_balances e g y hsy
  have hd := routed_den_positive g x.z hg hgu hx.2.2.1
  have hdd : routedDen g x.z < routedDen g y.z := by
    dsimp [routedDen]
    nlinarith [mul_pos hg (sub_pos.mpr hz)]
  have hb : y.B < x.B := by
    by_contra h
    have hle : x.B ≤ y.B := le_of_not_gt h
    nlinarith [mul_nonneg (sub_nonneg.mpr hle) hd.le,
      mul_pos hy.2.1 (sub_pos.mpr hdd)]
  have ha := positive_response_increment e 33 x.A y.A x.B y.B he hx.1 hy.1 hb hAx hAy
  have hid : g*(y.A-x.A)=(3-g)*(x.B-y.B)+(routedK y.z-routedK x.z) := by
    dsimp [routedDen] at hBx hBy
    linear_combination hKy-hKx+hBy-hBx
  have hmul := mul_le_mul_of_nonneg_left ha hg.le
  have hp := mul_pos (show 0 < 3-2*g by linarith) (sub_pos.mpr hb)
  nlinarith only [hid,hmul,hp]

theorem routed_distinct_stationary_sum_bound (e g : ℝ) (he : 0 ≤ e)
    (hg : 0 < g) (hgu : g ≤ 1) (x y : State)
    (hx : x.Positive) (hy : y.Positive)
    (hsx : RoutedStationary e g x) (hsy : RoutedStationary e g y)
    (hz : x.z < y.z) : x.z+y.z < (13332/1667:ℝ) := by
  have hk := routed_multiplicity_requires_decreasing_load e g he hg hgu x y hx hy hsx hsy hz
  have hid : routedK y.z-routedK x.z=
      (y.z-x.z)*(20004*(x.z+y.z)-159984)/20001 := by
    dsimp [routedK]
    ring
  have hm : (y.z-x.z)*(20004*(x.z+y.z)-159984) < 0 := by
    rw [← sub_neg] at hk
    rw [hid] at hk
    linarith only [hk]
  by_contra h
  have hn : 0 ≤ 20004*(x.z+y.z)-159984 := by linarith
  have hp := mul_nonneg (sub_pos.mpr hz).le hn
  linarith only [hm,hp]

theorem routed_unique_on_monotone_load (e g : ℝ) (he : 0 ≤ e)
    (hg : 0 < g) (hgu : g ≤ 1) (S : Set ℝ) (hK : MonotoneOn routedK S)
    (x y : State) (hx : x.Positive) (hy : y.Positive)
    (hsx : RoutedStationary e g x) (hsy : RoutedStationary e g y)
    (hSx : x.z ∈ S) (hSy : y.z ∈ S) : x=y := by
  have hz : x.z=y.z := by
    rcases lt_trichotomy x.z y.z with h|h|h
    · have hk := routed_multiplicity_requires_decreasing_load e g he hg hgu x y hx hy hsx hsy h
      have hm := hK hSx hSy h.le
      linarith
    · exact h
    · have hk := routed_multiplicity_requires_decreasing_load e g he hg hgu y x hy hx hsy hsx h
      have hm := hK hSy hSx h.le
      linarith
  have hx' := (routed_stationary_reconstruction e g hg hgu x hx hsx).1
  have hy' := (routed_stationary_reconstruction e g hg hgu y hy hsy).1
  rw [hz] at hx'
  exact hx'.trans hy'.symm

/-- The successful family realizes the load competition with unchanged intrinsic
rates: admissible weak coupling is unique and admissible strong coupling has
two actual attractors whose stationary loads are oppositely ordered. -/
theorem routed_mechanism_realized (e weak strong : ℝ)
    (hp : (e,strong) ∈ routedBistableRegion)
    (hw : (1/100:ℝ) ≤ weak) (hwu : weak ≤ 1/10) :
    (RoutedCoreCertificate e weak ∧
      (∃! x : State, x.Positive ∧ RoutedStationary e weak x)) ∧
    RoutedCoreCertificate e strong ∧
    ∃ x y : State, x.Positive ∧ y.Positive ∧ RoutedStationary e strong x ∧
      RoutedStationary e strong y ∧ x.z < y.z ∧ routedK y.z < routedK x.z ∧
      RoutedSelected e strong lowLeft lowRight x ∧
      RoutedSelected e strong highLeft highRight y := by
  obtain ⟨hweak,hcore,_,x,y,hx,hy,hsx,hsy,hxy,hl,hh⟩ :=
    admissible_feedback_creates_bistability e weak strong hp hw hwu
  have he : 0 ≤ e := by have h := hp.1.1; linarith
  have hg : 0 < strong := by have h := hp.2.1; linarith
  exact ⟨hweak,hcore,x,y,hx,hy,hsx,hsy,hxy,
    routed_multiplicity_requires_decreasing_load e strong he hg hp.2.2.le x y hx hy hsx hsy hxy,
    hl,hh⟩

end CoreCouplingGlobal
