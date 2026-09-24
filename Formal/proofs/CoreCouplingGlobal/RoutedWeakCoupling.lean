import proofs.CoreCouplingGlobal.RoutedResponse
import proofs.CoreCouplingGlobal.Response

namespace CoreCouplingGlobal
open CoreCouplingCAC Set

theorem routed_stationary_balances (e g : ℝ) (x : State)
    (hs : RoutedStationary e g x) :
    x.B*routedDen g x.z=60 ∧
    e*x.A^2+x.A+(1-e)*x.B=33 ∧
    g*(x.A-x.B*x.z)=routedK x.z := by
  obtain ⟨ha,hb,hz,hh⟩ := hs
  dsimp [fA,fB,fH,routedZ,flagshipRates] at ha hb hz hh
  refine ⟨?_,?_,?_⟩
  · dsimp [routedDen]
    linear_combination -ha-2*hb
  · linear_combination -ha-hb
  · dsimp [routedK]
    linear_combination hz+(30000/20001:ℝ)*hh

theorem routed_small_positive_z (e g : ℝ) (hg : 0 ≤ g) (hgu : g ≤ 1/10)
    (x : State) (hx : x.Positive) (hs : RoutedStationary e g x) : 4 < x.z := by
  obtain ⟨hB,_,hK⟩ := routed_stationary_balances e g x hs
  have hd : 2 ≤ routedDen g x.z := by
    dsimp [routedDen]
    nlinarith [mul_nonneg hg hx.2.2.1.le]
  have hb : x.B ≤ 30 := by nlinarith [mul_nonneg hx.2.1.le (sub_nonneg.mpr hd)]
  have hgb : g*x.B ≤ 3 := by nlinarith [mul_nonneg (sub_nonneg.mpr hgu) hx.2.1.le]
  by_contra hz
  have hzu : x.z ≤ 4 := le_of_not_gt hz
  have hk : routedK x.z < -3*x.z := by
    have hm := mul_pos hx.2.2.1 (show 0 < 99981-20004*x.z by linarith)
    dsimp [routedK]
    nlinarith
  have hm := mul_nonneg (sub_nonneg.mpr hgb) hx.2.2.1.le
  have ha := mul_nonneg hg hx.1.le
  nlinarith

theorem routed_load_strictMonoOn : StrictMonoOn routedK (Ici (4:ℝ)) := by
  intro x hx y hy hxy
  have hsum : 0 < 20004*(y+x)-159984 := by
    have hx' : 4 ≤ x := hx
    have hy' : 4 ≤ y := hy
    linarith
  have hp := mul_pos (sub_pos.mpr hxy) hsum
  dsimp [routedK]
  nlinarith

theorem routed_small_no_ordered_pair (e g : ℝ) (he : 0 ≤ e)
    (hg : 0 ≤ g) (hgu : g ≤ 1/10) (x y : State)
    (hx : x.Positive) (hy : y.Positive)
    (hsx : RoutedStationary e g x) (hsy : RoutedStationary e g y)
    (hxy : x.z < y.z) : False := by
  obtain ⟨hBx,hAx,hKx⟩ := routed_stationary_balances e g x hsx
  obtain ⟨hBy,hAy,hKy⟩ := routed_stationary_balances e g y hsy
  have hz := routed_small_positive_z e g hg hgu x hx hsx
  have hK : routedK x.z < routedK y.z :=
    routed_load_strictMonoOn hz.le (by exact (hz.trans hxy).le) hxy
  by_cases hg0 : g=0
  · simp only [hg0,zero_mul] at hKx hKy
    linarith
  have hgp : 0 < g := lt_of_le_of_ne hg (Ne.symm hg0)
  have hdx : 0 < routedDen g x.z := by
    dsimp [routedDen]
    nlinarith [mul_nonneg hg hx.2.2.1.le]
  have hdd : routedDen g x.z < routedDen g y.z := by
    dsimp [routedDen]
    nlinarith [mul_pos hgp (sub_pos.mpr hxy)]
  have hb : y.B < x.B := by
    by_contra h
    have hle : x.B ≤ y.B := le_of_not_gt h
    nlinarith [mul_nonneg (sub_nonneg.mpr hle) hdx.le,
      mul_pos hy.2.1 (sub_pos.mpr hdd)]
  have hid : g*(y.A-x.A)=(3-g)*(x.B-y.B)+(routedK y.z-routedK x.z) := by
    dsimp [routedDen] at hBx hBy
    linear_combination hKy-hKx+hBy-hBx
  have hdiff : x.B-y.B < y.A-x.A := by
    have hp := mul_pos (show 0 < 3-2*g by linarith) (sub_pos.mpr hb)
    nlinarith
  have ha : x.A < y.A := by linarith
  have hsq : 0 < y.A^2-x.A^2 := by nlinarith [mul_pos (sub_pos.mpr ha) (add_pos hy.1 hx.1)]
  have heq := mul_nonneg he hsq.le
  have heb := mul_nonneg he (sub_pos.mpr hb).le
  nlinarith

theorem routed_small_unique (e g : ℝ) (he : 0 ≤ e)
    (hg : 0 ≤ g) (hgu : g ≤ 1/10) (x y : State)
    (hx : x.Positive) (hy : y.Positive)
    (hsx : RoutedStationary e g x) (hsy : RoutedStationary e g y) : x=y := by
  have hz : x.z=y.z := by
    rcases lt_trichotomy x.z y.z with h|h|h
    · exact False.elim (routed_small_no_ordered_pair e g he hg hgu x y hx hy hsx hsy h)
    · exact h
    · exact False.elim (routed_small_no_ordered_pair e g he hg hgu y x hy hx hsy hsx h)
  obtain ⟨hBx,hAx,_⟩ := routed_stationary_balances e g x hsx
  obtain ⟨hBy,hAy,_⟩ := routed_stationary_balances e g y hsy
  have hd : routedDen g x.z ≠ 0 := by
    have hp := mul_nonneg hg hx.2.2.1.le
    dsimp [routedDen]
    linarith
  have hb : x.B=y.B := by rw [← hz] at hBy; exact (mul_right_cancel₀ hd) (hBx.trans hBy.symm)
  have hf : (x.A-y.A)*(1+e*(x.A+y.A))=0 := by rw [← hb] at hAy; nlinarith only [hAx,hAy]
  have hp : 0 < 1+e*(x.A+y.A) := by
    have hm := mul_nonneg he (add_pos hx.1 hy.1).le
    linarith
  have ha : x.A=y.A := sub_eq_zero.mp ((mul_eq_zero.mp hf).resolve_right (ne_of_gt hp))
  have hHx := hsx.2.2.2
  have hHy := hsy.2.2.2
  dsimp [fH,flagshipRates] at hHx hHy
  have hh : x.H=y.H := by rw [hz] at hHx; linarith only [hHx,hHy]
  cases x
  cases y
  simp_all

end CoreCouplingGlobal
