import proofs.FiniteCopy.LocalNonlinear

namespace FiniteCopy
open CoreCouplingCAC Set

theorem low_source_dissipation (z : ℝ)
    (hz : z ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (hs : Stationary sourceRates (lift sourceRates z)) (y : Point)
    (hy : ∀ i, |y i| ≤ 1/400) :
    2*lowPair y (drift (1/100000) 0 (fun i => pointOfState (lift sourceRates z) i+y i)) ≤
      -(59/100)*normSq y := by
  let s := pointOfState (lift sourceRates z)
  have hzero : drift (1/100000) 0 s = 0 := stationary_drift_zero _ hs
  have hb := low_source_box z hz
  have hlin : 2*lowPair y (sourceLinear (s 0) (s 1) (s 2) y) ≤ -(84/100)*normSq y := by
    apply lowlinear_dissipation
    · convert hb.1 using 1
      norm_num [s,pointOfState,lift]
    · convert hb.2.1 using 1
      norm_num [s,pointOfState,lift]
    · change z ∈ _
      norm_num at hz ⊢
      exact hz
  have hid : drift (1/100000) 0 (fun i => s i+y i) =
      fun i => sourceLinear (s 0) (s 1) (s 2) y i+sourceRemainder y i := by
    rw [source_remainder_identity,hzero]
    simp only [Pi.zero_apply,zero_add]
  change 2*lowPair y (drift (1/100000) 0 (fun i => s i+y i)) ≤ _
  rw [hid,lowPair_add]
  linarith only [hlin,lowcubic_bound y hy]

theorem high_source_dissipation (z : ℝ)
    (hz : z ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
    (hs : Stationary sourceRates (lift sourceRates z)) (y : Point)
    (hy : ∀ i, |y i| ≤ 1/400) :
    2*highPair y (drift (1/100000) 0 (fun i => pointOfState (lift sourceRates z) i+y i)) ≤
      -(59/100)*normSq y := by
  let s := pointOfState (lift sourceRates z)
  have hzero : drift (1/100000) 0 s = 0 := stationary_drift_zero _ hs
  have hb := high_source_box z hz
  have hlin : 2*highPair y (sourceLinear (s 0) (s 1) (s 2) y) ≤ -(84/100)*normSq y := by
    apply highlinear_dissipation
    · convert hb.1 using 1
      norm_num [s,pointOfState,lift]
    · exact hb.2.1
    · change z ∈ _
      norm_num at hz ⊢
      exact hz
  have hid : drift (1/100000) 0 (fun i => s i+y i) =
      fun i => sourceLinear (s 0) (s 1) (s 2) y i+sourceRemainder y i := by
    rw [source_remainder_identity,hzero]
    simp only [Pi.zero_apply,zero_add]
  change 2*highPair y (drift (1/100000) 0 (fun i => s i+y i)) ≤ _
  rw [hid,highPair_add]
  linarith only [hlin,highcubic_bound y hy]

end FiniteCopy


