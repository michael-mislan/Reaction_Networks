import proofs.ProductiveRecovery.SourceFlow

namespace C4Assemblies
open ProductiveRecovery
noncomputable section

theorem sharp_phase_comparison (r d : ℝ) (c : State) (hc : Nonneg c)
    (hr : 19 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25)
    (hA : A c ≤ 11/10) (hB : B c ≤ 11/10) :
    -48*c 2+20*c 3+38*c 5 ≤ field r d c 2 ∧
    -48*c 3+20*c 4 ≤ field r d c 3 ∧
    -48*c 4 ≤ field r d c 4 ∧
    -48*c 5+20*c 4 ≤ field r d c 5 := by
  have hu : c 0 ≤ 11/10 := by dsimp [A] at hA; linarith [hc 2,hc 3,hc 4,hc 5]
  have hw : c 1 ≤ 11/10 := by dsimp [B] at hB; linarith [hc 2,hc 3,hc 4,hc 5]
  have hx : c 2 ≤ 11/10 := by dsimp [A] at hA; linarith [hc 0,hc 3,hc 4,hc 5]
  have hjoint : c 0+c 2 ≤ 11/10 := by dsimp [A] at hA; linarith [hc 3,hc 4,hc 5]
  have hjointx := mul_le_mul_of_nonneg_right hjoint (hc 2)
  have hux := mul_le_mul_of_nonneg_right hu (hc 2)
  have hwc := mul_le_mul_of_nonneg_right hw (hc 3)
  have hxx := mul_le_mul_of_nonneg_right hx (hc 2)
  have hrx := mul_le_mul_of_nonneg_right hr' (sq_nonneg (c 2))
  have hrl := mul_le_mul_of_nonneg_right hr (hc 5)
  have hrz := mul_le_mul_of_nonneg_right hr' (hc 5)
  have hdx := mul_le_mul_of_nonneg_right hd' (hc 2)
  have him : 0 ≤ ((1/500000000)+d*(1/8000000000))*c 0*c 1 :=
    mul_nonneg (mul_nonneg (by positivity) (hc 0)) (hc 1)
  have hxu := mul_nonneg (hc 2) (hc 0)
  have hcw := mul_nonneg (hc 3) (hc 1)
  have hrxx := mul_nonneg (show 0 ≤ r by linarith) (sq_nonneg (c 2))
  change -48*c 2+20*c 3+38*c 5 ≤
    -c 2+((1/500000000)*c 0*c 1-(1/5000000000)*c 2)-
      (20*c 2*c 0-20*c 3)+2*(r*(c 5-c 2^2))-
      (d*c 2-d*(1/8000000000)*c 0*c 1) ∧
    -48*c 3+20*c 4 ≤ -c 3+(20*c 2*c 0-20*c 3)-(20*c 3*c 1-20*c 4) ∧
    -48*c 4 ≤ -c 4+(20*c 3*c 1-20*c 4)-(20*c 4-2*c 5) ∧
    -48*c 5+20*c 4 ≤ -c 5+(20*c 4-2*c 5)-r*(c 5-c 2^2)
  constructor
  · nlinarith [hc 2]
  constructor
  · nlinarith [hc 3]
  constructor <;> nlinarith [hc 4,hc 5]

end
end C4Assemblies
