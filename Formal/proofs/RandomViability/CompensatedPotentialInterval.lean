import proofs.RandomViability.CompensatedCollectiveGrowth
import proofs.RandomViability.CollectiveCalculus

namespace RandomViability
open Set MeasureTheory
noncomputable section
set_option maxHeartbeats 100000

/-- Integrate the robust potential on a single (possibly truncated) holding
interval. The count state is constant while each corrected coordinate is affine. -/
theorem compensated_holding_potential_gain (u w x au aw ax du dw dx C a b : ℝ)
    (hu : 0 ≤ u) (hw : 0 ≤ w) (hx : 0 < x) (hC : 0 ≤ C) (hab : a ≤ b)
    (hdu : 1-u-23*C*u ≤ du) (hdw : 1-w-23*C*w ≤ dw)
    (hdx : x*(4*u*w-1-25*C) ≤ dx)
    (hnoiseU : ∀ s ∈ Icc a b,|au-du*s| ≤ (1/100000 : ℝ))
    (hnoiseW : ∀ s ∈ Icc a b,|aw-dw*s| ≤ (1/100000 : ℝ))
    (hnoiseX : ∀ s ∈ Icc a b,|ax-dx*s| ≤ x/100) :
    (b-a)*((19/10 : ℝ)-120*C) ≤
      collectivePotential (u-au+du*b) (w-aw+dw*b) (x-ax+dx*b)-
      collectivePotential (u-au+du*a) (w-aw+dw*a) (x-ax+dx*a) := by
  let P := fun s => collectivePotential (u-au+du*s) (w-aw+dw*s) (x-ax+dx*s)
  let D := fun s => dx/(x-ax+dx*s)-
    4*(-2*foodDeficit (u-au+du*s)*du-2*foodDeficit (w-aw+dw*s)*dw)
  have hd : ∀ s ∈ Icc a b,HasDerivAt P (D s) s := by
    intro s hs
    apply collectivePotential_hasDerivAt
    · simpa only [zero_add,mul_one] using
        (hasDerivAt_const s (u-au)).add ((hasDerivAt_id s).const_mul du)
    · simpa only [zero_add,mul_one] using
        (hasDerivAt_const s (w-aw)).add ((hasDerivAt_id s).const_mul dw)
    · simpa only [zero_add,mul_one] using
        (hasDerivAt_const s (x-ax)).add ((hasDerivAt_id s).const_mul dx)
    · have ha := (abs_le.mp (hnoiseX s hs)).2
      have hp : 0 < x-ax+dx*s := by linarith only [hx,ha]
      exact ne_of_gt hp
  have hbound : ∀ s ∈ Ioo a b,(19/10 : ℝ)-120*C ≤ D s := by
    intro s hs
    have hs' : s ∈ Icc a b := ⟨hs.1.le,hs.2.le⟩
    have hh := compensated_collective_growth u w x (au-du*s) (aw-dw*s) (ax-dx*s)
      du dw dx C hu hw hx hC (hnoiseU s hs') (hnoiseW s hs') (hnoiseX s hs') hdu hdw hdx
    have hU : u-(au-du*s) = u-au+du*s := by ring
    have hW : w-(aw-dw*s) = w-aw+dw*s := by ring
    have hX : x-(ax-dx*s) = x-ax+dx*s := by ring
    simpa only [hU,hW,hX] using hh
  have hcont : ContinuousOn P (Icc a b) := fun s hs => (hd s hs).continuousAt.continuousWithinAt
  have hh := intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le hab hcont
    (fun s hs => (hd s ⟨hs.1.le,hs.2.le⟩).hasDerivWithinAt)
    (continuousOn_const.integrableOn_Icc : IntegrableOn (fun _ : ℝ => (19/10 : ℝ)-120*C) (Icc a b))
    hbound
  simpa only [intervalIntegral.integral_const,smul_eq_mul] using hh

end
end RandomViability
