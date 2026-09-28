import proofs.RandomViability.CollectiveGrowth
import Mathlib.Tactic

namespace StartupCount
open RandomViability

/-- Count-scale logarithmic correction: the physical adapter must supply
the selected-birth and adverse-copy-flux logarithmic bound. Positive channels
not used by that adapter need not be charged to quadratic variation. -/
theorem count_log_occupation (u w du dw C K L V : ℝ)
    (hu : 0 ≤ u) (hw : 0 ≤ w) (hC : 0 ≤ C) (hK : 2 < K)
    (huw : 4*u*w ≤ 121/4) (hdelta : 1+25*C ≤ 1476)
    (hdu : 1-u-23*C*u ≤ du) (hdw : 1-w-23*C*w ≤ dw)
    (hlog : 4*u*w-1-25*C-4*u*w/K-2*(1+25*C)/(K-2) ≤ L) :
    2-117*C-3000/(K-2)-768000/V ≤
      L+8*foodDeficit u*du+8*foodDeficit w*dw-768000/V := by
  have h1 := deficit_drift u du C hC hdu
  have h2 := deficit_drift w dw C hC hdw
  have hp := food_product_deficit u w hu hw
  have hk0 : 0 < K := by linarith
  have hk2 : 0 < K-2 := by linarith
  have hc1 : 4*u*w/K ≤ (121/4)/(K-2) := by
    apply (div_le_div_of_nonneg_right huw hk0.le).trans
    exact div_le_div_of_nonneg_left (by norm_num) hk2 (by linarith)
  have hc2 : 2*(1+25*C)/(K-2) ≤ 2952/(K-2) := by
    apply div_le_div_of_nonneg_right _ hk2.le
    linarith
  have hc3 : (121/4)/(K-2)+2952/(K-2) ≤ 3000/(K-2) := by
    rw [← add_div]
    exact div_le_div_of_nonneg_right (by norm_num) hk2.le
  linarith

end StartupCount
