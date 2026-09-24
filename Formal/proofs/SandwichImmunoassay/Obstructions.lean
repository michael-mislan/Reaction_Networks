import proofs.SandwichImmunoassay.Controls

noncomputable section

namespace SandwichImmunoassay

theorem Occupancy.scale {x C K p s : ℝ} (h : Occupancy x C K p) (hs : 0<s) :
    Occupancy (s*x) (s*C) (s*K) p := by
  refine ⟨mul_nonneg hs.le h.x_nonneg, mul_pos hs h.total_pos,
    mul_pos hs h.kd_pos, h.pos,h.lt_one,?_⟩
  rw [h.balance]
  ring

theorem scale_signal {s x p q g : ℝ} (hs : 0<s) :
    (g/s)*signal (s*x) p q = g*signal x p q := by
  dsimp [signal]
  field_simp

/-- Quantitative finite-panel tail bound. Every finite positive panel has a finite
upper dilution M. The displayed concentration condition makes blank compatible. -/
theorem tail_blank {x d M eps C D K J p q : ℝ}
    (h : Reaction (x/d) C D K J p q)
    (hc : InBox C) (hd : InBox D) (hk : InBox K) (hj : InBox J)
    (hd0 : 0<d) (hdM : d≤M) (hx : 0<x)
    (hlarge : (121/100)*M ≤ eps*x) :
    |signal (x/d) p q| ≤ eps := by
  have b := (h.box_bounds hc hd hk hj).2
  have mult := mul_le_mul_of_nonneg_right b hd0.le
  have idn : (x/d)*signal (x/d) p q*d = x*signal (x/d) p q := by field_simp
  rw [idn] at mult
  have sm : x*signal (x/d) p q ≤ eps*x := by nlinarith
  rw [abs_of_nonneg h.signal_nonneg]
  nlinarith

def hook (x : ℝ) : ℝ := x/(1+x)^2

theorem no_rise_hooked : (1:ℝ)<3 ∧ hook (3/10)<hook 3 := by norm_num [hook]

theorem hook_involution {x : ℝ} (hx : 0<x) : hook (1/x)=hook x := by
  dsimp [hook]
  field_simp
  ring

end SandwichImmunoassay
