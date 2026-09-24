import proofs.ThermoCoreCompatibility.MultiInterface.WeightedPair
import Mathlib.Topology.Order.IntermediateValue

namespace ThermoCoreCompatibility.MultiInterface

/-- A nonempty path, built in physical order by appending its final edge. -/
inductive Path where
  | single : Factors → Path
  | snoc : Path → Factors → Path

namespace Path

noncomputable def lower : Path → ℝ → ℝ
  | .single w, x => w.lower x
  | .snoc p w, x => w.lower (p.lower x)

noncomputable def upper : Path → ℝ → ℝ
  | .single w, x => w.upper x
  | .snoc p w, x => w.upper (p.upper x)

def Realizes : Path → ℝ → ℝ → Prop
  | .single w, x, y => w.Productive x y
  | .snoc p w, x, y => ∃ t, p.Realizes x t ∧ w.Productive t y

noncomputable def blend (w : Factors) (t x : ℝ) : ℝ :=
  (1-t)*w.lower x+t*w.upper x

noncomputable def interpolate : Path → ℝ → ℝ → ℝ
  | .single w, t, x => blend w t x
  | .snoc p w, t, x => blend w t (p.interpolate t x)

theorem lower_pos (p : Path) {x : ℝ} (hx : 0 < x) : 0 < p.lower x := by
  induction p with
  | single w => exact w.lower_pos hx
  | snoc p w ih => exact w.lower_pos ih

theorem upper_pos (p : Path) {x : ℝ} (hx : 0 < x) : 0 < p.upper x := by
  induction p with
  | single w => simpa using w.upper_strictMono (by simp) hx.le hx
  | snoc p w ih => simpa [upper] using w.upper_strictMono (by simp) ih.le ih

@[simp] theorem lower_one (p : Path) : p.lower 1 = 1 := by
  induction p with
  | single w => exact w.lower_one
  | snoc p w ih => simp [lower, ih]

@[simp] theorem upper_one (p : Path) : p.upper 1 = 1 := by
  induction p with
  | single w => exact w.upper_one
  | snoc p w ih => simp [upper, ih]

theorem realizes_pos (p : Path) {x y : ℝ} (h : p.Realizes x y) : 0 < y := by
  induction p generalizing x y with
  | single w =>
    have hq := (w.currents_positive h).2
    have := (mul_pos_iff_of_pos_left w.b_pos).mp hq
    nlinarith [sq_nonneg x]
  | snoc p w _ =>
    obtain ⟨t,_,ht⟩ := h
    have hq := (w.currents_positive ht).2
    have := (mul_pos_iff_of_pos_left w.b_pos).mp hq
    nlinarith [sq_nonneg t]

theorem realizes_decreases (p : Path) {x y : ℝ} (h : p.Realizes x y) : y < x := by
  induction p generalizing x y with
  | single w => exact w.decreases h
  | snoc p w ih =>
    obtain ⟨t,hp,hw⟩ := h
    exact (w.decreases hw).trans (ih hp)

theorem necessary (p : Path) {x y : ℝ} (hx : 0 < x) (h : p.Realizes x y) :
    p.lower x < y ∧ y < p.upper x := by
  induction p generalizing y with
  | single w => exact (w.productive_iff x y).mp h
  | snoc p w ih =>
    obtain ⟨t,hp,hw⟩ := h
    obtain ⟨hl,hu⟩ := ih hp
    obtain ⟨hwl,hwu⟩ := (w.productive_iff t y).mp hw
    exact ⟨(w.lower_strictMono (p.lower_pos hx).le (p.realizes_pos hp).le hl).trans hwl,
      hwu.trans (w.upper_strictMono (p.realizes_pos hp).le (p.upper_pos hx).le hu)⟩

theorem blend_inside (w : Factors) {t x : ℝ} (ht : 0 < t) (ht1 : t < 1)
    (hx : 0 < x) (hx1 : x < 1) : w.Productive x (blend w t x) := by
  apply (w.productive_iff _ _).2
  have hg := w.lower_lt_upper hx hx1
  have h₁ := mul_pos ht (sub_pos.mpr hg)
  have h₂ := mul_pos (sub_pos.mpr ht1) (sub_pos.mpr hg)
  unfold blend
  constructor <;> nlinarith

theorem interpolate_realizes (p : Path) {t x : ℝ} (ht : 0 < t) (ht1 : t < 1)
    (hx : 0 < x) (hx1 : x < 1) : p.Realizes x (p.interpolate t x) := by
  induction p with
  | single w => exact blend_inside w ht ht1 hx hx1
  | snoc p w ih =>
    exact ⟨p.interpolate t x, ih, blend_inside w ht ht1 (p.realizes_pos ih)
      ((p.realizes_decreases ih).trans hx1)⟩

@[simp] theorem interpolate_zero (p : Path) (x : ℝ) : p.interpolate 0 x = p.lower x := by
  induction p with
  | single w => simp [interpolate, blend, lower]
  | snoc p w ih => simp [interpolate, blend, lower, ih]

@[simp] theorem interpolate_one (p : Path) (x : ℝ) : p.interpolate 1 x = p.upper x := by
  induction p with
  | single w => simp [interpolate, blend, upper]
  | snoc p w ih => simp [interpolate, blend, upper, ih]

theorem continuous_interpolate (p : Path) (x : ℝ) : Continuous (fun t => p.interpolate t x) := by
  induction p with
  | single w => unfold interpolate blend; fun_prop
  | snoc p w ih =>
    change Continuous (fun t => (1-t)*w.lower (p.interpolate t x)+t*w.upper (p.interpolate t x))
    exact ((continuous_const.sub continuous_id).mul (w.continuous_lower.comp ih)).add
      (continuous_id.mul (w.continuous_upper.comp ih))

theorem sufficient (p : Path) {x y : ℝ} (hx : 0 < x) (hx1 : x < 1)
    (h : p.lower x < y ∧ y < p.upper x) : p.Realizes x y := by
  have hh : y ∈ Set.Ioo (p.interpolate 0 x) (p.interpolate 1 x) := by simpa using h
  obtain ⟨t,ht,he⟩ := intermediate_value_Ioo (show (0:ℝ) ≤ 1 by norm_num)
    (p.continuous_interpolate x).continuousOn hh
  rw [← he]
  exact p.interpolate_realizes ht.1 ht.2 hx hx1

theorem realizes_iff (p : Path) {x y : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    p.Realizes x y ↔ p.lower x < y ∧ y < p.upper x :=
  ⟨p.necessary hx, p.sufficient hx hx1⟩

end Path
end ThermoCoreCompatibility.MultiInterface
