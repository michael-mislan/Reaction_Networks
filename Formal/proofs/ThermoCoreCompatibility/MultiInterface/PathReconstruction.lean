import proofs.ThermoCoreCompatibility.MultiInterface.PathResponse

namespace ThermoCoreCompatibility.MultiInterface.Path

/-- All internal species and endpoints obey the same closed activity box. -/
def BoxRealizes (ell : ℝ) : Path → ℝ → ℝ → Prop
  | .single w, x, y => ell ≤ x ∧ x ≤ 1 ∧ ell ≤ y ∧ y ≤ 1 ∧ w.Productive x y
  | .snoc p w, x, y => ∃ t, p.BoxRealizes ell x t ∧ ell ≤ y ∧ y ≤ 1 ∧ w.Productive t y

theorem BoxRealizes.realizes {p : Path} {ell x y : ℝ} (h : p.BoxRealizes ell x y) :
    p.Realizes x y := by
  induction p generalizing x y with
  | single w => exact h.2.2.2.2
  | snoc p w ih =>
    obtain ⟨t,hp,_,_,hw⟩ := h
    exact ⟨t,ih hp,hw⟩

theorem box_of_realizes {p : Path} {ell x y : ℝ} (h : p.Realizes x y)
    (hy : ell ≤ y) (hx : x ≤ 1) : p.BoxRealizes ell x y := by
  induction p generalizing x y with
  | single w =>
    have hd := w.decreases h
    exact ⟨hy.trans hd.le,hx,hy,hd.le.trans hx,h⟩
  | snoc p w ih =>
    obtain ⟨t,hp,hw⟩ := h
    have hd := w.decreases hw
    have ht := p.realizes_decreases hp
    exact ⟨t,ih hp (hy.trans hd.le) hx,hy,hd.le.trans (ht.le.trans hx),hw⟩

theorem boxed_iff (p : Path) {ell x y : ℝ} (hell : 0 < ell)
    (hx : ell ≤ x) (hx1 : x ≤ 1) (hy : ell ≤ y) :
    p.BoxRealizes ell x y ↔ p.lower x < y ∧ y < p.upper x := by
  constructor
  · intro h
    exact p.necessary (hell.trans_le hx) h.realizes
  · intro h
    have hlt : x < 1 := by
      rcases hx1.eq_or_lt with he | he
      · subst x
        simp only [lower_one, upper_one] at h
        exact False.elim (lt_asymm h.1 h.2)
      · exact he
    exact box_of_realizes (p.sufficient (hell.trans_le hx) hlt h) hy hx1

end ThermoCoreCompatibility.MultiInterface.Path
