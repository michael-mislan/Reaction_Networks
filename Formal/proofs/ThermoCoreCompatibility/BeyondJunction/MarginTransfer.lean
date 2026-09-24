import proofs.ThermoCoreCompatibility.BeyondJunction.SourceBoxes
import Mathlib.Tactic.Ring

namespace ThermoCoreCompatibility.BeyondJunction

open MultiInterface

theorem quadratic_lipschitz (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    {x y : ℝ} (hx : x ∈ Set.Icc 0 1) (hy : y ∈ Set.Icc 0 1) :
    |(a*x+b*x^2)/(a+b)-(a*y+b*y^2)/(a+b)| ≤ 2*|x-y| := by
  have hd : 0 < a+b := add_pos ha hb
  have hs : |x^2-y^2| ≤ 2*|x-y| := by
    calc
      |x^2-y^2| = |x-y| *|x+y| := by rw [← abs_mul]; congr 1; ring
      _ ≤ |x-y| *2 := mul_le_mul_of_nonneg_left
        (by rw [abs_of_nonneg (add_nonneg hx.1 hy.1)]; linarith [hx.2,hy.2]) (abs_nonneg _)
      _ = _ := by ring
  rw [← sub_div, abs_div, abs_of_pos hd, div_le_iff₀ hd]
  calc
    |a*x+b*x^2-(a*y+b*y^2)| = |a*(x-y)+b*(x^2-y^2)| := by congr 1; ring
    _ ≤ |a*(x-y)|+|b*(x^2-y^2)| := abs_add_le _ _
    _ = a*|x-y|+b*|x^2-y^2| := by rw [abs_mul,abs_mul,abs_of_pos ha,abs_of_pos hb]
    _ ≤ a*|x-y|+b*(2*|x-y|) := add_le_add le_rfl (mul_le_mul_of_nonneg_left hs hb.le)
    _ ≤ 2*|x-y| *(a+b) := by nlinarith [mul_nonneg ha.le (abs_nonneg (x-y))]

theorem lower_lipschitz (w : Factors) {x y : ℝ}
    (hx : x ∈ Set.Icc 0 1) (hy : y ∈ Set.Icc 0 1) :
    |w.lower x-w.lower y| ≤ 2*|x-y| := by
  exact quadratic_lipschitz w.a (2*w.b) w.a_pos (by have := w.b_pos; positivity) hx hy

theorem upper_lipschitz (w : Factors) {x y : ℝ}
    (hx : x ∈ Set.Icc 0 1) (hy : y ∈ Set.Icc 0 1) :
    |w.upper x-w.upper y| ≤ 2*|x-y| :=
  quadratic_lipschitz w.a w.b w.a_pos w.b_pos hx hy

theorem edge_margin_transfer (w : Factors) {x y X Y eps eta : ℝ}
    (hx : x ∈ Set.Icc 0 1) (hX : X ∈ Set.Icc 0 1)
    (dx : |X-x| ≤ eta) (dy : |Y-y| ≤ eta)
    (hl : eps ≤ y-w.lower x) (hu : eps ≤ w.upper x-y) :
    eps-3*eta ≤ Y-w.lower X ∧ eps-3*eta ≤ w.upper X-Y := by
  have hG := lower_lipschitz w hX hx
  have hF := upper_lipschitz w hX hx
  have hy := abs_le.mp dy
  have hg := abs_le.mp hG
  have hf := abs_le.mp hF
  constructor <;> linarith

theorem margin_boxed_productive {V E : Type*}
    (src dst : E → V) (w : E → Factors) (lo hi z Z : V → ℝ)
    {eps eta : ℝ} (heps : 0 < eps) (heta : eta ≤ eps/4)
    (hz : ∀ v, z v ∈ Set.Icc 0 1) (hZ : ∀ v, Z v ∈ Set.Icc 0 1)
    (hbox : ∀ v, lo v ≤ Z v ∧ Z v ≤ hi v)
    (hd : ∀ v, |Z v-z v| ≤ eta)
    (hm : ∀ e, eps ≤ z (dst e)-(w e).lower (z (src e)) ∧
      eps ≤ (w e).upper (z (src e))-z (dst e)) :
    BoxedProductive src dst w lo hi Z := by
  refine ⟨hbox,fun e => ?_⟩
  have hh := edge_margin_transfer (w e) (hz _) (hZ _) (hd _) (hd _)
    (hm e).1 (hm e).2
  apply ((w e).productive_iff _ _).mpr
  constructor <;> linarith [hh.1,hh.2]

theorem no_margin_of_grid_unsat {V E : Type*}
    (src dst : E → V) (w : E → Factors) (lo hi : V → ℝ) (D : V → Set ℝ)
    {eps eta : ℝ} (heps : 0 < eps) (heta : eta ≤ eps/4)
    (hb : ∀ v, 0 ≤ lo v ∧ hi v ≤ 1)
    (cover : ∀ v x, x ∈ Set.Icc (lo v) (hi v) →
      ∃ q ∈ D v, q ∈ Set.Icc (lo v) (hi v) ∧ |q-x| ≤ eta)
    (unsat : ¬ ∃ Z, (∀ v, Z v ∈ D v) ∧ BoxedProductive src dst w lo hi Z) :
    ¬ ∃ z : V → ℝ, (∀ v, z v ∈ Set.Icc (lo v) (hi v)) ∧
      ∀ e, eps ≤ z (dst e)-(w e).lower (z (src e)) ∧
        eps ≤ (w e).upper (z (src e))-z (dst e) := by
  classical
  rintro ⟨z,hz,hm⟩
  have hc := fun v => cover v (z v) (hz v)
  choose Z hD hZ using hc
  apply unsat
  refine ⟨Z,hD,margin_boxed_productive src dst w lo hi z Z heps heta ?_ ?_
    (fun v => (hZ v).1) (fun v => (hZ v).2) hm⟩
  · intro v
    exact ⟨(hb v).1.trans (hz v).1,(hz v).2.trans (hb v).2⟩
  · intro v
    exact ⟨(hb v).1.trans (hZ v).1.1,(hZ v).1.2.trans (hb v).2⟩

end ThermoCoreCompatibility.BeyondJunction

