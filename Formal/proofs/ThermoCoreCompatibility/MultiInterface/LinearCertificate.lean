import proofs.ThermoCoreCompatibility.MultiInterface.WeightedPair

namespace ThermoCoreCompatibility.MultiInterface

theorem deficit_identities (a b u v ε : ℝ) :
    2*(b*((1-ε*v)-(1-ε*u)^2))-a*((1-ε*u)-(1-ε*v)) =
      ε*((a+4*b)*u-(a+2*b)*v)-2*b*ε^2*u^2 ∧
    a*((1-ε*u)-(1-ε*v))-b*((1-ε*v)-(1-ε*u)^2) =
      ε*((a+b)*v-(a+2*b)*u)+b*ε^2*u^2 := by
  constructor <;> ring

theorem deficit_productive (w : Factors) (u v ε : ℝ) (hε : 0 < ε)
    (hU : 2*w.b*ε*u^2 < (w.a+4*w.b)*u-(w.a+2*w.b)*v)
    (hV : 0 < (w.a+w.b)*v-(w.a+2*w.b)*u) :
    w.Productive (1-ε*u) (1-ε*v) := by
  obtain ⟨e₁,e₂⟩ := deficit_identities w.a w.b u v ε
  have hu := mul_pos hε (sub_pos.mpr hU)
  have hv := mul_pos hε hV
  have hn : 0 ≤ w.b*ε^2*u^2 := mul_nonneg (mul_nonneg w.b_pos.le (sq_nonneg ε)) (sq_nonneg u)
  constructor <;> nlinarith

theorem deficit_box (ell d ε : ℝ) (hd : 0 ≤ d) (hε : 0 ≤ ε)
    (hbound : ε*d ≤ 1-ell) : ell ≤ 1-ε*d ∧ 1-ε*d ≤ 1 := by
  have := mul_nonneg hε hd
  constructor <;> linarith

end ThermoCoreCompatibility.MultiInterface
