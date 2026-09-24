import proofs.ThermoCoreCompatibility.MultiInterface.WeightedPair

namespace ThermoCoreCompatibility.MultiInterface

theorem relative_box_iff (p q ρ : ℝ) (hp : 0 < p) (hq : 0 < q) (hρ : 0 ≤ ρ) :
    (∀ u v : ℝ, 1-ρ ≤ u → u ≤ 1+ρ → 1-ρ ≤ v → v ≤ 1+ρ →
      0 < 2*(v*q)-u*p ∧ 0 < u*p-v*q) ↔
    0 < 2*q-p-ρ*(2*q+p) ∧ 0 < p-q-ρ*(p+q) := by
  constructor
  · intro h
    have hu := (h (1+ρ) (1-ρ) (by linarith) (by rfl) (by rfl) (by linarith)).1
    have hv := (h (1-ρ) (1+ρ) (by rfl) (by linarith) (by linarith) (by rfl)).2
    constructor <;> nlinarith
  · rintro ⟨hu,hv⟩ u v hul huh hvl hvh
    have pu := mul_le_mul_of_nonneg_right huh hp.le
    have pl := mul_le_mul_of_nonneg_right hul hp.le
    have qu := mul_le_mul_of_nonneg_right hvh hq.le
    have ql := mul_le_mul_of_nonneg_right hvl hq.le
    constructor <;> nlinarith

theorem relative_radius_iff (p q ρ : ℝ) (hp : 0 < p) (hq : 0 < q) :
    (0 < 2*q-p-ρ*(2*q+p) ∧ 0 < p-q-ρ*(p+q)) ↔
    ρ < (2*q-p)/(2*q+p) ∧ ρ < (p-q)/(p+q) := by
  have hd : 0 < 2*q+p := by linarith
  have he : 0 < p+q := by linarith
  rw [lt_div_iff₀ hd, lt_div_iff₀ he]
  constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith

end ThermoCoreCompatibility.MultiInterface
