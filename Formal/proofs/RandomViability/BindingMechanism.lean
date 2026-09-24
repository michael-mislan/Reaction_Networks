import proofs.RandomViability.BindingGrowthWeights

namespace RandomViability.Binding
noncomputable section

def physicalMass (u w x c₁ c₂ z : ℝ) : ℝ := 2*u+2*w+4*x+6*c₁+8*c₂+8*z
def productMass (x c₁ c₂ z : ℝ) : ℝ := 4*x+4*c₁+4*c₂+8*z

/-- Signed internal reaction fluxes in the six-species ODE, k=1/K. -/
def basalFlux (u w x eps k : ℝ) := eps*(u*w-k*x)
def bindFirst (u x c₁ : ℝ) := 20*(x*u-c₁)
def bindSecond (w c₁ c₂ : ℝ) := 20*(c₁*w-c₂)
def conversion (c₂ z k : ℝ) := 20*(c₂-k*z)
def release (x z r : ℝ) := r*(z-x*x)

/-- Exact physical mass balance, including feed and every complex washout. -/
theorem mass_balance (u w x c₁ c₂ z f₀ f₁ f₂ f₃ f₄ : ℝ) :
    physicalMass (1-u-f₀-f₁) (1-w-f₀-f₂)
      (-x+f₀-f₁+2*f₄) (-c₁+f₁-f₂) (-c₂+f₂-f₃) (-z+f₃-f₄) =
    4-physicalMass u w x c₁ c₂ z := by dsimp [physicalMass]; ring

/-- Binding food does not count as new covalent production. -/
theorem product_balance (x c₁ c₂ z f₀ f₁ f₂ f₃ f₄ : ℝ) :
    productMass (-x+f₀-f₁+2*f₄) (-c₁+f₁-f₂) (-c₂+f₂-f₃) (-z+f₃-f₄) =
      4*f₀+4*f₃-productMass x c₁ c₂ z := by dsimp [productMass]; ring

theorem weighted_drift_identity (u w x c₁ c₂ z eps k r : ℝ) :
    weighted (-x+basalFlux u w x eps k-bindFirst u x c₁+2*release x z r)
      (-c₁+bindFirst u x c₁-bindSecond w c₁ c₂)
      (-c₂+bindSecond w c₁ c₂-conversion c₂ z k)
      (-z+conversion c₂ z k-release x z r) =
    eps*u*w-eps*k*x+(5/2*u-1)*x+(-29/8+11/2*w)*c₁+
      11/10*c₂+(r/5-9/5-8*k)*z-r/5*x*x := by
  dsimp [weighted,basalFlux,bindFirst,bindSecond,conversion,release]
  ring

/-- All five reversible pairs balance at (1,1,K,K,K,K^2). -/
theorem equilibrium_fluxes (K eps r : ℝ) (hK : K ≠ 0) :
    basalFlux 1 1 K eps (1/K) = 0 ∧ bindFirst 1 K K = 0 ∧
    bindSecond 1 K K = 0 ∧ conversion K (K^2) (1/K) = 0 ∧
    release K (K^2) r = 0 := by
  dsimp [basalFlux,bindFirst,bindSecond,conversion,release]
  field_simp
  simp

/-- Direct full-mechanism growth in a food corridor, retaining rebinding and
basal loss. k=1/K. The small-density hypothesis is explicit. -/
theorem corridor_growth (u w x c₁ c₂ z eps k r : ℝ)
    (hu : 4/5 ≤ u) (hw : 4/5 ≤ w)
    (hx : 0 ≤ x) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hz : 0 ≤ z)
    (heps : 0 ≤ eps) (hepsSmall : eps ≤ 1/1000000)
    (hk : 0 ≤ k) (hk1 : k ≤ 1/8) (hr : 18 ≤ r) (hr1 : r ≤ 22)
    (hsmall : x ≤ 1/1000) :
    (39/100)*weighted x c₁ c₂ z+(16/25)*eps ≤
    eps*u*w-eps*k*x+(5/2*u-1)*x+(-29/8+11/2*w)*c₁+
      11/10*c₂+(r/5-9/5-8*k)*z-r/5*x*x := by
  have hp : (16/25:ℝ) ≤ u*w := by
    have h := mul_le_mul hu hw (by norm_num : (0:ℝ) ≤ 4/5) (by linarith : 0 ≤ u)
    norm_num at h
    exact h
  have hb := mul_le_mul_of_nonneg_left hp heps
  have hxu := mul_le_mul_of_nonneg_right hu hx
  have hcw := mul_le_mul_of_nonneg_right hw hc₁
  have hzr := mul_le_mul_of_nonneg_right hr hz
  have hzk := mul_le_mul_of_nonneg_right hk1 hz
  have he : eps*k ≤ 1/8000000 :=
    (mul_le_mul hepsSmall hk1 hk (by norm_num)).trans (by norm_num)
  have hex := mul_le_mul_of_nonneg_right he hx
  have hrx : r*x ≤ 22/1000 :=
    (mul_le_mul hr1 hsmall hx (by norm_num)).trans (by norm_num)
  have hrxx := mul_le_mul_of_nonneg_right hrx hx
  dsimp [weighted]
  nlinarith

end
end RandomViability.Binding
