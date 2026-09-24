import proofs.CompositionalMemory.GenericReactionEnergy

namespace CompositionalMemory
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

private theorem bilinear_cauchy_positive (Q : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hsym : ∀ x y,Q x y=Q y x) (hpos : ∀ x,0 ≤ Q x x)
    (x y : V) (hx : 0 < Q x x) : (Q x y)^2 ≤ Q x x*Q y y := by
  have hh := hpos ((Q x x) • y-(Q x y) • x)
  have he : Q ((Q x x) • y-(Q x y) • x) ((Q x x) • y-(Q x y) • x)=
      Q x x*(Q x x*Q y y-(Q x y)^2) := by
    simp only [map_sub,map_smul,LinearMap.sub_apply,LinearMap.smul_apply,smul_eq_mul]
    rw [hsym y x]
    ring
  rw [he] at hh
  exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hx).mp hh)

theorem bilinear_cauchy_sq (Q : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hsym : ∀ x y,Q x y=Q y x) (hpos : ∀ x,0 ≤ Q x x) (x y : V) :
    (Q x y)^2 ≤ Q x x*Q y y := by
  by_cases hx : 0 < Q x x
  · exact bilinear_cauchy_positive Q hsym hpos x y hx
  by_cases hy : 0 < Q y y
  · simpa only [hsym y x,mul_comm] using bilinear_cauchy_positive Q hsym hpos y x hy
  have hx0 : Q x x=0 := le_antisymm (le_of_not_gt hx) (hpos x)
  have hy0 : Q y y=0 := le_antisymm (le_of_not_gt hy) (hpos y)
  have hp := hpos (x+y)
  have hm := hpos (x-y)
  simp only [map_add,map_sub,LinearMap.add_apply,LinearMap.sub_apply,hx0,hy0,hsym y x] at hp hm
  have hxy : Q x y=0 := by linarith only [hp,hm]
  rw [hxy,hx0]
  simp

/-- A jump bound that retains the individual jump energy, needed when summing
the second jump moment against all source propensities. -/
theorem quadratic_increment_squared_bound (cross q x h volume : ℝ)
    (hq : 0 ≤ q) (hx : 0 ≤ x) (hh : 0 ≤ h) (hv : 0 < volume)
    (hc : cross^2 ≤ x^2*q) (hqh : q ≤ h^2) :
    ((2/volume)*cross+(1/volume^2)*q)^2 ≤
      q*(2*x/volume+h/volume^2)^2 := by
  have hs := Real.sq_sqrt hq
  have hs0 := Real.sqrt_nonneg q
  have hcabs : |cross| ≤ x*Real.sqrt q := by
    apply (sq_le_sq₀ (abs_nonneg cross) (mul_nonneg hx hs0)).mp
    simpa only [sq_abs,mul_pow,hs] using hc
  have hsh : Real.sqrt q ≤ h := by
    exact (sq_le_sq₀ hs0 hh).mp (by simpa only [hs] using hqh)
  have hqsh : q ≤ h*Real.sqrt q := by nlinarith only [mul_le_mul_of_nonneg_right hsh hs0,hs]
  have hbound : |(2/volume)*cross+(1/volume^2)*q| ≤
      Real.sqrt q*(2*x/volume+h/volume^2) := by
    calc
      _ ≤ |(2/volume)*cross|+|(1/volume^2)*q| := abs_add_le _ _
      _ = (2/volume)*|cross|+(1/volume^2)*q := by
        rw [abs_mul,abs_of_nonneg (by positivity : 0 ≤ 2/volume),
          abs_of_nonneg (by positivity : 0 ≤ (1/volume^2)*q)]
      _ ≤ (2/volume)*(x*Real.sqrt q)+(1/volume^2)*(h*Real.sqrt q) :=
        add_le_add (mul_le_mul_of_nonneg_left hcabs (by positivity))
          (mul_le_mul_of_nonneg_left hqsh (by positivity))
      _ = _ := by ring
  have hb := pow_le_pow_left₀ (abs_nonneg _) hbound 2
  simpa only [sq_abs,mul_pow,hs] using hb

end CompositionalMemory
