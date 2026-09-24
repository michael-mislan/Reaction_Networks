import proofs.CompositionalMemory.TwoSpeciesQuality

namespace CompositionalMemory

theorem two_x_deviation (b : Bool) (u : TwoPoint) (hr : ‖u-twoCenter b‖ ≤ 1/10000) :
    twoCenter b 0-1/10000 ≤ u 0 ∧ u 0 ≤ twoCenter b 0+1/10000 := by
  have hh := abs_le.mp ((two_coordinate_abs_le (u-twoCenter b) 0).trans hr)
  change -(1/10000:ℝ) ≤ u 0-twoCenter b 0 ∧ u 0-twoCenter b 0 ≤ 1/10000 at hh
  constructor <;> linarith only [hh.1,hh.2]

theorem two_high_resident_x_bound (u : TwoPoint) (hr : ‖u-twoCenter true‖ ≤ 1/10000) :
    twoField u 0 ≤ 3/500 := by
  let y := u-twoCenter true
  have h₀ := abs_le.mp ((two_coordinate_abs_le y 0).trans hr)
  have h₁ := abs_le.mp ((two_coordinate_abs_le y 1).trans hr)
  have hrem := (le_abs_self (twoRemainder y 0)).trans
    ((two_coordinate_abs_le (twoRemainder y) 0).trans (two_remainder_bound y))
  have hs := (sq_le_sq₀ (norm_nonneg y) (by norm_num : (0:ℝ) ≤ 1/10000)).mpr hr
  have heq : twoField u 0 = -56*y 0+(3/2)*y 1+twoRemainder y 0 := by
    have hh := congrFun (two_field_expansion true y) 0
    have hy : twoCenter true+y=u := by dsimp [y]; abel
    rw [hy] at hh
    exact hh
  rw [heq]
  nlinarith only [h₀.1,h₁.2,hrem,hs]

/-- X component of the shared-growth, exchanging two-species fluid system. -/
noncomputable def twoCoupledXDrift {k : ℕ} (γ : ℝ) (w : Fin k → Fin k → ℝ)
    (u : Fin k → TwoPoint) (i : Fin k) : ℝ :=
  twoField (u i) 0+(∑ j, w i j*(u j 0-u i 0))-γ*u i 0-
    γ*((∑ j, u j 0)/(k:ℝ))*u i 0

/-- Large total exchange excludes a rare-high stationary state from these wells. -/
theorem two_rare_high_drift_negative {k : ℕ} (γ : ℝ) (hγ : 0 ≤ γ)
    (w : Fin k → Fin k → ℝ) (hw : ∀ i j, 0 ≤ w i j) (hdiag : ∀ i, w i i=0)
    (u : Fin k → TwoPoint) (i : Fin k)
    (hhigh : ‖u i-twoCenter true‖ ≤ 1/10000)
    (hlow : ∀ j, j ≠ i → ‖u j-twoCenter false‖ ≤ 1/10000)
    (hrow : (1:ℝ)/100 ≤ ∑ j, w i j) :
    twoCoupledXDrift γ w u i ≤ -1/200 := by
  classical
  have hi := two_x_deviation true (u i) hhigh
  norm_num [twoCenter] at hi
  have hlowx (j : Fin k) (hj : j ≠ i) : u j 0 ≤ 1+1/10000 := by
    have hh := (two_x_deviation false (u j) (hlow j hj)).2
    simpa only [twoCenter,Bool.false_eq_true,if_false] using hh
  have hpositive (j : Fin k) : 0 ≤ u j 0 := by
    by_cases hj : j=i
    · subst j; linarith only [hi.1]
    · have hh := (two_x_deviation false (u j) (hlow j hj)).1
      norm_num [twoCenter] at hh
      linarith only [hh]
  have hex : (∑ j, w i j*(u j 0-u i 0)) ≤ -(3/2)*(∑ j, w i j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    by_cases hj : j=i
    · subst j; simp [hdiag]
    · have hgap : u j 0-u i 0 ≤ -(3/2) := by linarith only [hlowx j hj,hi.1]
      have hh := mul_le_mul_of_nonneg_left hgap (hw i j)
      nlinarith only [hh]
  have hm : 0 ≤ (∑ j, u j 0)/(k:ℝ) :=
    div_nonneg (Finset.sum_nonneg (fun j _ => hpositive j)) (Nat.cast_nonneg k)
  have hf := two_high_resident_x_bound (u i) hhigh
  have hc : 0 ≤ γ*u i 0 := mul_nonneg hγ (hpositive i)
  have hd : 0 ≤ γ*((∑ j, u j 0)/(k:ℝ))*u i 0 := mul_nonneg (mul_nonneg hγ hm) (hpositive i)
  unfold twoCoupledXDrift
  linarith only [hf,hex,hrow,hc,hd]

theorem two_rare_high_not_stationary {k : ℕ} (γ : ℝ) (hγ : 0 ≤ γ)
    (w : Fin k → Fin k → ℝ) (hw : ∀ i j, 0 ≤ w i j) (hdiag : ∀ i, w i i=0)
    (u : Fin k → TwoPoint) (i : Fin k)
    (hhigh : ‖u i-twoCenter true‖ ≤ 1/10000)
    (hlow : ∀ j, j ≠ i → ‖u j-twoCenter false‖ ≤ 1/10000)
    (hrow : (1:ℝ)/100 ≤ ∑ j, w i j) : twoCoupledXDrift γ w u i ≠ 0 := by
  have hh := two_rare_high_drift_negative γ hγ w hw hdiag u i hhigh hlow hrow
  linarith only [hh]

end CompositionalMemory
