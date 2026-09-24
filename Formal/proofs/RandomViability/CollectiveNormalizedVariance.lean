import proofs.RandomViability.CollectiveMassCorridor

namespace RandomViability
open Classical RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 80000

def nonfoodConcentrationJump {n : ℕ} (V : NNReal) (N : Molecule n → ℕ)
    (ch : PhysicalCountChannel n) : ℝ :=
  (countNonfoodMass (unboundedPhysicalNext N ch)-countNonfoodMass N)/V

theorem physical_nonfood_normalized_variance {n : ℕ} (hn : 2 ≤ n)
    (c : SourceMoleculeFibreConfig n) (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ) (hM : (countMass N : ℝ) ≤ 11*V)
    (hbasal : ∀ r, (basal r : ℝ) ≤ 1) (hcat : ∀ r z, (cat r z : ℝ) ≤ 16) :
    (∑ ch, unboundedPhysicalRate c V 1 basal cat N ch *
      (nonfoodConcentrationJump V N ch)^2) ≤ (384000+11*(n : ℝ))/V := by
  have hq := physical_nonfood_quadratic_rate_bound c V hV basal cat N
  have hr := unbounded_total_rate_mass_eleven hn c V hV basal cat N hM hbasal hcat
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hb : physicalNonfoodQuadraticRate c V basal cat N ≤
      (384000+11*(n : ℝ))*V := by
    nlinarith [mul_le_mul_of_nonneg_left hM hn0]
  have he : (∑ ch, unboundedPhysicalRate c V 1 basal cat N ch *
      (nonfoodConcentrationJump V N ch)^2) =
      physicalNonfoodQuadraticRate c V basal cat N/(V : ℝ)^2 := by
    simp only [nonfoodConcentrationJump,physicalNonfoodQuadraticRate,div_pow,
      ← mul_div_assoc,Finset.sum_div]
  rw [he]
  calc
    _ ≤ ((384000+11*(n : ℝ))*V)/(V : ℝ)^2 :=
      div_le_div_of_nonneg_right hb (sq_nonneg _)
    _ = _ := by field_simp

theorem physical_nonfood_normalized_jump {n : ℕ} (hn : 4 ≤ n)
    (V : NNReal) (hV : 0 < (V : ℝ)) (N : Molecule n → ℕ)
    (ch : PhysicalCountChannel n) : |nonfoodConcentrationJump V N ch| ≤ (n : ℝ)/V := by
  have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : (countNonfoodMass (unboundedPhysicalNext N ch)-countNonfoodMass N)^2 ≤ (n : ℝ)^2 := by
    rcases ch with (f|x)|(⟨r,d⟩|⟨r,x,d⟩)
    · rw [unbounded_feed_nonfood_jump]
      simpa only [zero_pow (by decide : 2 ≠ 0)] using sq_nonneg (n : ℝ)
    · have h := unbounded_outflow_nonfood_jump_sq N x
      have hl : (molLength x : ℝ) ≤ n := by exact_mod_cast (show molLength x ≤ n by simp [molLength])
      nlinarith
    · have h := unbounded_basal_nonfood_jump_sq N r d
      nlinarith
    · have h := unbounded_catalytic_nonfood_jump_sq N r x d
      nlinarith
  have ha : |countNonfoodMass (unboundedPhysicalNext N ch)-countNonfoodMass N| ≤ (n : ℝ) := by
    apply abs_le.mpr
    constructor <;> nlinarith
  unfold nonfoodConcentrationJump
  rw [abs_div,abs_of_pos hV]
  exact div_le_div_of_nonneg_right ha hV.le

end
end RandomViability
