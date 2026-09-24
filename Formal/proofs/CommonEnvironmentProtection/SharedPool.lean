import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Convert

/-! Exact algebra for the maintained affine shared-pool model. These theorems
do not assert that any published biochemical mechanism has affine kinetics. -/
namespace CommonEnvironmentProtection

noncomputable section

def branch (C D r : ℝ) : ℝ := C * r - D * (1 - r)
def regeneration (A B r : ℝ) : ℝ := A * (1 - r) - B * r
def equilibrium (A B C D m : ℝ) : ℝ := (A + D - m) / (A + B + C + D)

theorem service_iff (C D q r : ℝ) (h : 0 < C + D) :
    q ≤ branch C D r ↔ (q + D) / (C + D) ≤ r := by
  rw [div_le_iff₀ h]
  unfold branch
  constructor <;> intro hq <;> nlinarith

theorem balance_iff (A B C D m r : ℝ) (hK : 0 < A + B + C + D) :
    regeneration A B r - branch C D r - m = 0 ↔
      r = equilibrium A B C D m := by
  unfold regeneration branch equilibrium
  rw [eq_div_iff (ne_of_gt hK)]
  constructor <;> intro hr <;> nlinarith

theorem joint_equilibrium_iff
    (A B C₁ D₁ C₂ D₂ m q₁ q₂ lo hi : ℝ)
    (hK : 0 < A + B + (C₁ + C₂) + (D₁ + D₂))
    (h₁ : 0 < C₁ + D₁) (h₂ : 0 < C₂ + D₂) :
    (∃ r : ℝ, lo ≤ r ∧ r ≤ hi ∧
      regeneration A B r - branch C₁ D₁ r - branch C₂ D₂ r - m = 0 ∧
      q₁ ≤ branch C₁ D₁ r ∧ q₂ ≤ branch C₂ D₂ r) ↔
    max lo (max ((q₁ + D₁) / (C₁ + D₁)) ((q₂ + D₂) / (C₂ + D₂))) ≤
      equilibrium A B (C₁ + C₂) (D₁ + D₂) m ∧
      equilibrium A B (C₁ + C₂) (D₁ + D₂) m ≤ hi := by
  have hb (r : ℝ) :
      regeneration A B r - branch C₁ D₁ r - branch C₂ D₂ r - m = 0 ↔
      r = equilibrium A B (C₁ + C₂) (D₁ + D₂) m := by
    convert balance_iff A B (C₁ + C₂) (D₁ + D₂) m r hK using 1
    unfold branch
    ring_nf
  simp only [hb, service_iff C₁ D₁ q₁ _ h₁, service_iff C₂ D₂ q₂ _ h₂,
    max_le_iff]
  constructor
  · rintro ⟨r, hl, hu, rfl, hq₁, hq₂⟩
    exact ⟨⟨hl, hq₁, hq₂⟩, hu⟩
  · rintro ⟨⟨hl, hq₁, hq₂⟩, hu⟩
    exact ⟨_, hl, hu, rfl, hq₁, hq₂⟩

theorem repair_lower_iff (A B C D m s L : ℝ)
    (hK : 0 < s*A + s*B + C + D) (hG : 0 < regeneration A B L) :
    L ≤ equilibrium (s*A) (s*B) C D m ↔
      (branch C D L + m) / regeneration A B L ≤ s := by
  unfold equilibrium
  rw [le_div_iff₀ hK, div_le_iff₀ hG]
  unfold branch regeneration
  constructor <;> intro h <;> nlinarith

theorem no_finite_repair (A B C D m s L r : ℝ)
    (hs : 0 < s) (hAB : 0 ≤ A + B) (hCD : 0 ≤ C + D)
    (hG : regeneration A B L ≤ 0) (hN : 0 < branch C D L + m)
    (hr : L ≤ r) :
    regeneration (s*A) (s*B) r - branch C D r - m ≠ 0 := by
  have hgr : regeneration A B r ≤ regeneration A B L := by
    unfold regeneration
    nlinarith [mul_nonneg hAB (sub_nonneg.mpr hr)]
  have hfr : branch C D L ≤ branch C D r := by
    unfold branch
    nlinarith [mul_nonneg hCD (sub_nonneg.mpr hr)]
  have hscale : regeneration (s*A) (s*B) r = s * regeneration A B r := by
    unfold regeneration
    ring
  rw [hscale]
  have : s * regeneration A B r ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hs.le (hgr.trans hG)
  linarith

theorem synthetic_fixture :
    equilibrium 6 (1/100) 1 (1/100) 0 = 601/702 ∧
    equilibrium 6 (1/100) 2 (2/100) 0 = 602/803 ∧
    branch 1 (1/100) (601/702) > 4/5 ∧
    branch 1 (1/100) (602/803) < 4/5 ∧
    equilibrium ((16160/11919)*6) ((16160/11919)*(1/100)) 2 (2/100) 0 = 81/101 ∧
    branch 1 (1/100) (81/101) = 4/5 := by
  norm_num [equilibrium, branch]

end
end CommonEnvironmentProtection
