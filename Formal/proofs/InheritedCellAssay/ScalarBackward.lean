import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace InheritedCellAssay.ScalarBackward

/-- Backward equation for the PGF of one cell with independent descendants. -/
def field (b d h : ℝ) : ℝ := (b*h-d)*(1-h)

noncomputable def candidate (m a : ℝ → ℝ) (z t : ℝ) : ℝ :=
  1-m t*(1-z)/(1+a t*(1-z))

theorem candidate_derivative (m a : ℝ → ℝ) (z t b d : ℝ)
    (hm : HasDerivAt m (-(b-d)*m t) t)
    (ha : HasDerivAt a (-b*m t) t)
    (hd : 1+a t*(1-z) ≠ 0) :
    HasDerivAt (candidate m a z) (field b d (candidate m a z t)) t := by
  have h := (((hm.mul_const (1-z)).div
    ((ha.mul_const (1-z)).const_add 1) hd).const_sub 1)
  convert h using 1
  unfold field candidate
  generalize hD : 1+a t*(1-z) = D at hd ⊢
  field_simp [hd]
  ring

theorem field_lipschitz (b d : ℝ) (hb : b ∈ Set.Icc (0 : ℝ) 1)
    (hd : d ∈ Set.Icc (0 : ℝ) 3) :
    LipschitzOnWith 24 (field b d) (Set.Icc (-10 : ℝ) 10) := by
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro x hx y hy
  rw [Real.dist_eq, Real.dist_eq]
  have hxy : -20 ≤ b*(x+y) ∧ b*(x+y) ≤ 20 := by
    constructor <;> nlinarith [mul_nonneg hb.1 (show 0 ≤ x+y+20 by linarith [hx.1,hy.1]),
      mul_nonneg hb.1 (show 0 ≤ 20-x-y by linarith [hx.2,hy.2]), hb.2]
  have hc : |b+d-b*(x+y)| ≤ 24 := by
    rw [abs_le]
    constructor <;> linarith [hb.1,hb.2,hd.1,hd.2,hxy.1,hxy.2]
  have he : field b d x-field b d y = (x-y)*(b+d-b*(x+y)) := by
    unfold field
    ring
  rw [he, abs_mul]
  simpa [mul_comm] using mul_le_mul_of_nonneg_left hc (abs_nonneg (x-y))

/-- Only the scalar branching backward equation and terminal observation enter
    this uniqueness step; no endpoint geometric law is assumed. -/
theorem backward_unique (b d f g : ℝ → ℝ) (a T : ℝ)
    (hb : ∀ t ∈ Set.Ioc a T, b t ∈ Set.Icc (0 : ℝ) 1)
    (hd : ∀ t ∈ Set.Ioc a T, d t ∈ Set.Icc (0 : ℝ) 3)
    (hf : ContinuousOn f (Set.Icc a T))
    (hg : ContinuousOn g (Set.Icc a T))
    (hf' : ∀ t ∈ Set.Ioc a T, HasDerivAt f (field (b t) (d t) (f t)) t)
    (hg' : ∀ t ∈ Set.Ioc a T, HasDerivAt g (field (b t) (d t) (g t)) t)
    (hfb : ∀ t ∈ Set.Ioc a T, f t ∈ Set.Icc (-10 : ℝ) 10)
    (hgb : ∀ t ∈ Set.Ioc a T, g t ∈ Set.Icc (-10 : ℝ) 10)
    (hT : f T = g T) : Set.EqOn f g (Set.Icc a T) := by
  exact ODE_solution_unique_of_mem_Icc_left
    (fun t ht => field_lipschitz (b t) (d t) (hb t ht) (hd t ht))
    hf (fun t ht => (hf' t ht).hasDerivWithinAt) hfb
    hg (fun t ht => (hg' t ht).hasDerivWithinAt) hgb hT

end InheritedCellAssay.ScalarBackward
