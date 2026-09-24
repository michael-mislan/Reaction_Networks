import proofs.C4Assemblies.Bounds

namespace C4Assemblies
noncomputable section
open Set
variable {ι : Type*} [Fintype ι]

theorem diffusion_sub_const (k : ι → ι → ℝ) (z : ι → ℝ) (a : ℝ) (i : ι) :
    diffusion k (fun j => z j-a) i = diffusion k z i := by
  unfold diffusion
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  ring

/-- Exponential material contraction in the maximum norm, independent of graph strength. -/
theorem material_decay (k : ι → ι → ℝ) (hk : ∀ i j, 0 ≤ k i j)
    (z : ℝ → ι → ℝ) (delta : ℝ)
    (hz : ∀ t, 0 ≤ t → ∀ i,
      HasDerivAt (fun s => z s i) (1-z t i+diffusion k (z t) i) t)
    (h0 : ∀ i, |z 0 i-1| ≤ delta) :
    ∀ t, 0 ≤ t → ∀ i, |z t i-1| ≤ delta*Real.exp (-t) := by
  intro T hT
  let w : ℝ → ι → ℝ := fun t i => Real.exp t*(z t i-1)
  have hw : ∀ t ∈ Icc 0 T, ∀ i,
      HasDerivAt (fun s => w s i) (diffusion k (w t) i) t := by
    intro t ht i
    have hh := (Real.hasDerivAt_exp t).mul ((hz t ht.1 i).sub_const 1)
    dsimp [w]
    rw [diffusion_mul, diffusion_sub_const]
    convert hh using 1
    ring
  have hw0 : ∀ i, -delta ≤ w 0 i ∧ w 0 i ≤ delta := by
    intro i
    simpa [w] using abs_le.mp (h0 i)
  have hlo := diffusion_lower_bound k hk w (fun t => diffusion k (w t)) (-delta) T hT
    hw (fun i => (hw0 i).1) (fun _ _ _ => le_rfl)
  have hhi := finite_upper_barrier w (fun t => diffusion k (w t)) delta T hT
    hw (fun i => (hw0 i).2)
    (fun t _ i _ hm => diffusion_at_max k hk (w t) i hm)
  intro i
  have hl := mul_le_mul_of_nonneg_right (hlo i) (Real.exp_pos (-T)).le
  have hu := mul_le_mul_of_nonneg_right (hhi i) (Real.exp_pos (-T)).le
  have he : Real.exp T*Real.exp (-T) = 1 := by rw [← Real.exp_add]; simp
  have hprod : w T i*Real.exp (-T) = z T i-1 := by
    dsimp [w]
    calc
      Real.exp T*(z T i-1)*Real.exp (-T) =
          (Real.exp T*Real.exp (-T))*(z T i-1) := by ring
      _ = z T i-1 := by rw [he]; ring
  rw [hprod] at hl hu
  exact abs_le.mpr ⟨by nlinarith,hu⟩

theorem corridor_from_decay (z : ℝ → ℝ)
    (hz : ∀ t, 0 ≤ t → |z t-1| ≤ (1/10)*Real.exp (-t)) :
    (∀ t, 0 ≤ t → 9/10 ≤ z t ∧ z t ≤ 11/10) ∧
    (∀ t, 3 ≤ t → 159/160 ≤ z t ∧ z t ≤ 161/160) := by
  constructor
  · intro t ht
    have he : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    obtain ⟨hl,hu⟩ := abs_le.mp (hz t ht)
    constructor <;> linarith
  · intro t ht
    have he3 : 16 ≤ Real.exp 3 := by
      have hh := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 3) 5
      norm_num [Finset.sum_range_succ] at hh
      linarith
    have he : Real.exp (-t) ≤ 1/16 := by
      rw [Real.exp_neg, inv_eq_one_div]
      apply (div_le_iff₀ (Real.exp_pos t)).2
      have hh := he3.trans (Real.exp_le_exp.mpr ht)
      linarith
    obtain ⟨hl,hu⟩ := abs_le.mp (hz t (by linarith))
    constructor <;> linarith

end
end C4Assemblies
