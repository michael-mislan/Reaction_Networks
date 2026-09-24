import proofs.C4Assemblies.Comparison
import proofs.ProductiveRecovery.StrongScalar

namespace C4Assemblies
noncomputable section
open Set
variable {ι : Type*} [Fintype ι]

/-- Recovery from a common retained floor using growth only at minimizing vertices. -/
theorem assembly_scheduled_recovery (y v : ℝ → ι → ℝ)
    (hd : ∀ t, 0 ≤ t → ∀ i, HasDerivAt (fun s => y s i) (v t i) t)
    (b0 D : ℝ) (hb0pos : 0 < b0) (h0 : ∀ i, b0 ≤ y 0 i)
    (hD : 0 ≤ D) (hexpD : (1/20)/b0 ≤ Real.exp ((3/5)*D))
    (hg : ∀ t, 0 ≤ t → ∀ i, 0 ≤ y t i → y t i ≤ 1/20 →
      (∀ j, y t i ≤ y t j) → (2/3)*y t i ≤ v t i) :
    ∀ T, D ≤ T → ∀ i, 1/20 ≤ y T i := by
  intro T hT
  let b : ℝ → ℝ := fun s => (1/20)*Real.exp ((3/5)*(s-T))
  have hbpos (s : ℝ) : 0 < b s := by dsimp [b]; positivity
  have hbder (s : ℝ) : HasDerivAt b ((3/5)*b s) s := by
    convert ((((hasDerivAt_id s).sub_const T).const_mul (3/5)).exp).const_mul (1/20) using 1
    dsimp [b]
    ring
  have hb0 : b 0 ≤ b0 := by
    have he : (1/20)/b0 ≤ Real.exp ((3/5)*T) :=
      hexpD.trans (Real.exp_le_exp.mpr (by linarith))
    have hh : (1/20) / Real.exp ((3/5)*T) ≤ b0 := by
      apply (div_le_iff₀ (Real.exp_pos _)).2
      have hh := (div_le_iff₀ hb0pos).1 he
      nlinarith
    have heq : b 0 = (1/20) / Real.exp ((3/5)*T) := by
      dsimp [b]
      rw [show (3/5:ℝ)*(0-T) = -((3/5)*T) by ring, Real.exp_neg]
      rfl
    rw [heq]
    exact hh
  have hf := finite_strict_lower_barrier (fun t i => y t i-b t)
    (fun t i => v t i-(3/5)*b t) 0 T
    (fun t ht i => (hd t ht.1 i).sub (hbder t))
    (fun i => sub_nonneg.mpr (hb0.trans (h0 i)))
    (fun t ht hall i hz => by
      have heq : y t i = b t := sub_eq_zero.mp hz
      have hmin : ∀ j, y t i ≤ y t j := by
        intro j
        rw [heq]
        exact sub_nonneg.mp (hall j)
      have hb1 : b t ≤ 1/20 := by
        have h := Real.exp_le_one_iff.mpr (show (3/5:ℝ)*(t-T) ≤ 0 by nlinarith [ht.2])
        dsimp [b]
        linarith
      have hh := hg t ht.1 i (by rw [heq]; exact (hbpos t).le)
        (by rw [heq]; exact hb1) hmin
      have hp := hbpos t
      rw [heq] at hh
      linarith)
    T ⟨hD.trans hT,le_rfl⟩
  intro i
  have hh := hf i
  change 0 ≤ y T i-b T at hh
  have hbT : b T = 1/20 := by simp [b]
  rw [hbT] at hh
  linarith

end
end C4Assemblies
