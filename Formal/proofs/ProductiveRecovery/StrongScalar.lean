import proofs.ProductiveRecovery.ScalarRecovery
namespace ProductiveRecovery
noncomputable section
open Set
theorem strong_scheduled_recovery (y v : ℝ → ℝ)
    (hd : ∀ t, 0 ≤ t → HasDerivAt y (v t) t)
    (b0 D : ℝ) (hb0pos : 0 < b0) (h0 : b0 ≤ y 0)
    (hD : 0 ≤ D) (hexpD : (1/20)/b0 ≤ Real.exp ((3/5)*D))
    (hg : ∀ t, 0 ≤ t → 0 ≤ y t → y t ≤ 1/20 → (2/3)*y t ≤ v t) :
    ∀ T, D ≤ T → 1/20 ≤ y T := by
  intro T hT
  let b : ℝ → ℝ := fun s => (1/20)*Real.exp ((3/5)*(s-T))
  have hbpos (s : ℝ) : 0 < b s := by dsimp [b]; positivity
  have hbder (s : ℝ) : HasDerivAt b ((3/5)*b s) s := by
    convert ((((hasDerivAt_id s).sub_const T).const_mul (3/5)).exp).const_mul (1/20) using 1
    dsimp [b]
    ring
  have hTexp : Real.exp ((3/5)*D) ≤ Real.exp ((3/5)*T) :=
    Real.exp_le_exp.mpr (by linarith)
  have hb0 : b 0 ≤ y 0 := by
    have he : (1/20)/b0 ≤ Real.exp ((3/5)*T) := hexpD.trans hTexp
    have hh : (1/20) / Real.exp ((3/5)*T) ≤ b0 := by
      apply (div_le_iff₀ (Real.exp_pos _)).2
      have hh := (div_le_iff₀ hb0pos).1 he
      nlinarith
    have heq : b 0 = (1/20) / Real.exp ((3/5)*T) := by
      dsimp [b]
      rw [show (3/5:ℝ)*(0-T) = -((3/5)*T) by ring, Real.exp_neg]
      rfl
    rw [heq]
    exact hh.trans h0
  have hbound := image_le_of_deriv_right_lt_deriv_boundary
    (f := fun s => -y s) (f' := fun s => -v s) (a := 0) (b := T)
    (fun s hs => (hd s hs.1).neg.continuousAt.continuousWithinAt)
    (fun s hs => (hd s hs.1).neg.hasDerivWithinAt)
    (B := fun s => -b s) (B' := fun s => -((3/5)*b s))
    (by linarith : -y 0 ≤ -b 0) (fun s => (hbder s).neg)
    (fun s hs heq => by
      have hy : y s = b s := by linarith
      have hb1 : b s ≤ 1/20 := by
        have h := Real.exp_le_one_iff.mpr (show (3/5:ℝ)*(s-T) ≤ 0 by nlinarith [hs.2])
        dsimp [b]
        linarith
      have hh := hg s hs.1 (by rw [hy]; exact (hbpos s).le) (by rw [hy]; exact hb1)
      have hp := hbpos s
      rw [hy] at hh
      linarith)
    (show T ∈ Icc 0 T from ⟨by linarith,le_rfl⟩)
  have hbT : b T = 1/20 := by simp [b]
  dsimp only at hbound
  rw [hbT] at hbound
  linarith

end
end ProductiveRecovery
