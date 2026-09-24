import proofs.CoreCouplingGlobal.ScalarBarrier

namespace ProductiveRecovery
noncomputable section
open Set

theorem recovered_floor_invariant (y v : ℝ → ℝ)
    (hd : ∀ t, 0 ≤ t → HasDerivAt y (v t) t)
    (hn : ∀ t, 0 ≤ t → 0 ≤ y t) (h0 : 1/2500 ≤ y 0)
    (hg : ∀ t, 0 ≤ t → y t ≤ 1/2500 → (2/3)*y t ≤ v t) :
    ∀ t, 0 ≤ t → 1/2500 ≤ y t := by
  apply CoreCouplingGlobal.scalar_lower_barrier y v (1/2500) hd h0
  intro t ht hy
  have h := hg t ht hy
  linarith [hn t ht]

/-- A strict exponential fence proves the scheduled endpoint directly.
The rate 3/5 leaves slack below the available source rate 2/3. -/
theorem guarded_scheduled_recovery (y v : ℝ → ℝ)
    (hd : ∀ t, 0 ≤ t → HasDerivAt y (v t) t)
    (h0 : 49/1000000 ≤ y 0)
    (hg : ∀ t, 0 ≤ t → 0 ≤ y t → y t ≤ 1/2500 → (2/3)*y t ≤ v t) :
    ∀ T, 4 ≤ T → 1/2500 ≤ y T := by
  intro T hT
  let b : ℝ → ℝ := fun s => (1/2500)*Real.exp ((3/5)*(s-T))
  have hbpos (s : ℝ) : 0 < b s := by dsimp [b]; positivity
  have hbder (s : ℝ) : HasDerivAt b ((3/5)*b s) s := by
    convert ((((hasDerivAt_id s).sub_const T).const_mul (3/5)).exp).const_mul (1/2500) using 1
    dsimp [b]
    ring
  have hexp : 400/49 ≤ Real.exp (12/5) := by
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 12/5) 4
    norm_num [Finset.sum_range_succ] at h
    linarith
  have hTexp : Real.exp (12/5) ≤ Real.exp ((3/5)*T) :=
    Real.exp_le_exp.mpr (by linarith)
  have hb0 : b 0 ≤ y 0 := by
    have he : 400/49 ≤ Real.exp ((3/5)*T) := hexp.trans hTexp
    have hh : (1/2500) / Real.exp ((3/5)*T) ≤ 49/1000000 := by
      apply (div_le_iff₀ (Real.exp_pos _)).2
      linarith
    have heq : b 0 = (1/2500) / Real.exp ((3/5)*T) := by
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
      have hb1 : b s ≤ 1/2500 := by
        have h := Real.exp_le_one_iff.mpr (show (3/5:ℝ)*(s-T) ≤ 0 by nlinarith [hs.2])
        dsimp [b]
        linarith
      have hh := hg s hs.1 (by rw [hy]; exact (hbpos s).le) (by rw [hy]; exact hb1)
      have hp := hbpos s
      rw [hy] at hh
      linarith)
    (show T ∈ Icc 0 T from ⟨by linarith,le_rfl⟩)
  have hbT : b T = 1/2500 := by simp [b]
  dsimp only at hbound
  rw [hbT] at hbound
  linarith

end
end ProductiveRecovery
