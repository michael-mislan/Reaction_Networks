import proofs.OscillatoryCores.ShortFlow
import proofs.BressanJump.GlobalLipschitzFlow

namespace OscillatoryCores

open Set
open scoped NNReal

/-- Bounded fields with a Lipschitz derivative have C1 endpoint maps on
arbitrary nonnegative time intervals, by finite composition of genuine short flows. -/
theorem global_flow_contDiff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : E → E) (D : E → E →L[ℝ] E) (K L M : ℝ≥0)
    (hf : LipschitzWith K f) (hD : LipschitzWith L D)
    (hderiv : ∀ x, HasFDerivAt f (D x) x) (hbound : ∀ x, ‖f x‖ ≤ M)
    (hc : ContDiff ℝ 1 f) (T : ℝ≥0) :
    ContDiff ℝ 1 (BressanJump.globalLipschitzFlow f hc M K hbound hf T) := by
  let Φ := BressanJump.globalLipschitzFlow f hc M K hbound hf
  have hΦ0 (x : E) : Φ 0 x = x := BressanJump.globalLipschitzFlow_zero ..
  have hΦd (x : E) : ∀ t, HasDerivAt (fun s => Φ s x) (f (Φ t x)) t :=
    BressanJump.globalLipschitzFlow_isIntegralCurve f hc M K hbound hf x
  have hΦadd (s t : ℝ) (x : E) : Φ s (Φ t x) = Φ (t+s) x :=
    BressanJump.globalLipschitzFlow_add ..
  obtain ⟨n, hn⟩ := exists_nat_gt (2*K*T)
  have hnpos : (0 : ℝ≥0) < n := lt_of_le_of_lt (by positivity) hn
  let δ : ℝ≥0 := T/n
  have hshort : (2*K)*δ ≤ 1 := by
    dsimp [δ]
    rw [← mul_div_assoc]
    exact (div_le_one hnpos).mpr hn.le
  obtain ⟨X,hzero,hflow,hcX⟩ := exists_short_c1_flow f D δ K L M hf hD hderiv hbound hshort
  have heq (x : E) : X x δ = Φ δ x := by
    have huniq : EqOn (X x) (fun t => Φ t x) (Icc (0 : ℝ) δ) := by
      apply ODE_solution_unique_of_mem_Icc_right (v := fun _ => f)
        (s := fun _ => univ) (K := K)
      · intro _ _; exact hf.lipschitzOnWith
      · exact HasDerivWithinAt.continuousOn (hflow x)
      · intro t ht
        exact (hflow x t ⟨ht.1,ht.2.le⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht)
      · intros; exact mem_univ _
      · exact (continuous_iff_continuousAt.mpr (fun t => (hΦd x t).continuousAt)).continuousOn
      · intro t _; exact (hΦd x t).hasDerivWithinAt
      · intros; exact mem_univ _
      · rw [hzero, hΦ0]
    exact huniq ⟨by positivity,le_rfl⟩
  have hs : ContDiff ℝ 1 (Φ δ) := by
    convert hcX δ ⟨by positivity,le_rfl⟩ using 1
    exact (funext heq).symm
  have hi (m : ℕ) : ContDiff ℝ 1 (Φ ((m : ℝ)*δ)) := by
    induction m with
    | zero =>
      have hz : Φ 0 = (id : E → E) := funext hΦ0
      simpa only [Nat.cast_zero,zero_mul,hz] using (contDiff_id : ContDiff ℝ 1 (id : E → E))
    | succ m ih =>
      have hh : Φ (((m+1 : ℕ) : ℝ)*δ) = (Φ δ) ∘ (Φ ((m : ℝ)*δ)) := by
        funext x
        simp only [Function.comp_apply,hΦadd,Nat.cast_add,Nat.cast_one,add_mul,one_mul]
      rw [hh]
      exact hs.comp ih
  have htime : (n : ℝ)*(δ : ℝ) = T := by
    have hnreal : (n : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hnpos)
    simp only [δ,NNReal.coe_div,NNReal.coe_natCast]
    field_simp
  simpa only [htime,Φ] using hi n

end OscillatoryCores
