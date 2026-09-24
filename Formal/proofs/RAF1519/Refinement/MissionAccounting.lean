import proofs.RAF1519.Refinement.RelaxedInstance
import proofs.RAF1519.Reservoir.ObservableRecovery

namespace RAF1519.Refinement.Relaxed
noncomputable section

theorem mission_size (A B V δ : ℝ) (hA : 0 < A) (hB : 0 < B) (hδ : 0 < δ)
    (hV : B*Real.log (A/δ) ≤ V) : A*Real.exp (-V/B) ≤ δ := by
  have he : -V/B ≤ Real.log (δ/A) := by
    rw [Real.log_div hδ.ne' hA.ne']
    have hh : Real.log (A/δ) ≤ V/B := (le_div_iff₀ hB).mpr (by simpa only [mul_comm] using hV)
    rw [Real.log_div hA.ne' hδ.ne'] at hh
    simpa only [neg_sub,neg_div] using neg_le_neg hh
  have hx := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) hA.le
  rw [Real.exp_log (div_pos hδ hA)] at hx
  have hi : A*(δ/A)=δ := by field_simp
  rwa [hi] at hx

theorem successful_cycle_yield {n : ℕ} (V : ℕ) (out : CycleOutput n)
    (hs : cycleOutputSuccess V out) (i : Fin n) :
    out.2 i 2+out.2 i 3 ≤ 560*out.2 i 0 ∧
    out.2 i 2+out.2 i 3 ≤ 10800*out.2 i 1 := by
  obtain ⟨_,hI,hX,hU,hW,_⟩ := hs i
  have hi : (V:ℝ)/56 ≤ out.2 i 0 :=
    (Nat.le_ceil _).trans (by exact_mod_cast hI)
  have hx : (V:ℝ)/1080 ≤ out.2 i 1 :=
    (Nat.le_ceil _).trans (by exact_mod_cast hX)
  have hu : (out.2 i 2:ℝ) ≤ 5*V := by exact_mod_cast hU
  have hw : (out.2 i 3:ℝ) ≤ 5*V := by exact_mod_cast hW
  constructor
  · have h : (out.2 i 2:ℝ)+out.2 i 3 ≤ 560*out.2 i 0 := by linarith
    exact_mod_cast h
  · have h : (out.2 i 2:ℝ)+out.2 i 3 ≤ 10800*out.2 i 1 := by linarith
    exact_mod_cast h

end
end RAF1519.Refinement.Relaxed
