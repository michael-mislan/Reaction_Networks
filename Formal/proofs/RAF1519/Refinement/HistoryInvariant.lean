import proofs.FiniteCopyReactor.HistoryFullLaw

namespace RAF1519.Refinement
noncomputable section
open Classical MeasureTheory ProbabilityTheory FiniteCopyReactor
open scoped ENNReal

theorem successful_history_stays {H : Type*} [MeasurableSpace H]
    (K : Kernel H H) (S : Set H) (hS : MeasurableSet S) (m : ℕ) (h : H) (hh : h ∈ S) :
    successfulHistoryKernel K S hS m h Sᶜ = 0 := by
  induction m generalizing h with
  | zero =>
    rw [successfulHistoryKernel, Kernel.id_apply, Measure.dirac_apply' _ hS.compl]
    simp [hh]
  | succ m ih =>
    rw [successfulHistoryKernel, Kernel.comp_apply' _ _ _ hS.compl, Kernel.restrict_apply]
    calc
      _ = ∫⁻ _ in S, (0 : ℝ≥0∞) ∂K h := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem hS] with y hy
        exact ih y hy
      _ = 0 := by simp

/-- An invariant event of the full, unrestricted history law. Failed transitions remain in K. -/
theorem full_history_invariant_lower {H : Type*} [MeasurableSpace H]
    (K : Kernel H H) (S : Set H) (hS : MeasurableSet S) (e : ℝ) (he : 0 ≤ e)
    (hc : ∀ h ∈ S, ENNReal.ofReal (1-e) ≤ K h S) (m : ℕ) (h : H) (hh : h ∈ S) :
    ENNReal.ofReal (1-(m:ℝ)*e) ≤ fullHistoryKernel K m h S := by
  by_cases he1 : e ≤ 1
  · exact (history_survival_linear K S S hS (fun _ hx => hx) e he1 hc m h hh).trans
      (successful_history_event_lower K S hS m h S hS (successful_history_stays K S hS m h hh))
  · cases m with
    | zero => simp [fullHistoryKernel, Kernel.id_apply, hh]
    | succ m =>
      have hm : (1:ℝ) ≤ (m+1:ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
      have hh0 : 1-((m+1:ℕ):ℝ)*e ≤ 0 := by
        have := mul_le_mul_of_nonneg_right hm he
        linarith
      rw [ENNReal.ofReal_of_nonpos hh0]
      exact bot_le

end
end RAF1519.Refinement
