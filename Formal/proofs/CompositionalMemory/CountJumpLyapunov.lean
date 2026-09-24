import proofs.CompositionalMemory.CountJumpTrajectory
import proofs.CompositionalMemory.JumpLyapunov
import proofs.CompositionalMemory.CountLocalization

namespace CompositionalMemory
open FiniteCopy RandomViability MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable def positiveCountMass {k : ℕ} (s : PositiveCountState k) : ℝ := globalMoleculeCount s.val

theorem positive_count_mass_pos {k : ℕ} (s : PositiveCountState k) : 0 < positiveCountMass s := by
  have hm : (0 : ℝ) < s.val.2 := by exact_mod_cast s.property
  exact hm.trans_le (membrane_le_global_count s.val)

theorem positive_count_generator {k : ℕ} (hk : 1 ≤ k) (γ : ℝ)
    (w : Fin k → Fin k → ℝ) (s : PositiveCountState k) :
    (∑ r, modularRate γ w s.val r * (positiveCountMass (positiveCountNext s r)-positiveCountMass s)) ≤
      33*positiveCountMass s :=
  global_count_growth hk γ w s.val s.property

theorem count_jump_lyapunov_step {k : ℕ} (hk : 1 ≤ k) (γ : ℝ)
    (w : Fin k → Fin k → ℝ) (hγ : 0 ≤ γ) (hw : ∀ i j, 0 ≤ w i j)
    (s : PositiveCountState k) :
    (∫⁻ y, jumpMultiplier (fun r => positiveCountMass (positiveCountNext s r)/positiveCountMass s) 33 y
      ∂jumpStateKernel positiveCountNext (fun x r => modularRate γ w x.val r)
        (fun x r => modular_rate_nonnegative γ w hγ hw x.val r)
        (modular_total_positive hk γ w hγ hw) s) ≤ 1 :=
  jump_lyapunov_step positiveCountNext (fun x r => modularRate γ w x.val r)
    (fun x r => modular_rate_nonnegative γ w hγ hw x.val r)
    (modular_total_positive hk γ w hγ hw) positiveCountMass positive_count_mass_pos 33
    (by norm_num) (positive_count_generator hk γ w) s

/-- The actual unbounded-state rates are bounded on every mass sublevel. -/
theorem count_jump_rates_locally_bounded {k : ℕ} (γ : ℝ)
    (w : Fin k → Fin k → ℝ) (hγ : 0 ≤ γ) (hw : ∀ i j, 0 ≤ w i j) (B : ℕ) :
    ∃ q : NNReal, 1 ≤ (q : ℝ) ∧ ∀ s : PositiveCountState k, positiveCountMass s ≤ B →
      (∑ r, modularRate γ w s.val r) ≤ q := by
  obtain ⟨q,_hq,hq1,hclock⟩ := (killedModularModel γ w hγ hw (countCutoff k B)).exists_clock 1
  refine ⟨q,hq1,?_⟩
  intro s hs
  have hmem : s.val ∈ countCutoff k B := (mem_countCutoff B s.val).mpr ⟨s.property,hs⟩
  exact hclock (some ⟨s.val,hmem⟩)

end CompositionalMemory
