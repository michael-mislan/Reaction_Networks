import proofs.SerialTransferSelection.ManyCycleMeasured

namespace SerialTransferSelection
open ResourceLimitedCompetition HeritableCompositions FiniteCopy

theorem positive_count_log_odds_ceiling (H L M : ℕ)
    (hH : 0 < H) (hL : 0 < L) (hM : H+L=M) :
    Real.log (H : ℝ)-Real.log (L : ℝ) ≤ Real.log ((M : ℝ)-1) := by
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hsum : (H : ℝ)+(L : ℝ)=M := by exact_mod_cast hM
  have hbound : (H : ℝ) ≤ (M : ℝ)-1 := by linarith
  have hh := Real.log_le_log hHr hbound
  have hl := Real.log_nonneg hLr
  linarith

/-- Necessary ceiling only: violating the gain does not prove phenotype extinction. -/
theorem finite_population_horizon (H L M K : ℕ) (g : ℝ)
    (hH : 0 < H) (hL : 0 < L) (hM : H+L=M)
    (hgain : (K : ℝ)*g-Real.log 2 < Real.log (H : ℝ)-Real.log (L : ℝ)) :
    (K : ℝ)*g < Real.log (2*((M : ℝ)-1)) := by
  have hc := positive_count_log_odds_ceiling H L M hH hL hM
  have hm : (0 : ℝ) < (M : ℝ)-1 := by
    have : 2 ≤ M := by omega
    have : (2 : ℝ) ≤ M := by exact_mod_cast this
    linarith
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hm)]
  linarith

theorem ancestralCount_total (cs : List TaggedCell) :
    ancestralCount true cs+ancestralCount false cs=cs.length := by
  induction cs with
  | nil => simp [ancestralCount]
  | cons c cs ih =>
    cases hc : c.high <;> simp [ancestralCount,hc] at ih ⊢ <;> omega

theorem ready_count_odds_ceiling (N M : ℕ) (zL zH : ℝ)
    (s : ReadyPopulation N M zL zH)
    (hp : ∀ b, 0 < ancestralCount b s.val.live) :
    countLogOdds s.val ≤ Real.log ((M : ℝ)-1) := by
  apply positive_count_log_odds_ceiling _ _ M (hp true) (hp false)
  rw [ancestralCount_total]
  exact (readyPopulation_ready N M zL zH s).1

end SerialTransferSelection
