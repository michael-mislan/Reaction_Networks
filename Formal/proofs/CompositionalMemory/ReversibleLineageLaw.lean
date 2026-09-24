import proofs.CompositionalMemory.ReversibleOffspringAllocation
import proofs.CompositionalMemory.FiniteLineageKernel

namespace CompositionalMemory
open Classical RandomViability MeasureTheory ProbabilityTheory ControlledRows
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 100000

def reversibleOffspringPayoff (word : Fin 2 → Fin 2) (b : ReversibleWordNewborn word)
    (T : ℝ) (z : ReversibleBudgetPath 53) : ℝ≥0∞ :=
  ∑' k, if reversibleFirstDivisionAt 53 z k ∧ jumpElapsed z k ≤ T
    then reversibleOffspringWeight word (z k).1 b else 0

theorem reversibleOffspringPayoff_measurable (word : Fin 2 → Fin 2)
    (b : ReversibleWordNewborn word) (T : ℝ) : Measurable (reversibleOffspringPayoff word b T) := by
  apply Measurable.tsum
  intro k
  exact Measurable.ite ((reversibleFirstDivisionAt_measurable 53 k).inter
    (measurableSet_le (jumpElapsed_measurable k) measurable_const))
    ((measurable_of_countable (fun s => reversibleOffspringWeight word s b)).comp
      (measurable_pi_apply k).fst) measurable_const

theorem reversibleOffspringPayoff_sum (word : Fin 2 → Fin 2) (T : ℝ) (z : ReversibleBudgetPath 53) :
    (∑ b : ReversibleWordNewborn word,reversibleOffspringPayoff word b T z)=
      reversibleFirstDivisionPayoff 53 word T z := by
  rw [← tsum_fintype (L := SummationFilter.unconditional (ReversibleWordNewborn word))
    (fun b : ReversibleWordNewborn word => reversibleOffspringPayoff word b T z)]
  simp only [reversibleOffspringPayoff,reversibleFirstDivisionPayoff]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro k
  by_cases hk : reversibleFirstDivisionAt 53 z k ∧ jumpElapsed z k ≤ T
  · simpa only [if_pos hk,tsum_fintype] using reversibleOffspringWeight_sum word (z k).1
  · simp only [if_neg hk,tsum_zero]

theorem reversibleFirstDivisionReturn_le_one (N J : Nat) (ε ρ : ℝ) (hε : 0 ≤ ε) (hρ : 0 ≤ ρ)
    (word : Fin 2 → Fin 2) (initial : ReversibleBudgetState N) :
    reversibleFirstDivisionReturn N J ε ρ hε hρ word initial ≤ 1 := by
  calc
    _ ≤ ∫⁻ _,(1 : ℝ≥0∞) ∂jumpTrajectoryLaw initial (reversibleBudgetNext N J)
        (reversibleBudgetRate N ε ρ) (reversibleBudgetRate_nonneg N ε ρ hε hρ)
        (reversibleBudgetRate_total_pos N ε ρ hε hρ) :=
      lintegral_mono (reversibleFirstDivisionPayoff_le_one N word 20)
    _ = 1 := by simp

/-- Each cycle resets the event quota and membrane to the newborn scale.
Both siblings are inspected and daughter A continues the designated lineage. -/
def reversibleCycleWeight (ε ρ : ℝ) (hε : 0 ≤ ε) (hρ : 0 ≤ ρ) (word : Fin 2 → Fin 2)
    (a b : ReversibleWordNewborn word) : ℝ≥0∞ :=
  ∫⁻ z,reversibleOffspringPayoff word b 20 z ∂jumpTrajectoryLaw
    (reversibleBudgetEmbed 53 100000000 (⟨0,reversiblePairArray a.val⟩,0))
    (reversibleBudgetNext 53 100000000) (reversibleBudgetRate 53 ε ρ)
    (reversibleBudgetRate_nonneg 53 ε ρ hε hρ) (reversibleBudgetRate_total_pos 53 ε ρ hε hρ)

theorem reversibleCycleWeight_sum (ε ρ : ℝ) (hε : 0 ≤ ε) (hρ : 0 ≤ ρ)
    (word : Fin 2 → Fin 2) (a : ReversibleWordNewborn word) :
    (∑ b : ReversibleWordNewborn word,reversibleCycleWeight ε ρ hε hρ word a b)=
      reversibleFirstDivisionReturn 53 100000000 ε ρ hε hρ word
        (reversibleBudgetEmbed 53 100000000 (⟨0,reversiblePairArray a.val⟩,0)) := by
  simp only [reversibleCycleWeight,reversibleFirstDivisionReturn]
  rw [← lintegral_finsetSum Finset.univ (fun b _ => reversibleOffspringPayoff_measurable word b 20)]
  apply lintegral_congr
  intro z
  exact reversibleOffspringPayoff_sum word 20 z

def reversibleCycleKernel (ε ρ : ℝ) (hε : 0 ≤ ε) (hρ : 0 ≤ ρ) (word : Fin 2 → Fin 2) :
    FiniteLineageKernel (ReversibleWordNewborn word) where
  weight := reversibleCycleWeight ε ρ hε hρ word
  total_le_one a := by
    rw [reversibleCycleWeight_sum]
    exact reversibleFirstDivisionReturn_le_one 53 100000000 ε ρ hε hρ word _

theorem reversible_ten_cycles_from_checks (ε ρ : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1/10)
    (hρ : 0 ≤ ρ) (hρu : ρ ≤ 2/10000000) (data : Nat → Array Int)
    (hrows : ∀ m, 53 ≤ m → m < 106 → ReversibleRows.checkLayer m (data m) (data (m+1))=true)
    (ht : ReversibleRows.terminalCheck 53 (data 106)=true)
    (hb : ReversibleRows.birthOK 53 (data 53)=true)
    (word : Fin 2 → Fin 2) (a : ReversibleWordNewborn word) :
    (9/10 : ℝ≥0∞) ≤ (reversibleCycleKernel ε ρ hε hρ word).survival 10 a := by
  apply (reversibleCycleKernel ε ρ hε hρ word).ten_cycles
  intro b
  change (9901/10000 : ℝ≥0∞) ≤ ∑ c,reversibleCycleWeight ε ρ hε hρ word b c
  rw [reversibleCycleWeight_sum]
  have hh := reversible_actual_first_division_from_checks ε ρ hε hε1 hρ hρu data hrows ht hb word
    (reversiblePairArray b.val) (reversiblePairArray_newborn word b)
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 10000)] at hh
  norm_num only [ENNReal.ofReal_ofNat] at hh
  exact hh

end
end CompositionalMemory
