import proofs.RAF1519.Refinement.HoldingIndex
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace RAF1519.Refinement
noncomputable section
open Classical MeasureTheory
open scoped BigOperators

def holdingStepSum (h v : ℕ → ℝ) (K : ℕ) (t : ℝ) : ℝ :=
  ∑ j : Fin K, (Set.Ico (holdingClock h j) (holdingClock h j+h j)).indicator (fun _ => v j) t

theorem holdingStepSum_eq (h v : ℕ → ℝ) (hh : ∀ i, 0 ≤ h i)
    (K : ℕ) (t : ℝ) (ht : 0 ≤ t) (hK : t < holdingClock h K) :
    holdingStepSum h v K t = v (holdingIndex h t) := by
  have hi := holdingIndex_before_prefix h hh K t ht hK
  let j : Fin K := ⟨holdingIndex h t,hi.1⟩
  unfold holdingStepSum
  rw [Finset.sum_eq_single j]
  · rw [Set.indicator_of_mem (show t ∈ Set.Ico (holdingClock h j) (holdingClock h j+h j) from hi.2)]
  · intro q _ hq
    apply Set.indicator_of_notMem
    intro htq
    have he := holdingIndex_eq h hh t q htq.1 htq.2
    apply hq
    apply Fin.ext
    exact he.symm
  · intro hj
    exact False.elim (hj (Finset.mem_univ j))

theorem holdingStepSum_integrable (h v : ℕ → ℝ) (K : ℕ) (a b : ℝ) :
    IntervalIntegrable (holdingStepSum h v K) volume a b := by
  have hi : ∀ j : Fin K, IntervalIntegrable
      ((Set.Ico (holdingClock h j) (holdingClock h j+h j)).indicator (fun _ => v j)) volume a b := by
    intro j
    have hc : IntervalIntegrable (fun _ : ℝ => v j) volume a b := intervalIntegrable_const
    exact ⟨hc.1.indicator measurableSet_Ico,hc.2.indicator measurableSet_Ico⟩
  convert IntervalIntegrable.sum Finset.univ (fun j _ => hi j) using 1
  funext t
  simp only [holdingStepSum,Finset.sum_apply]

/-- Every state observable of a nonexplosive chronological path is integrable
    on a finite positive-time window, via its finite holding-interval partition. -/
theorem holdingObservable_integrable (h v : ℕ → ℝ) (hh : ∀ i, 0 ≤ h i)
    (K : ℕ) (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hK : b < holdingClock h K) :
    IntervalIntegrable (fun t => v (holdingIndex h t)) volume a b := by
  apply (holdingStepSum_integrable h v K a b).congr
  intro t ht
  rw [Set.uIoc_of_le hab] at ht
  exact holdingStepSum_eq h v hh K t (ha.trans ht.1.le) (ht.2.trans_lt hK)

end
end RAF1519.Refinement
