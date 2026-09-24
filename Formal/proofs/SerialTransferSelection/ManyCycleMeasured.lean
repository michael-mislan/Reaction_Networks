import proofs.SerialTransferSelection.ManyCycleBaseline
import proofs.SerialTransferSelection.ImprovedInstance

namespace SerialTransferSelection
open ResourceLimitedCompetition HeritableCompositions FiniteCopy CoreCouplingCAC Set

def manyMeasuredEvent (N M : ℕ) (zL zH : ℝ) (ε : ℝ)
    (K : ℕ) (s : PopulationState)
    (h : Fin K → Option (ReadyPopulation N M zL zH)) : Prop :=
  ∀ i : Fin K, ∃ y : ReadyPopulation N M zL zH, h i = some y ∧
    (∀ b, 0 < chemicalCount b y.val.live) ∧
    ((i.val+1 : ℕ) : ℝ)*cycleSizeGain ε-Real.log 2 <
      chemicalCountLogOdds y.val-chemicalCountLogOdds s

theorem manyCycle_good_measured (N M : ℕ) (hN : 0 < N) (zL zH : ℝ)
    (hzL : zL ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (hzH : zH ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
    (p : ℕ → ℝ) (ε : ℝ) (K : ℕ) (s : ReadyPopulation N M zL zH)
    (hnew : ∀ c ∈ s.val.live, c.compartment.2=N)
    (hpos : ∀ b, 0 < ancestralCount b s.val.live)
    (h : Fin K → Option (ReadyPopulation N M zL zH))
    (hh : historyGood (manyCycleStep N M zL zH p ε) K 0 (some s) h) :
    manyMeasuredEvent N M zL zH ε K s.val h := by
  intro i
  obtain ⟨y,hy,hyp,hgain⟩ := manyCycle_good_prefix N M zL zH p ε K 0 s h hh i
  have hrs := readyPopulation_ready N M zL zH s
  have hry := readyPopulation_ready N M zL zH y
  have hreadS := fun c hc => ready_population_readout N M zL zH hzL hzH s c hc
  have hreadY := fun c hc => ready_population_readout N M zL zH hzL hzH y c hc
  refine ⟨y,hy,?_,?_⟩
  · intro b
    rw [chemicalCount_eq_ancestralCount b y.val.live hreadY]
    exact hyp b
  · rw [chemicalCountLogOdds_eq y.val hreadY, chemicalCountLogOdds_eq s.val hreadS]
    exact newborn_endpoint_count_gain N hN s.val y.val hrs.2.2.2.1 hry.2.2.2.1
      hnew hpos hyp _ hgain

theorem finiteLaw_event_mono_many {α : Type*} [Fintype α] (μ : FiniteLaw α)
    (A B : Set α) (h : A ⊆ B) :
    μ.expect (FiniteKernel.eventIndicator A) ≤ μ.expect (FiniteKernel.eventIndicator B) := by
  classical
  apply μ.expect_mono
  intro x
  by_cases hx : x ∈ A
  · simp [FiniteKernel.eventIndicator,hx,h hx]
  · simp only [FiniteKernel.eventIndicator,if_neg hx]
    split_ifs <;> norm_num

end SerialTransferSelection
