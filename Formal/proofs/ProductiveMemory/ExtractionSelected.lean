import proofs.ProductiveMemory.ExtractionUniformReady
import proofs.SerialTransferSelection.TransferPhysical
import proofs.SerialTransferSelection.RecoveryProduct

namespace ProductiveMemory
open FiniteCopy HeritableCompositions ResourceLimitedCompetition Set
open scoped NNReal
noncomputable section
set_option Elab.async false

def extractionCenter (rho zL zH : ℝ) (b : Bool) : Point := lift rho (if b then zH else zL)
def extractionEnergy (b : Bool) : Point → ℝ := if b then highExtractionEnergy else lowExtractionEnergy
def extractionDomain (rho zL zH : ℝ) (b : Bool) (m : ℕ) : Finset Counts :=
  energyDomain m (extractionCenter rho zL zH b) (extractionEnergy b) outerLevel

theorem mixed_extraction_ready (rho zL zH : ℝ)
    (hr : rho ∈ Icc (9999/1000000:ℝ) (1/100))
    (hzL : zL ∈ Icc (98172/100000:ℝ) (98174/100000))
    (hzH : zH ∈ Icc (289014/100000:ℝ) (289017/100000))
    (heL : extractDrift rho 0 (lift rho zL) = 0)
    (heH : extractDrift rho 0 (lift rho zH) = 0)
    (b : Bool) (m : ℕ) (hm : recoveryCount ≤ m)
    (q : NNReal) (hq : 0 < (q:ℝ))
    (hclock : ∀ s, (extractionStoppedModel rho (by linarith [hr.1]) m
      (extractionDomain rho zL zH b m)).total s ≤ q)
    (hk : (m:ℝ)*localAlpha*readyLevel/480 ≤ q)
    (n : {n : Counts // n ∈ extractionDomain rho zL zH b m})
    (hbirth : extractionEnergy b (fun i => concentration m n.val i-extractionCenter rho zL zH b i) ≤ 8*readyLevel) :
    1-1/10^18 ≤
    ((extractionStoppedModel rho (by linarith [hr.1]) m (extractionDomain rho zL zH b m)).uniformize q hq hclock).poissonized (q*5376)
      (FiniteKernel.eventIndicator (terminalReady m (extractionDomain rho zL zH b m)
        (extractionCenter rho zL zH b) (extractionEnergy b))) (some n) := by
  cases b with
  | false => exact low_extraction_uniform_ready rho zL hr hzL heL m hm q hq hclock hk n hbirth
  | true => exact high_extraction_uniform_ready rho zH hr hzH heH m hm q hq hclock hk n hbirth

def extractionCellEnergy (rho zL zH : ℝ) (c : TaggedCell) : ℝ :=
  extractionEnergy c.high (fun i => concentration c.compartment.2 c.compartment.1 i-
    extractionCenter rho zL zH c.high i)

def extractionRetained (M : ℕ) (s : PopulationState)
    (S : SerialTransferSelection.TransferSubset s.live.length M) (i : Fin M) : TaggedCell :=
  selectedCell (SerialTransferSelection.exchangeSelectedMedium M s S)
    ⟨i.val, by rw [SerialTransferSelection.exchangeSelectedMedium_length]; exact i.isLt⟩

theorem extraction_retained_mem (M : ℕ) (s : PopulationState)
    (S : SerialTransferSelection.TransferSubset s.live.length M) (i : Fin M) :
    extractionRetained M s S i ∈ s.live :=
  SerialTransferSelection.exchangeSelectedMedium_preserves M s S _ (selected_mem _ _)

theorem extraction_cell_admitted (rho zL zH : ℝ)
    (hr : rho ∈ Icc (9999/1000000:ℝ) (1/100))
    (hzL : zL ∈ Icc (98172/100000:ℝ) (98174/100000))
    (hzH : zH ∈ Icc (289014/100000:ℝ) (289017/100000))
    (c : TaggedCell) (hm : recoveryCount ≤ c.compartment.2)
    (he : extractionCellEnergy rho zL zH c ≤ 8*readyLevel) :
    c.compartment.1 ∈ extractionDomain rho zL zH c.high c.compartment.2 := by
  have hm1 : 1 ≤ c.compartment.2 := (by norm_num [recoveryCount] : 1 ≤ recoveryCount).trans hm
  have hs : ∀ i, extractionCenter rho zL zH c.high i ≤ 34 := by
    cases hb : c.high with
    | false => exact low_extraction_root_upper rho zL hr hzL
    | true => exact high_extraction_root_upper rho zH hr hzH
  have hE : ∀ y, (1/200:ℝ)*normSq y ≤ extractionEnergy c.high y := by
    cases hb : c.high with
    | false => exact lowExtractionEnergy_lower
    | true => exact highExtractionEnergy_lower
  apply (mem_energyDomain c.compartment.2 hm1 c.compartment.1 _ hs _ hE outerLevel
    (by norm_num [outerLevel])).mpr
  exact he.trans_lt (by norm_num [readyLevel,outerLevel])

end
end ProductiveMemory
