import proofs.ProductiveMemory.ExtractionCycleLaw
import proofs.SerialTransferSelection.OperationalCorollaries
import proofs.SerialTransferSelection.DiscardAccounting

namespace ProductiveMemory
open ResourceLimitedCompetition HeritableCompositions FiniteCopy
noncomputable section
set_option Elab.async false

/-- Gross reservoir order F,G,RA,RB,WH,Zout,Q. No opposite exchanges are netted. -/
def productiveGrossExchange {D : Finset ProductiveState} (e : ProductivePopulationEvent D) (k : Fin 7) : ℕ :=
  match e.2 with
  | .inl ⟨_,.inl r⟩ => if h : k.val<5 then SerialTransferSelection.residentGrossExchange r ⟨k.val,h⟩ else 0
  | .inl ⟨_,.inr _⟩ => if k.val=6 then 1 else 0
  | .inr _ => if k.val=5 then 1 else 0

def extractionGrossExchange (r : ExtractionChannel) (k : Fin 7) : ℕ :=
  match r with
  | .inl j => if h : k.val<5 then SerialTransferSelection.residentGrossExchange j ⟨k.val,h⟩ else 0
  | .inr _ => if k.val=5 then 1 else 0

theorem productive_gross_le_one {D : Finset ProductiveState} (e : ProductivePopulationEvent D) (k : Fin 7) :
    productiveGrossExchange e k ≤ 1 := by
  rcases e with ⟨s,⟨i,r | d⟩ | i⟩
  · dsimp only [productiveGrossExchange]
    split_ifs
    · exact SerialTransferSelection.resident_gross_exchange_le_one _ _
    · omega
  · dsimp only [productiveGrossExchange]; split_ifs <;> omega
  · dsimp only [productiveGrossExchange]; split_ifs <;> omega

theorem extraction_gross_le_one (r : ExtractionChannel) (k : Fin 7) : extractionGrossExchange r k ≤ 1 := by
  cases r with
  | inl j =>
    dsimp only [extractionGrossExchange]
    split_ifs
    · exact SerialTransferSelection.resident_gross_exchange_le_one _ _
    · omega
  | inr r => dsimp only [extractionGrossExchange]; split_ifs <;> omega

theorem productive_batch_finite_service (rho gamma : ℝ) (hr : 0 ≤ rho) (hg : 0 ≤ gamma)
    (Omega N W0 J JS : ℕ) (zL zH : ℝ) (D : Finset ProductiveState) (s : ProductiveStopped D)
    (rs : List (ProductivePopulationEvent D))
    (hq : (SerialTransferSelection.eventRun (SerialTransferSelection.serviceCounterModel
      (productiveStoppedModel rho gamma hr hg Omega N W0 J zL zH D) JS) (s,0) rs).2.val < JS)
    (k : Fin 7) :
    (rs.map (fun r => productiveGrossExchange r k)).sum < JS ∧
    SerialTransferSelection.budgetRun (productiveStoppedModel rho gamma hr hg Omega N W0 J zL zH D)
      (fun r => productiveGrossExchange r k) JS s rs =
      SerialTransferSelection.eventRun (productiveStoppedModel rho gamma hr hg Omega N W0 J zL zH D) s rs := by
  exact ⟨SerialTransferSelection.service_run_material_budget _ JS s rs _ (fun r => productive_gross_le_one r k) hq,
    SerialTransferSelection.unsaturated_budget_agreement _ JS s rs _ (fun r => productive_gross_le_one r k) hq⟩

theorem extraction_recovery_finite_service (rho : ℝ) (hr : 0 ≤ rho) (m J : ℕ) (D : Finset Counts)
    (s : Option {n // n ∈ D}) (rs : List ExtractionChannel)
    (hq : (SerialTransferSelection.eventRun (SerialTransferSelection.serviceCounterModel
      (extractionStoppedModel rho hr m D) J) (s,0) rs).2.val < J) (k : Fin 7) :
    (rs.map (fun r => extractionGrossExchange r k)).sum < J ∧
    SerialTransferSelection.budgetRun (extractionStoppedModel rho hr m D)
      (fun r => extractionGrossExchange r k) J s rs =
      SerialTransferSelection.eventRun (extractionStoppedModel rho hr m D) s rs := by
  exact ⟨SerialTransferSelection.service_run_material_budget _ J s rs _ (fun r => extraction_gross_le_one r k) hq,
    SerialTransferSelection.unsaturated_budget_agreement _ J s rs _ (fun r => extraction_gross_le_one r k) hq⟩

theorem extraction_transfer_z_discard (M : ℕ) (s : PopulationState)
    (S : SerialTransferSelection.TransferSubset s.live.length M) :
    zInventory (SerialTransferSelection.exchangeSelectedMedium M s S).live+
      zInventory (SerialTransferSelection.discardedCells s.live.length M (selectedCell s) S)=zInventory s.live :=
  SerialTransferSelection.actual_transfer_material_balance M s S (fun c => c.compartment.1 2)

theorem productive_precursor_bill (N W0 J H0 L0 : ℕ) (rho zL zH : ℝ) {D : Finset ProductiveState}
    (x : ProductiveStopped D) (hx : x ∈ productiveBatchGoodSet N W0 J H0 L0 rho zL zH D) :
    (productivePhysical N x).population.resource=W0 ∧
      4*W0-(productivePhysical N x).population.resource=3*W0 := by
  obtain ⟨e,rfl,hn,_,_,_,_,_,_,_,_⟩ := hx
  have hq := productive_nutrient_resource N W0 J rho zL zH D e.1 e.2 hn
  change (productiveOutcome N e.1.val e.2).population.resource=W0 ∧ _
  exact ⟨hq.2.1,by change 4*W0-(productiveOutcome N e.1.val e.2).population.resource=3*W0; rw [hq.2.1]; omega⟩

end
end ProductiveMemory
