import proofs.ProductiveMemory.ExtractionHistory
import proofs.ProductiveMemory.ExtractionMaterialService

namespace ProductiveMemory
open ResourceLimitedCompetition HeritableCompositions FiniteCopy
noncomputable section
set_option Elab.async false

/-- Resident formal material weights A=2,B=1,z=1,H=2. -/
def residentWeight : Fin 4 → ℤ := ![2,1,1,2]
/-- External weights F=1,G=3,RA=2,RB=1,WH=2,Zout=1,Q=1. -/
def externalWeight : Fin 7 → ℤ := ![1,3,2,1,2,1,1]

/-- Signed reservoir change, positive for collection and negative for supply. -/
def residentExternalChange (r : Fin 13) (k : Fin 7) : ℤ :=
  if hk : k.val<5 then
    if hr : r.val<12 then
      let a : Fin 6 := ⟨r.val/2,by omega⟩
      let b : Fin 9 := ⟨k.val+4,by omega⟩
      if r.val%2=0 then
        (CommonPhysicalRealization.Resident.right a b:ℤ)-CommonPhysicalRealization.Resident.left a b
      else (CommonPhysicalRealization.Resident.left a b:ℤ)-CommonPhysicalRealization.Resident.right a b
    else if k.val=4 then 1 else 0
  else 0

theorem extraction_resident_element_balance (r : Fin 13) :
    (∑ j, intJump r j*residentWeight j)+(∑ k, residentExternalChange r k*externalWeight k)=0 := by
  revert r
  decide

theorem extraction_collection_element_balance : -residentWeight 2+externalWeight 5=0 := by decide

/-- One size material unit contains one Q and one z. Its formal weight is two. -/
theorem extraction_growth_element_balance : -residentWeight 2-externalWeight 6+2=0 := by decide

theorem extraction_resident_gross_controls_signed (r : Fin 13) (k : Fin 5) :
    (residentExternalChange r ⟨k.val,by omega⟩).natAbs=SerialTransferSelection.residentGrossExchange r k := by
  revert r k
  decide

/-- Intact-cell transfer preserves any weighted resident inventory exactly. -/
theorem extraction_weighted_discard (M : ℕ) (s : PopulationState)
    (S : SerialTransferSelection.TransferSubset s.live.length M) :
    let weight := fun c : TaggedCell => 2*c.compartment.1 0+c.compartment.1 1+
      c.compartment.1 2+2*c.compartment.1 3+2*c.compartment.2
    ((SerialTransferSelection.exchangeSelectedMedium M s S).live.map weight).sum+
      ((SerialTransferSelection.discardedCells s.live.length M (selectedCell s) S).map weight).sum=
      (s.live.map weight).sum := by
  exact SerialTransferSelection.actual_transfer_material_balance M s S _

end
end ProductiveMemory
