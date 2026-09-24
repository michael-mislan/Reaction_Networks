import proofs.ProductiveRecovery.RepeatedOperation
import proofs.ProductiveRecovery.SourceCorrespondence
import proofs.ProductiveRecovery.SourceUniqueness
import proofs.ProductiveRecovery.InventoryAccounting

namespace ProductiveRecovery
noncomputable section

def exampleState : State := fun i => if i=0 ∨ i=1 then 99/100 else 1/1000
theorem example_admitted : Admitted exampleState := by
  have hn : Nonneg exampleState := by
    intro i
    dsimp [exampleState]
    split_ifs <;> norm_num
  refine ⟨hn,?_,?_,?_⟩ <;> norm_num [A,B,Y,exampleState,Fin.ext_iff]

def exampleIntervention : Intervention where
  q := 1/2
  loss := fun _ => 99/100
  eU := 0
  eW := 0
  q_lower := by norm_num
  q_upper := by norm_num
  loss_lower := by intro i; norm_num
  loss_upper := by intro i; norm_num
  eU_lower := by norm_num
  eU_upper := by norm_num
  eW_lower := by norm_num
  eW_upper := by norm_num

/-- Source-authenticated productive return with actual global trajectories.
The parameter is fixed before intervention. No recovery premise is supplied. -/
theorem productive_recovery (r d : ℝ) (hr : 19 ≤ r) (hr' : r ≤ 21)
    (hd : 1/50 ≤ d) (hd' : d ≤ 1/25) (p : Intervention) (c : State) (hc : Admitted c) :
    (∀ s : State, ∀ i : Fin 6, field r d s i = (if i=0 ∨ i=1 then 1 else 0)-s i +
      ∑ j : Fin 6, flux r d s j *
        ((CommonPhysicalRealization.pairRight j (i.castLE (by decide)) : ℝ)-
          CommonPhysicalRealization.pairLeft j (i.castLE (by decide)))) ∧
    ∃ X : ℝ → State, X 0 = pulse p c ∧
      (∀ t, 0 ≤ t → Nonneg (X t)) ∧
      (∀ t, 0 ≤ t → HasDerivAt X (field r d (X t)) t) ∧
      Returned (X 4) ∧ Returned (X 5) ∧
      1/3500 ≤ measuredExport X ∧ foodU p ≤ 1151/200 ∧ foodW p ≤ 1151/200 ∧
      grossService d X ≤ 9/40 := by
  exact ⟨fun s => field_stoichiometry r d s,exists_productive_cycle r d hr hr' hd hd' p c hc⟩

end
end ProductiveRecovery
