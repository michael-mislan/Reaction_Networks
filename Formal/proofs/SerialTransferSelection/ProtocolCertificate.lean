import proofs.SerialTransferSelection.ProtocolRealization
import proofs.SerialTransferSelection.CycleMaterial
import proofs.SerialTransferSelection.DiscardAccounting

namespace SerialTransferSelection
open ResourceLimitedCompetition HeritableCompositions FiniteCopy

/-- Universal properties of the very physical operations used by sourceCycleLaw.
Analysis stopping flags and failure quotients are not physical sampling rules. -/
structure SerialProtocolCertificate : Prop where
  balanced : ∀ j, (∑ i, CommonPhysicalRealization.Resident.left j i * CommonPhysicalRealization.Resident.element i) =
    ∑ i, CommonPhysicalRealization.Resident.right j i * CommonPhysicalRealization.Resident.element i
  thermodynamic : ∀ j, Real.log (CommonPhysicalRealization.Resident.kp j/CommonPhysicalRealization.Resident.km j) =
    ∑ i, ((CommonPhysicalRealization.Resident.left j i : ℝ)-CommonPhysicalRealization.Resident.right j i)*
      CommonPhysicalRealization.Resident.potential i
  resident_projection : ∀ c r γ, CommonPhysicalRealization.Resident.maintainedPropensity c 1 1 1 1 r=
    propensity γ c (.inl r)
  equal_sample_mass : ∀ L M (hM : M ≤ L) (S T : TransferSubset L M),
    (uniformTransferLaw L M hM).mass S=(uniformTransferLaw L M hM).mass T
  sampling_neutral : ∀ L M (hM : M ≤ L) (a b : Fin L → TaggedCell),
    (∀ i, (a i).compartment=(b i).compartment) → ∀ F : List Compartment → ℝ,
    (uniformTransferLaw L M hM).expect (fun S => F ((retainSubset L M a S).map TaggedCell.compartment)) =
      (uniformTransferLaw L M hM).expect (fun S => F ((retainSubset L M b S).map TaggedCell.compartment))
  refill_neutral : ∀ a b : List TaggedCell, a.map TaggedCell.compartment=b.map TaggedCell.compartment →
    (preparePhaseBatch a).resource=(preparePhaseBatch b).resource
  empty_precursor : ∀ γ Ω c r, propensity (resourceCoefficient γ 0 Ω) c r=propensity 0 c r
  exchange_empty : ∀ M s (S : TransferSubset s.live.length M), (exchangeSelectedMedium M s S).resource=0
  intact_selection : ∀ M s (S : TransferSubset s.live.length M) c,
    c ∈ (exchangeSelectedMedium M s S).live → c ∈ s.live
  discard_balance : ∀ M s (S : TransferSubset s.live.length M) (F : TaggedCell → ℕ),
    ((exchangeSelectedMedium M s S).live.map F).sum+
      ((discardedCells s.live.length M (selectedCell s) S).map F).sum=(s.live.map F).sum
  resident_event_cost : ∀ r k, residentGrossExchange r k ≤ 1
  batch_quota_material : ∀ γ (hγ : 0 ≤ γ) Ω N W0 J zL zH D (x : StoppedPopulation D)
    (rs : List (PopulationEvent D)),
    (eventRun (serviceCounterModel (phaseStoppedModel γ hγ Ω N W0 zL zH D) J) (x,0) rs).2.val < J →
      ∀ k, (rs.map (fun r => populationGrossExchange r k)).sum < J
  recovery_quota_material : ∀ N J zL zH tag (x : StoppedCompartment (recoveryCellDomain N zL zH tag))
    (rs : List Channel), (eventRun (serviceCounterModel (recoveryCellModel N zL zH tag) J) (x,0) rs).2.val < J →
      ∀ k, (rs.map (fun r => recoveryGrossExchange r k)).sum < J
  two_cycle_allowance : ∀ M JB JR (B : Fin 2 → ℕ) (R : Fin 2 → Fin M → ℕ),
    (∀ j, B j < JB) → (∀ j i, R j i < JR) →
      (∑ j, (B j+(∑ i, R j i))) < 2*(JB+M*JR)
  growth_bill : ∀ N W0 H0 L0 zL zH (D : Finset PopulationState) (x : StoppedPopulation D),
    x ∈ phaseBatchGoodSet N W0 H0 L0 zL zH D →
      (physicalState N x).resource=W0 ∧ 4*W0-(physicalState N x).resource=3*W0 ∧
        membrane (physicalState N x).live=4*W0

theorem serial_protocol_certified : SerialProtocolCertificate where
  balanced := CommonPhysicalRealization.Resident.balanced
  thermodynamic := CommonPhysicalRealization.Resident.thermo
  resident_projection := maintained_resident_source
  equal_sample_mass := uniform_sampling_equal_mass
  sampling_neutral := sampling_ignores_tags
  refill_neutral := refill_ignores_tags
  empty_precursor := recovery_at_empty_precursor
  exchange_empty := exchangeSelectedMedium_resource
  intact_selection := exchangeSelectedMedium_preserves
  discard_balance := actual_transfer_material_balance
  resident_event_cost := resident_gross_exchange_le_one
  batch_quota_material := batch_gross_service_from_quota
  recovery_quota_material := recovery_gross_service_from_quota
  two_cycle_allowance := two_cycle_gross_allowance
  growth_bill := fun N W0 H0 L0 zL zH _ => successful_batch_growth_bill N W0 H0 L0 zL zH

end SerialTransferSelection
