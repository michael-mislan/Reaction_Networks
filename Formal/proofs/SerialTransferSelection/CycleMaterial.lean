import proofs.SerialTransferSelection.CycleProbability
import proofs.SerialTransferSelection.ServiceMaterial

namespace SerialTransferSelection
open ResourceLimitedCompetition HeritableCompositions FiniteCopy

def populationGrossExchange {D : Finset PopulationState} (e : PopulationEvent D) (k : Fin 5) : ℕ :=
  match e.2.2 with | .inl r => residentGrossExchange r k | .inr _ => 0

def recoveryGrossExchange (r : Channel) (k : Fin 5) : ℕ :=
  match r with | .inl j => residentGrossExchange j k | .inr _ => 0

theorem population_gross_le_one {D : Finset PopulationState} (e : PopulationEvent D) (k : Fin 5) :
    populationGrossExchange e k ≤ 1 := by
  unfold populationGrossExchange
  split
  · exact resident_gross_exchange_le_one _ _
  · omega

theorem recovery_gross_le_one (r : Channel) (k : Fin 5) : recoveryGrossExchange r k ≤ 1 := by
  cases r with
  | inl j => exact resident_gross_exchange_le_one j k
  | inr _ => exact Nat.zero_le _

theorem batch_gross_service_from_quota (γ : ℝ) (hγ : 0 ≤ γ) (Ω N W0 J : ℕ)
    (zL zH : ℝ) (D : Finset PopulationState) (x : StoppedPopulation D)
    (rs : List (PopulationEvent D))
    (hq : (eventRun (serviceCounterModel (phaseStoppedModel γ hγ Ω N W0 zL zH D) J)
      (x,0) rs).2.val < J) (k : Fin 5) :
    (rs.map (fun r => populationGrossExchange r k)).sum < J :=
  service_run_material_budget _ J x rs _ (fun r => population_gross_le_one r k) hq

theorem recovery_gross_service_from_quota (N J : ℕ) (zL zH : ℝ) (tag : Bool)
    (x : StoppedCompartment (recoveryCellDomain N zL zH tag)) (rs : List Channel)
    (hq : (eventRun (serviceCounterModel (recoveryCellModel N zL zH tag) J) (x,0) rs).2.val < J)
    (k : Fin 5) : (rs.map (fun r => recoveryGrossExchange r k)).sum < J :=
  service_run_material_budget _ J x rs _ (fun r => recovery_gross_le_one r k) hq

/-- Apply separately to each literal reservoir. No independence of bills is used. -/
theorem two_cycle_gross_allowance (M JB JR : ℕ) (B : Fin 2 → ℕ) (R : Fin 2 → Fin M → ℕ)
    (hb : ∀ j, B j < JB) (hr : ∀ j i, R j i < JR) :
    (∑ j, (B j+(∑ i, R j i))) < 2*(JB+M*JR) := by
  have hR (j : Fin 2) : (∑ i, R j i) ≤ M*JR := by
    have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => (hr j i).le)
    simpa using h
  simp only [Fin.sum_univ_two]
  change B 0+(∑ i, R 0 i)+(B 1+(∑ i, R 1 i)) < 2*(JB+M*JR)
  have h0 := hR 0
  have h1 := hR 1
  have hb0 := hb 0
  have hb1 := hb 1
  omega

theorem successful_batch_growth_bill (N W0 H0 L0 : ℕ) (zL zH : ℝ)
    {D : Finset PopulationState} (x : StoppedPopulation D)
    (hx : x ∈ phaseBatchGoodSet N W0 H0 L0 zL zH D) :
    (physicalState N x).resource=W0 ∧
      4*W0-(physicalState N x).resource=3*W0 ∧ membrane (physicalState N x).live=4*W0 := by
  obtain ⟨e,rfl,hn,_,_,hw,_,_,_⟩ := hx
  have hq := (phase_nutrient_event_resource N W0 zL zH D e.1 e.2 hn).2.1
  exact ⟨hq,by dsimp only [physicalState]; rw [hq]; omega,hw⟩

theorem two_cycle_growth_stock (N M : ℕ) (s t : PopulationState)
    (hs : s.live.length=M) (ht : t.live.length=M) (hvs : ValidVolumes N s) (hvt : ValidVolumes N t) :
    4*membrane s.live+4*membrane t.live ≤ 16*N*M := by
  have h0 := membrane_upper N s.live (fun c hc => (hvs c hc).2.le)
  have h1 := membrane_upper N t.live (fun c hc => (hvt c hc).2.le)
  rw [hs] at h0
  rw [ht] at h1
  nlinarith only [h0,h1]

end SerialTransferSelection
