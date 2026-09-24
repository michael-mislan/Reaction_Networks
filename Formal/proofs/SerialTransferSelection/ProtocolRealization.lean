import proofs.SerialTransferSelection.RecoveryDock
import proofs.SerialTransferSelection.BatchConservation
import proofs.SerialTransferSelection.ServiceMaterial

namespace SerialTransferSelection
open ResourceLimitedCompetition HeritableCompositions FiniteCopy

theorem uniform_sampling_equal_mass (L M : ℕ) (hM : M ≤ L) (S T : TransferSubset L M) :
    (uniformTransferLaw L M hM).mass S=(uniformTransferLaw L M hM).mass T := rfl

/-- Relabeling cells without changing their physical compartments does not
change the distribution of the sampled physical compartments. -/
theorem sampling_ignores_tags (L M : ℕ) (hM : M ≤ L) (a b : Fin L → TaggedCell)
    (hab : ∀ i, (a i).compartment=(b i).compartment) (F : List Compartment → ℝ) :
    (uniformTransferLaw L M hM).expect (fun S => F ((retainSubset L M a S).map TaggedCell.compartment)) =
      (uniformTransferLaw L M hM).expect (fun S => F ((retainSubset L M b S).map TaggedCell.compartment)) := by
  apply congrArg (uniformTransferLaw L M hM).expect
  funext S
  apply congrArg F
  simp only [retainSubset,List.map_map]
  apply List.map_congr_left
  intro i _
  exact hab i

theorem refill_ignores_tags (a b : List TaggedCell)
    (hab : a.map TaggedCell.compartment=b.map TaggedCell.compartment) :
    (preparePhaseBatch a).resource=(preparePhaseBatch b).resource := by
  have hh := congrArg (fun cs : List Compartment => (cs.map Prod.snd).sum) hab
  have hm : membrane a=membrane b := by
    simpa only [membrane,List.map_map,Function.comp_def] using hh
  simp only [preparePhaseBatch,hm]

/-- Empty precursor switches off growth for the same physical compartment,
while retaining every resident direction and its literal count convention. -/
theorem recovery_at_empty_precursor (γ : ℝ) (Ω : ℕ) (c : Compartment) (r : Channel) :
    propensity (resourceCoefficient γ 0 Ω) c r=propensity 0 c r := by
  simp [resourceCoefficient]

theorem maintained_resident_source (c : Compartment) (r : Fin 13) (γ : ℝ) :
    CommonPhysicalRealization.Resident.maintainedPropensity c 1 1 1 1 r=
      propensity γ c (.inl r) := CommonPhysicalRealization.Resident.resident_projection c r γ

theorem population_resident_rate_binding (γ : ℝ) (Ω : ℕ) {D : Finset PopulationState}
    (s : ActiveState D) (i : Fin s.val.live.length) (r : Fin 13) :
    eventRate γ Ω ⟨s,i,.inl r⟩ =
      CommonPhysicalRealization.Resident.maintainedPropensity (selectedCell s.val i).compartment 1 1 1 1 r := by
  rw [maintained_resident_source _ r (resourceCoefficient γ s.val.resource Ω)]
  rfl

/-- The common compartment determines the growth and complementary-draw rate;
no ancestry label is an argument of either propensity or partition weight. -/
theorem population_growth_rate_binding (γ : ℝ) (Ω : ℕ) {D : Finset PopulationState}
    (s : ActiveState D) (i : Fin s.val.live.length)
    (d : {d : Counts // d ∈ daughterDraws (nextCompartment (selectedCell s.val i).compartment (.inr ())).1}) :
    eventRate γ Ω ⟨s,i,.inr d⟩ =
      γ*((s.val.resource : ℝ)/(Ω : ℝ))*((selectedCell s.val i).compartment.1 2 : ℝ)*
        daughterWeight (nextCompartment (selectedCell s.val i).compartment (.inr ())).1 d.val := rfl

end SerialTransferSelection
