import proofs.FiniteReservoir.SegmentInventory
import proofs.FiniteReservoir.LiteralCycleBound

namespace FiniteReservoir
noncomputable section
open Classical FiniteCopyReactor ProductiveRecovery MeasureTheory ProbabilityTheory RandomViability RandomViability.Binding
open scoped ENNReal

structure CycleTrace (M : ℕ) (N : CountState M) (V : ℕ) (p : Intervention) (Y : (JointCounts M)) where
  pulse : PulseOutcome N.1
  middle : (JointCounts M)
  recovery : SegmentTrace false (pulseInitialState N.1 V M p N.2 pulse) middle
  collection : SegmentTrace true middle Y

def CycleTrace.produced {M N V p Y} (tr : CycleTrace M N V p Y) : ℝ := tr.recovery.produced+tr.collection.produced
def CycleTrace.exported {M N V p Y} (tr : CycleTrace M N V p Y) : ℝ := tr.recovery.exported+tr.collection.exported
def CycleTrace.removed {M N V p Y} (tr : CycleTrace M N V p Y) : ℝ :=
  templateStock (categoryCounts N.1 tr.pulse 1)+templateStock (categoryCounts N.1 tr.pulse 2)

theorem CycleTrace.inventory {M N V p Y} (tr : CycleTrace M N V p Y) :
    templateStock Y.1.1+tr.removed+tr.exported=templateStock N.1+tr.produced := by
  have h0 := pulse_template_inventory N.1 V p tr.pulse
  have h1 := tr.recovery.inventory
  have h2 := tr.collection.inventory
  change templateStock tr.middle.1.1+tr.recovery.exported=
    templateStock (postPulseCounts N.1 V p tr.pulse)+tr.recovery.produced at h1
  dsimp only [CycleTrace.removed,CycleTrace.exported,CycleTrace.produced]
  linarith

theorem CycleTrace.removed_nonneg {M N V p Y} (tr : CycleTrace M N V p Y) : 0 ≤ tr.removed :=
  add_nonneg (templateStock_nonneg _) (templateStock_nonneg _)

theorem CycleTrace.collection_le {M N V p Y} (tr : CycleTrace M N V p Y) : (Y.2 1:ℝ) ≤ tr.exported := by
  have h1 := tr.recovery.collection_le
  have h2 := tr.collection.collection_le
  have hz : ((pulseInitialState N.1 V M p N.2 tr.pulse).2 1:ℝ)=0 := by
    simp [pulseInitialState,integerInitialCounters]
  rw [hz] at h1
  dsimp only [CycleTrace.exported]
  linarith

/-- The full pulse and unrestricted source law almost surely supply actual finite traces. -/
theorem literal_cycle_has_trace (M : ℕ) (N : CountState M) (V : ℕ) (p : Intervention) (params : Parameters M)
    (hV : 0 < (V:ℝ))  :
    ∀ᵐ Y ∂literalPulseCycleMeasure N.1 V M p params N.2 hV,Nonempty (CycleTrace M N V p Y) := by
  unfold literalPulseCycleMeasure
  apply Measure.ae_comp_of_ae_ae (Set.to_countable _).measurableSet
  apply Filter.Eventually.of_forall
  intro o
  change ∀ᵐ Y ∂literalMarkedCycleKernel V M params hV (pulseInitialState N.1 V M p N.2 o),_
  apply Kernel.ae_comp_of_ae_ae (Set.to_countable _).measurableSet
  filter_upwards [joint_endpoint_has_trace false V M params hV (pulseInitialState N.1 V M p N.2 o) 3] with Z hZ
  filter_upwards [joint_endpoint_has_trace true V M params hV Z 1] with Y hY
  exact ⟨⟨o,Z,hZ.some,hY.some⟩⟩

end
end FiniteReservoir
