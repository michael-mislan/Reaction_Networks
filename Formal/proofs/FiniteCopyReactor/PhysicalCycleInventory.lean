import proofs.FiniteCopyReactor.SegmentInventory
import proofs.FiniteCopyReactor.LiteralCycleBound

namespace FiniteCopyReactor
noncomputable section
open Classical ProductiveRecovery MeasureTheory ProbabilityTheory RandomViability RandomViability.Binding
open scoped ENNReal

structure CycleTrace (N : Counts) (V : ℕ) (p : Intervention) (Y : JointCounts) where
  pulse : PulseOutcome N
  middle : JointCounts
  recovery : SegmentTrace false (pulseInitialState N V p pulse) middle
  collection : SegmentTrace true middle Y

def CycleTrace.produced {N V p Y} (tr : CycleTrace N V p Y) : ℝ := tr.recovery.produced+tr.collection.produced
def CycleTrace.exported {N V p Y} (tr : CycleTrace N V p Y) : ℝ := tr.recovery.exported+tr.collection.exported
def CycleTrace.removed {N V p Y} (tr : CycleTrace N V p Y) : ℝ :=
  templateStock (categoryCounts N tr.pulse 1)+templateStock (categoryCounts N tr.pulse 2)

theorem CycleTrace.inventory {N V p Y} (tr : CycleTrace N V p Y) :
    templateStock Y.1+tr.removed+tr.exported=templateStock N+tr.produced := by
  have h0 := pulse_template_inventory N V p tr.pulse
  have h1 := tr.recovery.inventory
  have h2 := tr.collection.inventory
  change templateStock tr.middle.1+tr.recovery.exported=
    templateStock (postPulseCounts N V p tr.pulse)+tr.recovery.produced at h1
  dsimp only [CycleTrace.removed,CycleTrace.exported,CycleTrace.produced]
  linarith

theorem CycleTrace.removed_nonneg {N V p Y} (tr : CycleTrace N V p Y) : 0 ≤ tr.removed :=
  add_nonneg (templateStock_nonneg _) (templateStock_nonneg _)

theorem CycleTrace.collection_le {N V p Y} (tr : CycleTrace N V p Y) : (Y.2 1:ℝ) ≤ tr.exported := by
  have h1 := tr.recovery.collection_le
  have h2 := tr.collection.collection_le
  have hz : ((pulseInitialState N V p tr.pulse).2 1:ℝ)=0 := by
    simp [pulseInitialState,integerInitialCounters]
  rw [hz] at h1
  dsimp only [CycleTrace.exported]
  linarith

/-- The full pulse and unrestricted source law almost surely supply actual finite traces. -/
theorem literal_cycle_has_trace (N : Counts) (V : ℕ) (p : Intervention) (r d : ℝ)
    (hV : 0 < (V:ℝ)) (hr : 0 ≤ r) (hd : 0 ≤ d) :
    ∀ᵐ Y ∂literalPulseCycleMeasure N V p r d hV hr hd,Nonempty (CycleTrace N V p Y) := by
  unfold literalPulseCycleMeasure
  apply Measure.ae_comp_of_ae_ae (Set.to_countable _).measurableSet
  apply Filter.Eventually.of_forall
  intro o
  change ∀ᵐ Y ∂literalMarkedCycleKernel V r d hV hr hd (pulseInitialState N V p o),_
  apply Kernel.ae_comp_of_ae_ae (Set.to_countable _).measurableSet
  filter_upwards [joint_endpoint_has_trace false V r d hV hr hd (pulseInitialState N V p o) 3] with M hM
  filter_upwards [joint_endpoint_has_trace true V r d hV hr hd M 1] with Y hY
  exact ⟨⟨o,M,hM.some,hY.some⟩⟩

end
end FiniteCopyReactor
