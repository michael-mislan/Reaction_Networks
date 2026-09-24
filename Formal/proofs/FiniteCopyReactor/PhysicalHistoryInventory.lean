import proofs.FiniteCopyReactor.PhysicalCycleInventory
import proofs.FiniteCopyReactor.SourceHorizon

namespace FiniteCopyReactor
noncomputable section
open Classical ProductiveRecovery MeasureTheory ProbabilityTheory RandomViability RandomViability.Binding
open scoped ENNReal

inductive HistoryTrace (N : Counts) (V : ℕ) (policy : ReturnedHistory → Intervention) : ReturnedHistory → Type
  | nil : HistoryTrace N V policy []
  | cons {h : ReturnedHistory} (previous : HistoryTrace N V policy h) (Y : JointCounts)
      (cycle : CycleTrace (returnedObservation N h).1 V (policy h) Y) : HistoryTrace N V policy (Y::h)

def HistoryTrace.produced {N V policy h} : HistoryTrace N V policy h → ℝ
  | .nil => 0
  | .cons previous _ cycle => previous.produced+cycle.produced

/-- The retained stock and all collected output are funded by initial stock plus actual net synthesis. -/
theorem HistoryTrace.inventory_lower {N V policy h} (tr : HistoryTrace N V policy h) :
    templateStock (returnedObservation N h).1+returnedTotal h 1 ≤ templateStock N+tr.produced := by
  induction tr with
  | nil => simp [returnedObservation,returnedTotal,HistoryTrace.produced]
  | @cons h previous Y cycle ih =>
    have hi := cycle.inventory
    have hc := cycle.collection_le
    have hr := cycle.removed_nonneg
    change templateStock Y.1+((Y.2 1:ℝ)+returnedTotal h 1) ≤
      templateStock N+(previous.produced+cycle.produced)
    linarith

theorem HistoryTrace.net_lower {N V policy h} (tr : HistoryTrace N V policy h) :
    returnedTotal h 1-templateStock N ≤ tr.produced := by
  have hh := tr.inventory_lower
  have hn := templateStock_nonneg (returnedObservation N h).1
  linarith

theorem HistoryTrace.certified_net_lower {N V policy h} (tr : HistoryTrace N V policy h)
    (n : ℕ) (hN : Restart V N) (hh : h ∈ returnedFinal V n) :
    ((n:ℝ)/56-161/160)*(V:ℝ) ≤ tr.produced := by
  have ht := (returned_joint_totals V n h hh).1
  have hc := Nat.le_ceil ((V:ℝ)/56)
  have hn : (n:ℝ)*((V:ℝ)/56) ≤ (n:ℝ)*(Nat.ceil ((V:ℝ)/56):ℝ) :=
    mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg n)
  have hi := (templateStock_le_uCount N).trans hN.2.1
  have hp := tr.net_lower
  nlinarith

theorem full_history_has_trace (N : Counts) (V : ℕ) (r d : ℝ)
    (hV : 0 < (V:ℝ)) (hr : 0 ≤ r) (hd : 0 ≤ d) (policy : ReturnedHistory → Intervention)
    (n : ℕ) (h : ReturnedHistory) (hh : Nonempty (HistoryTrace N V policy h)) :
    ∀ᵐ g ∂fullHistoryKernel (returnedHistoryStep N V r d hV hr hd policy) n h,
      Nonempty (HistoryTrace N V policy g) := by
  induction n generalizing h with
  | zero =>
    change ∀ᵐ g ∂Measure.dirac h,Nonempty (HistoryTrace N V policy g)
    exact (ae_dirac_iff (Set.to_countable _).measurableSet).mpr hh
  | succ n ih =>
    apply Kernel.ae_comp_of_ae_ae (Set.to_countable _).measurableSet
    have hstep : ∀ᵐ g ∂returnedHistoryStep N V r d hV hr hd policy h,
        Nonempty (HistoryTrace N V policy g) := by
      change ∀ᵐ g ∂(literalPulseCycleMeasure (returnedObservation N h).1 V (policy h) r d hV hr hd).map
        (fun X => X::h),Nonempty (HistoryTrace N V policy g)
      apply (ae_map_iff (measurable_of_countable _).aemeasurable (Set.to_countable _).measurableSet).mpr
      filter_upwards [literal_cycle_has_trace (returnedObservation N h).1 V (policy h) r d hV hr hd] with Y hY
      exact ⟨HistoryTrace.cons hh.some Y hY.some⟩
    filter_upwards [hstep] with g hg
    exact ih g hg

def certifiedPhysicalHistory (N : Counts) (V n : ℕ) (policy : ReturnedHistory → Intervention) : Set ReturnedHistory :=
  {h | h ∈ returnedFinal V n ∧ Nonempty (HistoryTrace N V policy h)}

/-- The full source probability certificate also contains physical reaction realizations and their inventory. -/
theorem full_source_inventory_success (N : Counts) (V : ℕ) (r d : ℝ)
    (hV : 0 < (V:ℝ)) (hr : 19 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25)
    (policy : ReturnedHistory → Intervention) (hscale : 200000000000 ≤ V) (hN : Restart V N) (n : ℕ) :
    ENNReal.ofReal (1-(n:ℝ)*oneCycleError V) ≤
      fullHistoryKernel (returnedHistoryStep N V r d hV (by linarith) hd policy) n []
        (certifiedPhysicalHistory N V n policy) := by
  have ht := full_history_has_trace N V r d hV (by linarith) hd policy n [] ⟨HistoryTrace.nil⟩
  have he : certifiedPhysicalHistory N V n policy =ᵐ[
      fullHistoryKernel (returnedHistoryStep N V r d hV (by linarith) hd policy) n []] returnedFinal V n := by
    filter_upwards [ht] with h hh
    change (h ∈ returnedFinal V n ∧ Nonempty (HistoryTrace N V policy h))=(h ∈ returnedFinal V n)
    simp only [hh,and_true]
  rw [measure_congr he]
  exact full_returned_history_success N V r d hV hr hr' hd hd' policy hscale hN n

end
end FiniteCopyReactor
