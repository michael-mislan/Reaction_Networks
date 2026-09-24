import proofs.FiniteReservoir.PhysicalCycleInventory
import proofs.FiniteReservoir.ReturnedTotals

namespace FiniteReservoir
noncomputable section
open Classical FiniteCopyReactor ProductiveRecovery MeasureTheory ProbabilityTheory RandomViability RandomViability.Binding
open scoped ENNReal

inductive HistoryTrace (M : ℕ) (N : CountState M) (V : ℕ) (policy : (ReturnedHistory M) → Intervention) : (ReturnedHistory M) → Type
  | nil : HistoryTrace M N V policy []
  | cons {h : (ReturnedHistory M)} (previous : HistoryTrace M N V policy h) (Y : (JointCounts M))
      (cycle : CycleTrace M (returnedObservation N h).1 V (policy h) Y) : HistoryTrace M N V policy (Y::h)

def HistoryTrace.produced {M N V policy h} : HistoryTrace M N V policy h → ℝ
  | .nil => 0
  | .cons previous _ cycle => previous.produced+cycle.produced

/-- The retained stock and all collected output are funded by initial stock plus actual net synthesis. -/
theorem HistoryTrace.inventory_lower {M N V policy h} (tr : HistoryTrace M N V policy h) :
    templateStock (returnedObservation N h).1.1+returnedTotal h 1 ≤ templateStock N.1+tr.produced := by
  induction tr with
  | nil => simp [returnedObservation,returnedTotal,HistoryTrace.produced]
  | @cons h previous Y cycle ih =>
    have hi := cycle.inventory
    have hc := cycle.collection_le
    have hr := cycle.removed_nonneg
    change templateStock Y.1.1+((Y.2 1:ℝ)+returnedTotal h 1) ≤
      templateStock N.1+(previous.produced+cycle.produced)
    linarith

theorem HistoryTrace.net_lower {M N V policy h} (tr : HistoryTrace M N V policy h) :
    returnedTotal h 1-templateStock N.1 ≤ tr.produced := by
  have hh := tr.inventory_lower
  have hn := templateStock_nonneg (returnedObservation N h).1.1
  linarith

theorem HistoryTrace.certified_net_lower {M N V policy h} (tr : HistoryTrace M N V policy h)
    (n : ℕ) (hN : Restart V N.1) (hh : h ∈ returnedFinal V M n) :
    ((n:ℝ)/56-161/160)*(V:ℝ) ≤ tr.produced := by
  have ht := (returned_joint_totals V M n h hh).1
  have hc := Nat.le_ceil ((V:ℝ)/56)
  have hn : (n:ℝ)*((V:ℝ)/56) ≤ (n:ℝ)*(Nat.ceil ((V:ℝ)/56):ℝ) :=
    mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg n)
  have hi := (templateStock_le_uCount N.1).trans hN.2.1
  have hp := tr.net_lower
  nlinarith

theorem full_history_has_trace (M : ℕ) (N : CountState M) (V : ℕ) (params : Parameters M)
    (hV : 0 < (V:ℝ))  (policy : (ReturnedHistory M) → Intervention)
    (n : ℕ) (h : (ReturnedHistory M)) (hh : Nonempty (HistoryTrace M N V policy h)) :
    ∀ᵐ g ∂fullHistoryKernel (returnedHistoryStep M N V params hV policy) n h,
      Nonempty (HistoryTrace M N V policy g) := by
  induction n generalizing h with
  | zero =>
    change ∀ᵐ g ∂Measure.dirac h,Nonempty (HistoryTrace M N V policy g)
    exact (ae_dirac_iff (Set.to_countable _).measurableSet).mpr hh
  | succ n ih =>
    apply Kernel.ae_comp_of_ae_ae (Set.to_countable _).measurableSet
    have hstep : ∀ᵐ g ∂returnedHistoryStep M N V params hV policy h,
        Nonempty (HistoryTrace M N V policy g) := by
      change ∀ᵐ g ∂(literalPulseCycleMeasure (returnedObservation N h).1.1 V M (policy h) params (returnedObservation N h).1.2 hV).map
        (fun X => X::h),Nonempty (HistoryTrace M N V policy g)
      apply (ae_map_iff (measurable_of_countable _).aemeasurable (Set.to_countable _).measurableSet).mpr
      filter_upwards [literal_cycle_has_trace M (returnedObservation N h).1 V (policy h) params hV] with Y hY
      exact ⟨HistoryTrace.cons hh.some Y hY.some⟩
    filter_upwards [hstep] with g hg
    exact ih g hg

def certifiedPhysicalHistory (M : ℕ) (N : CountState M) (V n : ℕ) (policy : (ReturnedHistory M) → Intervention) : Set (ReturnedHistory M) :=
  {h | h ∈ returnedFinal V M n ∧ Nonempty (HistoryTrace M N V policy h)}

/-- The full source probability certificate also contains physical reaction realizations and their inventory. -/
theorem full_source_inventory_success (M : ℕ) (N : CountState M) (V : ℕ) (params : Parameters M)
    (hV : 0 < (V:ℝ)) 
    (policy : (ReturnedHistory M) → Intervention) (hscale : 200000000000 ≤ V) (hN : Restart V N.1) (n : ℕ) :
    ENNReal.ofReal (1-(n:ℝ)*oneCycleError V) ≤
      fullHistoryKernel (returnedHistoryStep M N V params hV policy) n []
        (certifiedPhysicalHistory M N V n policy) := by
  have ht := full_history_has_trace M N V params hV policy n [] ⟨HistoryTrace.nil⟩
  have he : certifiedPhysicalHistory M N V n policy =ᵐ[
      fullHistoryKernel (returnedHistoryStep M N V params hV policy) n []] returnedFinal V M n := by
    filter_upwards [ht] with h hh
    change (h ∈ returnedFinal V M n ∧ Nonempty (HistoryTrace M N V policy h))=(h ∈ returnedFinal V M n)
    simp only [hh,and_true]
  rw [measure_congr he]
  exact full_returned_history_success M N V params hV policy hscale hN n

end
end FiniteReservoir
