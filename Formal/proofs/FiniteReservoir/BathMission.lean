import proofs.FiniteReservoir.BathInventory
import proofs.FiniteReservoir.Mission
import proofs.FiniteReservoir.FullProduct
import proofs.CommonPhysicalRealization.ActivityCorridor

namespace FiniteReservoir
noncomputable section
open Classical FiniteCopyReactor RandomViability.Binding

theorem CycleTrace.fuel_abs {M N V p Y} (tr : CycleTrace M N V p Y) :
    |(Y.1.2.val:ℝ)-(N.2.val:ℝ)| ≤ (Y.2 4:ℝ) := by
  have h1 := tr.recovery.fuel_abs
  have h2 := tr.collection.fuel_abs
  have hz : (pulseInitialState N.1 V M p N.2 tr.pulse).2 4=0 := by
    simp [pulseInitialState,integerInitialCounters]
  rw [hz] at h1
  have ht := abs_sub_le (Y.1.2.val:ℝ) (tr.middle.1.2.val:ℝ) (N.2.val:ℝ)
  change |(tr.middle.1.2.val:ℝ)-(N.2.val:ℝ)| ≤ (tr.middle.2 4:ℝ)-(0:ℕ) at h1
  linarith

theorem HistoryTrace.fuel_abs {M N V policy h} (tr : HistoryTrace M N V policy h) :
    |((returnedObservation N h).1.2.val:ℝ)-(N.2.val:ℝ)| ≤ returnedTotal h 4 := by
  induction tr with
  | nil => simp [returnedObservation,returnedTotal]
  | @cons h previous Y cycle ih =>
    have hc := cycle.fuel_abs
    have ht := abs_sub_le (Y.1.2.val:ℝ) ((returnedObservation N h).1.2.val:ℝ) (N.2.val:ℝ)
    change |(Y.1.2.val:ℝ)-(N.2.val:ℝ)| ≤ (Y.2 4:ℝ)+returnedTotal h 4
    linarith

/-- Every cycle endpoint uses the same successful-event gross-service allowance. -/
theorem HistoryTrace.successful_bath_bound {M N V policy h} (tr : HistoryTrace M N V policy h)
    (n : ℕ) (hh : h ∈ returnedFinal V M n) :
    |((returnedObservation N h).1.2.val:ℝ)-(N.2.val:ℝ)| ≤ (n:ℝ)*(Nat.floor ((V:ℝ)/5):ℝ) :=
  tr.fuel_abs.trans (returned_joint_totals V M n h hh).2.2.2.2

/-- Conditional lifetime obstruction: a positive net-consumption premise is required. -/
theorem positive_net_service_obstruction (f0 fEnd J jstar V : ℝ) (m : ℕ)
    (hfEnd : 0 ≤ fEnd) (balance : fEnd=f0-J) (service : (m:ℝ)*jstar*V ≤ J) :
    (m:ℝ)*jstar*V ≤ f0 := by linarith

end
end FiniteReservoir
