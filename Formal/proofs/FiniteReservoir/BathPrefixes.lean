import proofs.FiniteReservoir.BathMission

namespace FiniteReservoir
noncomputable section
open Classical FiniteCopyReactor RandomViability.Binding

def CycleTrace.visitedBath {M N V p Y} (tr : CycleTrace M N V p Y) : Set (FuelState M) :=
  {b | (∃ k ≤ tr.recovery.length,b=(tr.recovery.state k).1.2) ∨
    (∃ k ≤ tr.collection.length,b=(tr.collection.state k).1.2)}

theorem CycleTrace.prefix_fuel_abs {M N V p Y} (tr : CycleTrace M N V p Y)
    (b : FuelState M) (hb : b ∈ tr.visitedBath) : |(b.val:ℝ)-(N.2.val:ℝ)| ≤ (Y.2 4:ℝ) := by
  have hz : (pulseInitialState N.1 V M p N.2 tr.pulse).2 4=0 := by
    simp [pulseInitialState,integerInitialCounters]
  have hmid := tr.recovery.fuel_abs
  rw [hz] at hmid
  change |(tr.middle.1.2.val:ℝ)-(N.2.val:ℝ)| ≤ (tr.middle.2 4:ℝ)-(0:ℕ) at hmid
  rcases hb with ⟨k,hk,rfl⟩ | ⟨k,hk,rfl⟩
  · have hp := tr.recovery.prefix_fuel_abs k hk
    rw [hz] at hp
    change |((tr.recovery.state k).1.2.val:ℝ)-(N.2.val:ℝ)| ≤ (tr.middle.2 4:ℝ)-(0:ℕ) at hp
    have hm : (tr.middle.2 4:ℝ) ≤ (Y.2 4:ℝ) := by exact_mod_cast tr.collection.counter_gross_mono
    linarith
  · have hp := tr.collection.prefix_fuel_abs k hk
    have ht := abs_sub_le ((tr.collection.state k).1.2.val:ℝ) (tr.middle.1.2.val:ℝ) (N.2.val:ℝ)
    linarith

def HistoryTrace.visitedBath {M N V policy h} : HistoryTrace M N V policy h → Set (FuelState M)
  | .nil => {N.2}
  | .cons previous _ cycle => previous.visitedBath ∪ cycle.visitedBath

theorem HistoryTrace.prefix_fuel_abs {M N V policy h} (tr : HistoryTrace M N V policy h)
    (b : FuelState M) (hb : b ∈ tr.visitedBath) : |(b.val:ℝ)-(N.2.val:ℝ)| ≤ returnedTotal h 4 := by
  induction tr with
  | nil =>
    have he : b=N.2 := hb
    subst b
    simp [returnedTotal]
  | @cons h previous Y cycle ih =>
    change |(b.val:ℝ)-(N.2.val:ℝ)| ≤ (Y.2 4:ℝ)+returnedTotal h 4
    rcases hb with hb | hb
    · have hh := ih hb
      have hn : (0:ℝ) ≤ (Y.2 4:ℝ) := Nat.cast_nonneg _
      linarith
    · have hc := cycle.prefix_fuel_abs b hb
      have hp := previous.fuel_abs
      have ht := abs_sub_le (b.val:ℝ) ((returnedObservation N h).1.2.val:ℝ) (N.2.val:ℝ)
      linarith

theorem bath_waste_difference {M : ℕ} (a b : FuelState M) :
    ((bathOf a).waste:ℝ)-((bathOf b).waste:ℝ) = -((a.val:ℝ)-(b.val:ℝ)) := by
  have ha : a.val ≤ M := Nat.le_of_lt_succ a.isLt
  have hb : b.val ≤ M := Nat.le_of_lt_succ b.isLt
  simp only [bathOf,Nat.cast_sub ha,Nat.cast_sub hb]
  ring

/-- All chemical prefixes, not just final endpoints, obey the same event's gross-service bound. -/
theorem HistoryTrace.successful_prefix_bound {M N V policy h} (tr : HistoryTrace M N V policy h)
    (n : ℕ) (hh : h ∈ returnedFinal V M n) (b : FuelState M) (hb : b ∈ tr.visitedBath) :
    |(b.val:ℝ)-(N.2.val:ℝ)| ≤ (n:ℝ)*(Nat.floor ((V:ℝ)/5):ℝ) ∧
    |((bathOf b).waste:ℝ)-((bathOf N.2).waste:ℝ)| ≤ (n:ℝ)*(Nat.floor ((V:ℝ)/5):ℝ) := by
  have hf := (tr.prefix_fuel_abs b hb).trans (returned_joint_totals V M n h hh).2.2.2.2
  refine ⟨hf,?_⟩
  rw [bath_waste_difference,abs_neg]
  exact hf

end
end FiniteReservoir
